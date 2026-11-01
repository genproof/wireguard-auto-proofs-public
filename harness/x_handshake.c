// SPDX-License-Identifier: GPL-2.0
// Law `handshake`: a full Noise_IKpsk2 handshake between two devices agrees with the model at every step, and is
// complete.
//
// Setup: devices A and B with ANY static private keys (32 bytes each, as userspace sets them), each with one peer
// for the other configured with the other's public key and ONE preshared key (any 32 bytes, or none); ANY boot
// clock (< 2^62 ns, common.h) and real-time clock, ANY ephemeral randomness (the shim's get_random_bytes).
// Steps: A wg_noise_handshake_create_initiation, A wg_cookie_add_mac_to_packet, B consume_initiation,
// B create_response, B add_mac, A consume_response, A and B wg_noise_handshake_begin_session, then both
// wg_noise_keypairs_clear.
// Claims:
//  - identities, precomputed static-static DH and cookie keys are the model's;
//  - every step's result (bool / returned peer) is the model's (common.h: the WireGuard paper's handshake over the
//    kernel's primitives), and when it succeeds EVERY byte it writes is the model's: all message fields (type,
//    indices, ephemeral, encrypted static, encrypted timestamp = TAI64N of the real clock, encrypted empty payload,
//    mac1 = MAC(HASH("mac1----" || S_pub), message up to mac1), mac2 = 0 without a cookie), the handshake state,
//    hash, chaining key, ephemeral private key (= clamp(random bytes)), remote ephemeral, remote index, latest
//    timestamp, last consumption time; the fields the step must not touch are unchanged (incl. the macs of a
//    message before add_mac, and the message a consume reads);
//  - indices: a new sender index is the random 32-bit value the table drew, hashed exactly once and unique;
//    begin_session moves the handshake's index to the keypair (the handshake entry leaves the table);
//  - the keypairs are the model's: initiator current / responder next, keys = KDF2(C, empty) in the
//    initiator/responder order, remote index, birthdate = now, valid, fresh counters, references, and the peer
//    references taken by the consume functions are balanced;
//  - COMPLETENESS: if the Diffie-Hellman values of the two sides agree pairwise (DH(a, B) = DH(b, A) for the four
//    pairs ee, es, se, ss - a property of X25519, not proved here: this law is relative to the primitives), none
//    of them is zero, both identities are usable, the timestamp is not zero and B's clock is at least 20 ms, then
//    every step succeeds (unless the one allocation fails), both sides end with the same chaining key and hash,
//    and A's sending key is B's receiving key and vice versa;
//  - clear frees both keypairs and empties both index tables; no allocation is left (the harness frees its own).
#include "common.h"

int main(void)
{
	struct wg_device wa, wb;
	struct index_hashtable ita, itb;
	struct pubkey_hashtable pta, ptb;
	struct wg_peer pb, pa;   // pb: A's peer for B, pa: B's peer for A
	struct m_identity ia, ib;
	u8 raw_a[32], raw_b[32], psk[32], ssa[32], ssb[32], tmp[32], ts[12];
	u8 img[INIT_LEN], img_before[INIT_LEN], rimg[RESP_LEN], rimg_before[RESP_LEN];
	struct message_handshake_initiation *m1;
	struct message_handshake_response *m2;
	struct m_initiation mi;
	struct m_consumed_initiation ci;
	struct m_response mr;
	struct m_state st2;
	struct hs_snap snap;
	struct wg_peer *ret;
	struct noise_keypair *ka, *kb;
	int use_psk, ok1, acc1, ok2, acc2, all_ok;
	u64 now_b, now_a, id_a;
	unsigned long allocs0, frees0, fails0;

	wg_shim_boottime_ns = draw_boottime();
	wg_shim_ratelimit_allow = true;
	wg_noise_init();
	nondet_bytes(raw_a, 32);
	nondet_bytes(raw_b, 32);
	use_psk = nondet_u8() & 1;
	if (use_psk)
		nondet_bytes(psk, 32);
	else
		bytes_set(psk, 0, 32);   // no preshared key: the zeroed field (wg_noise_handshake_init with NULL)
	allocs0 = wg_shim_allocs;
	frees0 = wg_shim_frees;
	fails0 = wg_shim_alloc_failures;

	setup_device(&wa, &ita, &pta, raw_a);
	setup_device(&wb, &itb, &ptb, raw_b);
	m_identity_of(&ia, raw_a);
	m_identity_of(&ib, raw_b);
	CHECK(wa.static_identity.has_identity == ia.ok && wb.static_identity.has_identity == ib.ok);
	CHECK(bytes_eq(wa.static_identity.static_private, ia.priv, 32));
	CHECK(bytes_eq(wb.static_identity.static_private, ib.priv, 32));
	m_static_public_field(tmp, &ia, raw_a);
	CHECK(bytes_eq(wa.static_identity.static_public, tmp, 32));
	m_static_public_field(tmp, &ib, raw_b);
	CHECK(bytes_eq(wb.static_identity.static_public, tmp, 32));

	setup_peer(&pb, &wa, ib.pub, use_psk ? psk : NULL, 1);
	setup_peer(&pa, &wb, ia.pub, use_psk ? psk : NULL, 2);
	m_precomputed(ssa, &ia, ib.pub);
	m_precomputed(ssb, &ib, ia.pub);
	CHECK(bytes_eq(pb.handshake.precomputed_static_static, ssa, 32));
	CHECK(bytes_eq(pa.handshake.precomputed_static_static, ssb, 32));
	CHECK(bytes_eq(pb.handshake.preshared_key, psk, 32) && bytes_eq(pa.handshake.preshared_key, psk, 32));
	m_label_key(tmp, M_LABEL_MAC1, ib.pub);
	CHECK(bytes_eq(pb.latest_cookie.message_mac1_key, tmp, 32));
	m_label_key(tmp, M_LABEL_COOKIE, ib.pub);
	CHECK(bytes_eq(pb.latest_cookie.cookie_decryption_key, tmp, 32));
	CHECK(pb.handshake.state == HANDSHAKE_ZEROED && pa.handshake.state == HANDSHAKE_ZEROED);

	m1 = malloc(sizeof(*m1));
	m2 = malloc(sizeof(*m2));
	if (m1 == NULL || m2 == NULL) {
		free(m1);
		free(m2);
		return 0;
	}
	all_ok = ia.ok && ib.ok;

	// ---- A: create_initiation ----
	fill_init(m1);
	init_img(img_before, m1);
	draw_real_clock();
	m_tai64n(ts, wg_shim_real_sec, wg_shim_real_nsec);
	hs_take(&snap, &pb.handshake);
	ok1 = wg_noise_handshake_create_initiation(m1, &pb.handshake);
	if (!ia.ok) {
		// no identity: nothing is written
		CHECK(!ok1 && hs_same(&snap, &pb.handshake));
		init_img(img, m1);
		CHECK(bytes_eq(img, img_before, INIT_LEN));
	}
	if (ia.ok) {
		int mok = m_create_initiation(&mi, wa.static_identity.static_public, ib.pub, ssa, wg_shim_random_log, ts);
		CHECK(ok1 == mok);
		all_ok = all_ok && mok && !bytes_zero(ts, 12);
	}
	if (!ok1) {
		free(m1);
		free(m2);
		return 0;   // the failure paths of create_initiation are claimed in full by law create_any
	}
	init_img(img, m1);
	CHECK(m1->header.type == MESSAGE_HANDSHAKE_INITIATION);
	CHECK(m1->sender_index == wg_shim_random_u32 && m1->sender_index == pb.handshake.entry.index);
	CHECK(table_has(&ita, &pb.handshake.entry) && table_index_unique(&ita, m1->sender_index) && table_len(&ita) == 1);
	CHECK(pb.handshake.entry.type == INDEX_HASHTABLE_HANDSHAKE && pb.handshake.entry.peer == &pb);
	CHECK(bytes_eq(m1->unencrypted_ephemeral, mi.ephemeral, 32));
	CHECK(bytes_eq(m1->encrypted_static, mi.enc_static, 48));
	CHECK(bytes_eq(m1->encrypted_timestamp, mi.enc_timestamp, 28));
	CHECK(bytes_eq(img + 116, img_before + 116, 32));   // the macs are not written by create_initiation
	CHECK(pb.handshake.state == HANDSHAKE_CREATED_INITIATION);
	CHECK(bytes_eq(pb.handshake.hash, mi.st.h, 32) && bytes_eq(pb.handshake.chaining_key, mi.st.ck, 32));
	CHECK(bytes_eq(pb.handshake.ephemeral_private, mi.eph_priv, 32));
	CHECK(bytes_eq(pb.handshake.remote_ephemeral, snap.remote_ephemeral, 32) &&
	      bytes_eq(pb.handshake.latest_timestamp, snap.latest_timestamp, 12) &&
	      pb.handshake.remote_index == snap.remote_index &&
	      pb.handshake.last_initiation_consumption == snap.last_initiation_consumption &&
	      bytes_eq(pb.handshake.remote_static, snap.remote_static, 32) &&
	      bytes_eq(pb.handshake.precomputed_static_static, snap.precomputed_static_static, 32) &&
	      bytes_eq(pb.handshake.preshared_key, snap.preshared_key, 32));

	// ---- A: mac1/mac2 ----
	wg_cookie_add_mac_to_packet(m1, sizeof(*m1), &pb);
	m_label_key(tmp, M_LABEL_MAC1, ib.pub);
	m_mac(img + 116, tmp, 32, img, 116);
	bytes_set(img + 132, 0, 16);   // no cookie: mac2 is zero
	init_img(img_before, m1);
	CHECK(bytes_eq(img, img_before, INIT_LEN));
	CHECK(pb.latest_cookie.have_sent_mac1 && bytes_eq(pb.latest_cookie.last_mac1_sent, img + 116, 16));

	// ---- B: consume_initiation ----
	wg_shim_boottime_ns = draw_boottime();
	now_b = wg_shim_boottime_ns;
	hs_take(&snap, &pa.handshake);
	ret = wg_noise_handshake_consume_initiation(m1, &wb);
	acc1 = ib.ok && m_consume_initiation_1(&ci, &ib, m1->unencrypted_ephemeral, m1->encrypted_static) &&
	       bytes_eq(ci.spub, pa.handshake.remote_static, 32) &&
	       m_consume_initiation_2(&ci, ssb, m1->encrypted_timestamp) &&
	       m_ts_newer(ci.ts, snap.latest_timestamp) && m_not_flood(snap.last_initiation_consumption, now_b);
	all_ok = all_ok && now_b >= 20000000;
	init_img(img_before, m1);
	CHECK(bytes_eq(img, img_before, INIT_LEN));   // the message is not written
	if (!acc1) {
		CHECK(ret == NULL && hs_same(&snap, &pa.handshake) && pa.refcount.refcount == 1);
	} else {
		CHECK(ret == &pa && pa.refcount.refcount == 2);
		wg_peer_put(ret);
		CHECK(pa.handshake.state == HANDSHAKE_CONSUMED_INITIATION);
		CHECK(bytes_eq(pa.handshake.remote_ephemeral, m1->unencrypted_ephemeral, 32));
		CHECK(bytes_eq(pa.handshake.latest_timestamp, ci.ts, 12) && bytes_eq(ci.ts, ts, 12));
		CHECK(bytes_eq(pa.handshake.hash, ci.st.h, 32) && bytes_eq(pa.handshake.chaining_key, ci.st.ck, 32));
		CHECK(pa.handshake.remote_index == m1->sender_index);
		CHECK(pa.handshake.last_initiation_consumption == m_last_consumption(snap.last_initiation_consumption, now_b));
		CHECK(bytes_eq(pa.handshake.ephemeral_private, snap.ephemeral_private, 32) &&
		      pa.handshake.entry.hashed == snap.hashed && pa.handshake.entry.index == snap.index);
	}
	// completeness, first half: the initiation is accepted when the DH values agree and are non-zero
	if (all_ok) {
		int agree;
		u8 d1[32], d2[32];
		agree = m_dh(d1, mi.eph_priv, ib.pub) && m_dh(d2, ib.priv, mi.ephemeral) && bytes_eq(d1, d2, 32);
		agree = agree && !bytes_zero(ssa, 32) && bytes_eq(ssa, ssb, 32);
		all_ok = agree;
		if (all_ok)
			CHECK(acc1);
	}
	if (!acc1) {
		free(m1);
		free(m2);
		return 0;
	}

	// ---- B: create_response ----
	fill_resp(m2);
	resp_img(rimg_before, m2);
	hs_take(&snap, &pa.handshake);
	ok2 = wg_noise_handshake_create_response(m2, &pa.handshake);
	{
		int mok = m_create_response(&mr, &ci.st, m1->unencrypted_ephemeral, pa.handshake.remote_static, psk,
					    wg_shim_random_log);
		CHECK(ok2 == mok);
	}
	if (all_ok) {
		u8 d1[32], d2[32];
		int agree = m_dh(d1, mr.eph_priv, mi.ephemeral) && m_dh(d2, mi.eph_priv, mr.ephemeral) &&
			    bytes_eq(d1, d2, 32) &&
			    m_dh(d1, mr.eph_priv, ia.pub) && m_dh(d2, ia.priv, mr.ephemeral) && bytes_eq(d1, d2, 32);
		all_ok = agree && !bytes_zero(mr.ephemeral, 32);
		if (all_ok)
			CHECK(ok2);
	}
	if (!ok2) {
		free(m1);
		free(m2);
		return 0;   // failure paths: law create_any
	}
	resp_img(rimg, m2);
	CHECK(m2->header.type == MESSAGE_HANDSHAKE_RESPONSE);
	CHECK(m2->receiver_index == m1->sender_index);
	CHECK(m2->sender_index == wg_shim_random_u32 && m2->sender_index == pa.handshake.entry.index);
	CHECK(table_has(&itb, &pa.handshake.entry) && table_index_unique(&itb, m2->sender_index) && table_len(&itb) == 1);
	CHECK(bytes_eq(m2->unencrypted_ephemeral, mr.ephemeral, 32) && bytes_eq(m2->encrypted_nothing, mr.enc_nothing, 16));
	CHECK(bytes_eq(rimg + 60, rimg_before + 60, 32));
	CHECK(pa.handshake.state == HANDSHAKE_CREATED_RESPONSE);
	CHECK(bytes_eq(pa.handshake.hash, mr.st.h, 32) && bytes_eq(pa.handshake.chaining_key, mr.st.ck, 32));
	CHECK(bytes_eq(pa.handshake.ephemeral_private, mr.eph_priv, 32));
	CHECK(bytes_eq(pa.handshake.remote_ephemeral, snap.remote_ephemeral, 32) &&
	      pa.handshake.remote_index == snap.remote_index &&
	      bytes_eq(pa.handshake.latest_timestamp, snap.latest_timestamp, 12) &&
	      pa.handshake.last_initiation_consumption == snap.last_initiation_consumption);

	// ---- B: mac1/mac2 ----
	wg_cookie_add_mac_to_packet(m2, sizeof(*m2), &pa);
	m_label_key(tmp, M_LABEL_MAC1, ia.pub);
	m_mac(rimg + 60, tmp, 32, rimg, 60);
	bytes_set(rimg + 76, 0, 16);
	resp_img(rimg_before, m2);
	CHECK(bytes_eq(rimg, rimg_before, RESP_LEN));

	// ---- A: consume_response ----
	wg_shim_boottime_ns = draw_boottime();
	now_a = wg_shim_boottime_ns;
	hs_take(&snap, &pb.handshake);
	ret = wg_noise_handshake_consume_response(m2, &wa);
	acc2 = ia.ok && m2->receiver_index == pb.handshake.entry.index &&
	       m_consume_response(&st2, &mi.st, mi.eph_priv, ia.priv, psk, m2->unencrypted_ephemeral, m2->encrypted_nothing);
	resp_img(rimg_before, m2);
	CHECK(bytes_eq(rimg, rimg_before, RESP_LEN));
	if (!acc2) {
		CHECK(ret == NULL && hs_same(&snap, &pb.handshake) && pb.refcount.refcount == 1);
	} else {
		CHECK(ret == &pb && pb.refcount.refcount == 2);
		wg_peer_put(ret);
		CHECK(pb.handshake.state == HANDSHAKE_CONSUMED_RESPONSE);
		CHECK(bytes_eq(pb.handshake.remote_ephemeral, m2->unencrypted_ephemeral, 32));
		CHECK(bytes_eq(pb.handshake.hash, st2.h, 32) && bytes_eq(pb.handshake.chaining_key, st2.ck, 32));
		CHECK(pb.handshake.remote_index == m2->sender_index);
		CHECK(bytes_eq(pb.handshake.ephemeral_private, snap.ephemeral_private, 32) &&
		      bytes_eq(pb.handshake.latest_timestamp, snap.latest_timestamp, 12) &&
		      pb.handshake.last_initiation_consumption == snap.last_initiation_consumption &&
		      table_has(&ita, &pb.handshake.entry) && pb.handshake.entry.index == snap.index);
	}
	if (all_ok)
		CHECK(acc2 && bytes_eq(st2.ck, mr.st.ck, 32) && bytes_eq(st2.h, mr.st.h, 32));
	if (!acc2) {
		free(m1);
		free(m2);
		return 0;
	}

	// ---- begin_session on both sides ----
	{
		u8 first[32], second[32];
		bool ra, rb;
		unsigned long f0;
		m_transport(first, second, st2.ck);   // (T_send^i = T_recv^r, T_recv^i = T_send^r)

		hs_take(&snap, &pb.handshake);
		f0 = wg_shim_alloc_failures;
		ra = wg_noise_handshake_begin_session(&pb.handshake, &pb.keypairs);
		if (wg_shim_alloc_failures != f0) {
			CHECK(!ra && hs_same(&snap, &pb.handshake) && pb.keypairs.current_keypair == NULL);
			free(m1);
			free(m2);
			return 0;
		}
		CHECK(ra);
		ka = pb.keypairs.current_keypair;
		CHECK(ka != NULL && pb.keypairs.previous_keypair == NULL && pb.keypairs.next_keypair == NULL);
		CHECK(ka->i_am_the_initiator && ka->remote_index == m2->sender_index);
		CHECK(bytes_eq(ka->sending.key, first, 32) && bytes_eq(ka->receiving.key, second, 32));
		CHECK(ka->sending.is_valid && ka->receiving.is_valid);
		CHECK(ka->sending.birthdate == now_a && ka->receiving.birthdate == now_a);
		CHECK(ka->sending_counter.counter == 0 && ka->receiving_counter.counter == 0);
		CHECK(ka->refcount.refcount == 1 && ka->entry.type == INDEX_HASHTABLE_KEYPAIR && ka->entry.peer == &pb);
		CHECK(ka->entry.index == m1->sender_index && table_has(&ita, &ka->entry) && table_len(&ita) == 1);
		CHECK(!pb.handshake.entry.hashed && hs_zeroed_from(&snap, &pb.handshake));
		id_a = ka->internal_id;

		hs_take(&snap, &pa.handshake);
		f0 = wg_shim_alloc_failures;
		rb = wg_noise_handshake_begin_session(&pa.handshake, &pa.keypairs);
		if (wg_shim_alloc_failures != f0) {
			CHECK(!rb && hs_same(&snap, &pa.handshake) && pa.keypairs.next_keypair == NULL);
			wg_noise_keypairs_clear(&pb.keypairs);
			free(m1);
			free(m2);
			return 0;
		}
		CHECK(rb);
		kb = pa.keypairs.next_keypair;
		CHECK(kb != NULL && pa.keypairs.previous_keypair == NULL && pa.keypairs.current_keypair == NULL);
		CHECK(!kb->i_am_the_initiator && kb->remote_index == m1->sender_index);
		CHECK(bytes_eq(kb->receiving.key, first, 32) && bytes_eq(kb->sending.key, second, 32));
		CHECK(kb->sending.is_valid && kb->receiving.is_valid);
		CHECK(kb->sending.birthdate == now_a && kb->receiving.birthdate == now_a);
		CHECK(kb->refcount.refcount == 1 && kb->entry.type == INDEX_HASHTABLE_KEYPAIR && kb->entry.peer == &pa);
		CHECK(kb->entry.index == m2->sender_index && table_has(&itb, &kb->entry) && table_len(&itb) == 1);
		CHECK(!pa.handshake.entry.hashed && hs_zeroed_from(&snap, &pa.handshake));
		CHECK(kb->internal_id == id_a + 1);
		// completeness: the transport keys cross over
		CHECK(bytes_eq(ka->sending.key, kb->receiving.key, 32) && bytes_eq(ka->receiving.key, kb->sending.key, 32));
	}

	// ---- clear: both keypairs freed, tables empty, nothing leaked ----
	wg_noise_keypairs_clear(&pb.keypairs);
	wg_noise_keypairs_clear(&pa.keypairs);
	CHECK(pb.keypairs.current_keypair == NULL && pa.keypairs.next_keypair == NULL);
	CHECK(ita.head == NULL && itb.head == NULL);
	CHECK(wg_shim_allocs - allocs0 == 2 && wg_shim_frees - frees0 == 2 && wg_shim_alloc_failures == fails0);
	CHECK(pa.refcount.refcount == 1 && pb.refcount.refcount == 1);
	free(m1);
	free(m2);
	return 0;
}
