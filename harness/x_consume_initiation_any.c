// SPDX-License-Identifier: GPL-2.0
// Law `consume_initiation_any`: wg_noise_handshake_consume_initiation on ANY message and ANY prior state.
//
// State: responder device B with ANY static private key; ANY number of peers (unique public keys: the device's
// invariant) with ANY public keys and preshared keys (or none), ANY mutable handshake state (common.h hs_randomize),
// ANY other mutable peer state (common.h peer_randomize_rest: dead flag, last sent handshake, cookie state) and any
// reference count below INT_MAX (common.h draw_peer_refs); each peer's handshake entry is in B's index table or not
// (any), and ANY number of keypairs (whole objects of ANY content, common.h kents_add) of ANY peers are in the table
// too, possibly in their peers' slots; one peer (A) has a public key whose private key the harness knows; ANY boot
// clock.  Message: ANY 148 bytes (all fields drawn), or A's valid initiation (built by the model, any ephemeral
// randomness, any timestamp), optionally with one byte changed.
// Claims (exact agreement with the model, common.h):
//  - the result is the peer whose handshake the model accepts, or NULL; acceptance exactly when: B has an
//    identity, DH(S_b, E) is not zero, the static decrypts to the public key of some peer P, P's precomputed
//    static-static DH is not zero, the timestamp decrypts, it is greater than P's latest timestamp
//    (lexicographic, TAI64N: an EQUAL timestamp is rejected) and P's last consumption is at least 20 ms before
//    now, exactly as noise.c compares it: rejected iff (s64)(last + 20000000 ns) > (s64)now, so an initiation
//    exactly 20 ms after the last one is ACCEPTED (wireguard-go rejects at exactly 20 ms; whitepaper: no such
//    rule);
//  - on acceptance, P's handshake is exactly: state CONSUMED_INITIATION, remote ephemeral = E, latest timestamp =
//    the decrypted one, hash and chaining key = the model's, remote index = the message's sender index, last
//    consumption = now if later; every other field of P's handshake and ALL the rest of P (cookie state, keypair
//    slots, last sent handshake, dead flag, ...), and every other peer as a whole, unchanged; P holds one more
//    reference (the returned one);
//  - on rejection NOTHING changes: every peer as a whole (handshake byte for byte, reference count, cookie state,
//    keypair slots, ...);
//  - in both cases (whole-state frame): the device (identity, cookie checker, public-key table) and
//    every entry of the index table and every keypair (byte for byte) are unchanged, nothing is allocated or freed
//    and no peer is released (an initiation never creates state by itself), no reference count saturates or warns
//    (common.h shim_same); the message is never modified.
// (The harness draws the boundaries on purpose: the boot clock exactly 20 ms +- 2 ns after A's last consumption,
// and A's latest timestamp equal to the message's or one below / above it.)
#include "common.h"

// t = t + 1 (up) or t - 1, as a 96-bit big-endian number (wrapping)
static void ts_step(u8 t[12], int up)
{
	int i = 11;
	while (i >= 0) {
		u8 old = t[i];
		t[i] = up ? (u8)(old + 1) : (u8)(old - 1);
		if (up ? t[i] != 0 : old != 0)
			break;
		i--;
	}
}

int main(void)
{
	struct wg_device wb;
	struct index_hashtable itb;
	struct pubkey_hashtable ptb;
	struct m_identity ia, ib;
	u8 raw_a[32], raw_b[32], pub[32], ts[12], img[INIT_LEN], img_after[INIT_LEN];
	struct hnode *peers = NULL, *na, *it, *target;
	struct kent *kes;
	struct dev_snap ds;
	struct shim_snap ss;
	struct index_hashtable_entry *head0;
	struct message_handshake_initiation *msg;
	struct m_consumed_initiation ci;
	struct wg_peer *ret;
	size_t n, i;
	u64 now;
	int mode;

	wg_shim_boottime_ns = draw_boottime();
	wg_noise_init();
	nondet_bytes(raw_a, 32);
	nondet_bytes(raw_b, 32);
	setup_device(&wb, &itb, &ptb, raw_b);
	m_identity_of(&ia, raw_a);
	m_identity_of(&ib, raw_b);

	na = hnodes_add(&peers, &wb, ia.pub, 0);
	n = draw_steps();
	for (i = 0; i < n; i++) {
		nondet_bytes(pub, 32);
		hnodes_add(&peers, &wb, pub, 1 + i);
	}
	for (it = peers; it; it = it->next) {
		hs_randomize(&it->p->handshake);
		peer_randomize_rest(it->p);
		if (nondet_u8() % 4 != 0)
			wg_index_hashtable_insert(&itb, &it->p->handshake.entry);
	}
	kes = kents_add(&itb, peers, NULL, 1);

	msg = malloc(sizeof(*msg));
	if (msg == NULL) {
		kents_free(kes);
		hnodes_free(peers);
		return 0;
	}
	fill_init(msg);
	mode = nondet_u8() % 3;
	if (mode != 0 && na != NULL) {
		// A's initiation to B, as the model builds it
		struct m_initiation mi;
		u8 eraw[32], ss[32];
		nondet_bytes(eraw, 32);
		m_precomputed(ss, &ia, ib.pub);
		draw_real_clock();
		m_tai64n(ts, wg_shim_real_sec, wg_shim_real_nsec);
		if (m_create_initiation(&mi, ia.pub, ib.pub, ss, eraw, ts)) {
			msg->header.type = MESSAGE_HANDSHAKE_INITIATION;
			bytes_copy(msg->unencrypted_ephemeral, mi.ephemeral, 32);
			bytes_copy(msg->encrypted_static, mi.enc_static, 48);
			bytes_copy(msg->encrypted_timestamp, mi.enc_timestamp, 28);
		}
		if (mode == 2) {
			size_t k = nondet_size() % 116;
			u8 d = (u8)(1 + nondet_u8() % 255);
			if (k < 8) {
				msg->sender_index ^= d;   // the header and index are not authenticated here
			} else if (k < 40) {
				msg->unencrypted_ephemeral[k - 8] ^= d;
			} else if (k < 88) {
				msg->encrypted_static[k - 40] ^= d;
			} else {
				msg->encrypted_timestamp[k - 88] ^= d;
			}
		}
	}
	if (mode != 0 && na != NULL && nondet_u8() % 4 == 0) {
		// the replay boundary: A's latest timestamp equal to the message's, or the 96-bit value one below / above it
		int d = nondet_u8() % 3;
		bytes_copy(na->p->handshake.latest_timestamp, ts, 12);
		if (d != 0)
			ts_step(na->p->handshake.latest_timestamp, d == 2);
	}
	init_img(img, msg);

	now = draw_boottime();
	if (na != NULL && nondet_u8() % 4 == 0) {
		// the flood limit's boundary: exactly 20 ms (+- 2 ns) after A's last consumption
		u64 edge = na->p->handshake.last_initiation_consumption + 20000000 - 2 + nondet_u8() % 5;
		if (edge < (1ULL << 62))
			now = edge;
	}
	wg_shim_boottime_ns = now;
	hnodes_snap(peers);
	kents_snap(kes);
	dev_take(&ds, &wb);
	head0 = itb.head;
	shim_take(&ss);
	ret = wg_noise_handshake_consume_initiation(msg, &wb);

	// the model
	target = NULL;
	if (ib.ok && m_consume_initiation_1(&ci, &ib, msg->unencrypted_ephemeral, msg->encrypted_static)) {
		struct hnode *p = NULL;
		for (it = peers; it; it = it->next)
			if (p == NULL && bytes_eq(it->p->handshake.remote_static, ci.spub, 32))
				p = it;
		if (p != NULL) {
			u8 ss[32];
			m_precomputed(ss, &ib, p->p->handshake.remote_static);
			if (m_consume_initiation_2(&ci, ss, msg->encrypted_timestamp) &&
			    m_ts_newer(ci.ts, p->snap.latest_timestamp) && m_not_flood(p->snap.last_initiation_consumption, now))
				target = p;
		}
	}

	init_img(img_after, msg);
	CHECK(bytes_eq(img, img_after, INIT_LEN));
	CHECK(dev_same(&ds, &wb) && itb.head == head0 && kents_same(kes) && shim_same(&ss));
	if (target == NULL) {
		CHECK(ret == NULL && hnodes_same_except(peers, NULL));
	} else {
		struct noise_handshake *h = &target->p->handshake;
		const struct hs_snap *s = &target->snap;
		CHECK(ret == target->p && target->p->refcount.refcount == target->refs + 1);
		wg_peer_put(ret);
		CHECK(hnodes_same_except(peers, target->p));
		CHECK(h->state == HANDSHAKE_CONSUMED_INITIATION);
		CHECK(bytes_eq(h->remote_ephemeral, msg->unencrypted_ephemeral, 32));
		CHECK(bytes_eq(h->latest_timestamp, ci.ts, 12));
		CHECK(bytes_eq(h->hash, ci.st.h, 32) && bytes_eq(h->chaining_key, ci.st.ck, 32));
		CHECK(h->remote_index == msg->sender_index);
		CHECK(h->last_initiation_consumption == m_last_consumption(s->last_initiation_consumption, now));
		CHECK(h->entry.peer == s->peer && h->entry.next == s->next && h->entry.hashed == s->hashed &&
		      h->entry.type == s->type && h->entry.index == s->index && h->static_identity == s->static_identity &&
		      bytes_eq(h->ephemeral_private, s->ephemeral_private, 32) &&
		      bytes_eq(h->remote_static, s->remote_static, 32) &&
		      bytes_eq(h->precomputed_static_static, s->precomputed_static_static, 32) &&
		      bytes_eq(h->preshared_key, s->preshared_key, 32));
		CHECK(target->p->refcount.refcount == target->refs && pr_same(&target->rest, target->p));
	}
	free(msg);
	kents_free(kes);
	hnodes_free(peers);
	return 0;
}
