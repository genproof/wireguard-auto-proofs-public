// SPDX-License-Identifier: GPL-2.0
// Law `create_any`: wg_noise_handshake_create_initiation and wg_noise_handshake_create_response from ANY prior
// state, including every failure path, against a step-by-step model.
//
// State: a device with ANY static key (usable or not); a peer with ANY public key (degenerate ones included:
// the precomputed static-static DH may be zero) and ANY preshared key or none; ANY mutable handshake state
// (common.h hs_randomize) and ANY other mutable peer state (common.h peer_randomize_rest), any reference count below
// INT_MAX (common.h draw_peer_refs), its
// index entry hashed or not, ANY number of keypairs of the peer (whole objects of ANY content,
// common.h kents_add) in the table, possibly in its slots; ANY ephemeral randomness and
// real-time clock; the output message pre-filled with ANY bytes.
// Claims, for the call and for the model's step at which it stops (identity, ephemeral public key zero, es / ee /
// se DH zero, precomputed ss zero, success):
//  - the return value is true exactly at success;
//  - EVERY byte of the output message is the model's: the fields written before the stop (type, receiver index,
//    ephemeral, encrypted static / timestamp / nothing, sender index at success) and the pre-filled bytes
//    elsewhere (the macs are never written);
//  - EVERY field of the handshake is the model's: chaining key, hash and ephemeral private key as they are at the
//    stop (create_initiation restarts the hash chain from the peer's public key; create_response continues from
//    the current one), state CREATED_INITIATION / CREATED_RESPONSE only at success, everything else unchanged;
//  - create_response does nothing at all unless the state is CONSUMED_INITIATION; create_initiation nothing
//    without an identity;
//  - at success the handshake's entry is (re)inserted with the random index the table drew, unique; the other
//    entries of the table never change (peer, type, index, membership);
//  - (whole-state frame) the rest of the peer (cookie state, keypair slots, last sent handshake, dead
//    flag, ...) and its reference count, and the device (identity, cookie checker, public-key table) never change,
//    and nothing is allocated or freed; no reference count warns.
#include "common.h"

int main(void)
{
	struct wg_device wa;
	struct index_hashtable ita;
	struct pubkey_hashtable pta;
	struct wg_peer p;
	struct m_identity ia;
	struct hs_snap s, x;
	struct m_state st;
	struct kent *kes, *ke;
	struct pr_snap ps;
	struct dev_snap ds;
	struct shim_snap ss;
	unsigned int refs0;
	u8 raw[32], pub[32], psk[32], key[32], dh[32], eph[32], E[32], ts[12], nothing[1];
	size_t n;
	int op, ok, use_psk;
	bool r;

	wg_shim_boottime_ns = draw_boottime();
	wg_noise_init();
	nondet_bytes(raw, 32);
	nondet_bytes(pub, 32);
	nondet_bytes(psk, 32);
	use_psk = nondet_u8() & 1;
	setup_device(&wa, &ita, &pta, raw);
	m_identity_of(&ia, raw);
	setup_peer(&p, &wa, pub, use_psk ? psk : NULL, 1);
	m_precomputed(dh, &ia, pub);
	CHECK(bytes_eq(p.handshake.precomputed_static_static, dh, 32));
	hs_randomize(&p.handshake);
	peer_randomize_rest(&p);
	p.refcount.refcount = draw_peer_refs();
	if (nondet_u8() & 1)
		wg_index_hashtable_insert(&ita, &p.handshake.entry);
	kes = kents_add(&ita, NULL, &p, 1);
	kents_snap(kes);
	pr_take(&ps, &p);
	refs0 = p.refcount.refcount;
	dev_take(&ds, &wa);
	shim_take(&ss);
	hs_take(&s, &p.handshake);
	hs_take(&x, &p.handshake);   // the model's expected handshake, updated step by step
	op = nondet_u8() & 1;
	ok = 0;

	if (op == 0) {
		struct message_handshake_initiation *m = malloc(sizeof(*m));
		u8 before[INIT_LEN], exp[INIT_LEN], img[INIT_LEN];
		if (m != NULL) {
			fill_init(m);
			init_img(before, m);
			bytes_copy(exp, before, INIT_LEN);
			draw_real_clock();
			m_tai64n(ts, wg_shim_real_sec, wg_shim_real_nsec);
			r = wg_noise_handshake_create_initiation(m, &p.handshake);
			if (ia.ok) {
				le32_store(exp, MESSAGE_HANDSHAKE_INITIATION);
				m_start(&st, s.remote_static);
				bytes_copy(x.chaining_key, st.ck, 32);
				bytes_copy(x.hash, st.h, 32);
				bytes_copy(eph, wg_shim_random_log, 32);
				m_clamp(eph);
				bytes_copy(x.ephemeral_private, eph, 32);
				CHECK(!bytes_zero(eph, 32));
				m_dh(E, eph, M_BASEPOINT);
				bytes_copy(exp + 8, E, 32);
				if (!bytes_zero(E, 32)) {
					m_mix_hash(&st, E, 32);
					m_mix_ck(&st, E, 32);
					bytes_copy(x.chaining_key, st.ck, 32);
					bytes_copy(x.hash, st.h, 32);
					if (m_dh(dh, eph, s.remote_static)) {
						m_mix_key(&st, key, dh, 32);
						m_encrypt_and_hash(&st, exp + 40, wa.static_identity.static_public, 32, key);
						bytes_copy(x.chaining_key, st.ck, 32);
						bytes_copy(x.hash, st.h, 32);
						if (!bytes_zero(s.precomputed_static_static, 32)) {
							m_mix_key(&st, key, s.precomputed_static_static, 32);
							m_encrypt_and_hash(&st, exp + 88, ts, 12, key);
							bytes_copy(x.chaining_key, st.ck, 32);
							bytes_copy(x.hash, st.h, 32);
							ok = 1;
							le32_store(exp + 4, wg_shim_random_u32);
							x.state = HANDSHAKE_CREATED_INITIATION;
						}
					}
				}
			}
			init_img(img, m);
			CHECK(r == ok && bytes_eq(img, exp, INIT_LEN));
			free(m);
		}
	} else {
		struct message_handshake_response *m = malloc(sizeof(*m));
		u8 before[RESP_LEN], exp[RESP_LEN], img[RESP_LEN];
		if (m != NULL) {
			fill_resp(m);
			resp_img(before, m);
			bytes_copy(exp, before, RESP_LEN);
			r = wg_noise_handshake_create_response(m, &p.handshake);
			if (s.state == HANDSHAKE_CONSUMED_INITIATION) {
				le32_store(exp, MESSAGE_HANDSHAKE_RESPONSE);
				le32_store(exp + 8, s.remote_index);
				bytes_copy(st.ck, s.chaining_key, 32);
				bytes_copy(st.h, s.hash, 32);
				bytes_copy(eph, wg_shim_random_log, 32);
				m_clamp(eph);
				bytes_copy(x.ephemeral_private, eph, 32);
				m_dh(E, eph, M_BASEPOINT);
				bytes_copy(exp + 12, E, 32);
				if (!bytes_zero(E, 32)) {
					m_mix_hash(&st, E, 32);
					m_mix_ck(&st, E, 32);
					bytes_copy(x.chaining_key, st.ck, 32);
					bytes_copy(x.hash, st.h, 32);
					if (m_dh(dh, eph, s.remote_ephemeral)) {
						m_mix_ck(&st, dh, 32);
						bytes_copy(x.chaining_key, st.ck, 32);
						if (m_dh(dh, eph, s.remote_static)) {
							m_mix_ck(&st, dh, 32);
							m_mix_psk(&st, key, s.preshared_key);
							m_encrypt_and_hash(&st, exp + 44, nothing, 0, key);
							bytes_copy(x.chaining_key, st.ck, 32);
							bytes_copy(x.hash, st.h, 32);
							ok = 1;
							le32_store(exp + 4, wg_shim_random_u32);
							x.state = HANDSHAKE_CREATED_RESPONSE;
						}
					}
				}
			}
			resp_img(img, m);
			CHECK(r == ok && bytes_eq(img, exp, RESP_LEN));
			free(m);
		}
	}

	// the handshake: the model's fields; the entry reinserted at success, else unchanged
	if (ok) {
		CHECK(p.handshake.entry.index == wg_shim_random_u32 && table_has(&ita, &p.handshake.entry) &&
		      table_index_unique(&ita, p.handshake.entry.index));
		x.next = p.handshake.entry.next;
		x.hashed = true;
		x.index = wg_shim_random_u32;
	}
	CHECK(hs_same(&x, &p.handshake));
	n = p.handshake.entry.hashed ? 1 : 0;
	CHECK(kents_same_but_next(kes, &ita));
	for (ke = kes; ke; ke = ke->next) {
		CHECK(ke->kp.entry.hashed);
		n++;
	}
	CHECK(table_len(&ita) == n);
	// nothing else changes
	CHECK(pr_same(&ps, &p) && p.refcount.refcount == refs0 && dev_same(&ds, &wa) && shim_same(&ss));
	kents_free(kes);
	return 0;
}
