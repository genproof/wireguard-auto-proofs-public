// SPDX-License-Identifier: GPL-2.0
// Law `config_any`: the configuration functions of noise.c and cookie.c from ANY prior state.
//
// The other laws set devices and peers up from zeroed memory (common.h setup_device, setup_peer); this one calls
// each configuration function on ANY prior contents of what it writes, in the order netlink.c / device.c / peer.c
// call them when a device's private key is changed and a peer is added:
//  1. wg_noise_set_static_identity_private_key(identity, ANY 32 bytes) over ANY prior identity (any public and
//     private key bytes, usable or not): private = clamp(key); public = X25519(key, 9), except that an all-zero
//     key leaves the public key as it was; usable exactly when the key is not all zero and X25519(key, 9) is not
//     zero (common.h m_identity_of);
//  2. wg_noise_precompute_static_static(P) for a peer P with ANY public key and ANY prior precomputed bytes:
//     X25519(private, P's key) if the identity is usable and that is not zero, else all zero;
//  3. wg_cookie_checker_precompute_device_keys over ANY prior keys: HASH("cookie--" || S_pub) and
//     HASH("mac1----" || S_pub) if the identity is usable, else both all zero;
//  4. wg_cookie_checker_precompute_peer_keys(P) over ANY prior keys: HASH("cookie--" || P's key), HASH("mac1----"
//     || P's key);
//  5. a new peer Q: wg_noise_handshake_init over ANY prior handshake contents (every field drawn, pointers
//     included) with ANY public key and ANY preshared key or none: the whole handshake is the initial one (entry of
//     Q, type HANDSHAKE, not hashed, no link, index 0; state ZEROED; no last consumption; the device's identity;
//     the remote static key and preshared key (zero if none) as given; precomputed DH as in 2; everything else
//     zero); then wg_cookie_init over ANY prior cookie state: all zero;
//  6. wg_cookie_checker_init over ANY prior secret, birthdate and device: a fresh random secret (the shim's draw),
//     born now, the device; its keys unchanged.
// After every step: nothing else changes (the device as a whole but the fields the step writes, P as a whole -
// handshake, reference count, cookie state, keypair slots, ... - but those, Q's handshake after it is set up, the
// index table and ANY keypairs of P - whole objects of any content, in the table and possibly in P's slots - byte for
// byte), and nothing is allocated or freed; no reference count warns.
#include "common.h"

int main(void)
{
	struct wg_device w;
	struct index_hashtable it;
	struct pubkey_hashtable pt;
	struct wg_peer p, q;
	struct m_identity id;
	struct hs_snap hs0, hq;
	struct pr_snap ps0;
	struct dev_snap ds;
	struct shim_snap ss;
	struct kent *kes;
	struct index_hashtable_entry *head0;
	unsigned int refs0;
	u8 raw0[32], raw[32], pub[32], qpub[32], psk[32], dh[32];
	int use_psk;
	u64 now;

	now = draw_boottime();
	wg_shim_boottime_ns = now;
	// a device with some key and a peer P of it with ANY public key, then ANY prior contents of what the
	// configuration functions write
	nondet_bytes(raw0, 32);
	setup_device(&w, &it, &pt, raw0);
	nondet_bytes(pub, 32);
	setup_peer(&p, &w, pub, NULL, 1);
	nondet_bytes(w.static_identity.static_public, 32);
	nondet_bytes(w.static_identity.static_private, 32);
	w.static_identity.has_identity = nondet_u8() & 1;
	nondet_bytes(w.cookie_checker.cookie_encryption_key, 32);
	nondet_bytes(w.cookie_checker.message_mac1_key, 32);
	nondet_bytes(p.handshake.precomputed_static_static, 32);
	nondet_bytes(p.latest_cookie.cookie_decryption_key, 32);
	nondet_bytes(p.latest_cookie.message_mac1_key, 32);
	hs_randomize(&p.handshake);
	peer_randomize_rest(&p);
	if (nondet_u8() & 1)
		wg_index_hashtable_insert(&it, &p.handshake.entry);
	kes = kents_add(&it, NULL, &p, 1);   // ANY keypairs of P, in the table, possibly in P's slots
	kents_snap(kes);
	head0 = it.head;
	dev_take(&ds, &w);
	hs_take(&hs0, &p.handshake);
	pr_take(&ps0, &p);
	refs0 = p.refcount.refcount;
	shim_take(&ss);

	// 1. the identity
	nondet_bytes(raw, 32);
	m_identity_of(&id, raw);
	wg_noise_set_static_identity_private_key(&w.static_identity, raw);
	bytes_copy(ds.static_private, id.priv, 32);
	if (!bytes_zero(raw, 32))
		bytes_copy(ds.static_public, id.pub, 32);
	ds.has_identity = id.ok;
	CHECK(dev_same(&ds, &w) && hs_same(&hs0, &p.handshake) && pr_same(&ps0, &p) && p.refcount.refcount == refs0 &&
	      shim_same(&ss) && kents_same(kes) && it.head == head0);

	// 2. P's precomputed static-static DH
	wg_noise_precompute_static_static(&p);
	m_precomputed(dh, &id, pub);
	bytes_copy(hs0.precomputed_static_static, dh, 32);
	CHECK(dev_same(&ds, &w) && hs_same(&hs0, &p.handshake) && pr_same(&ps0, &p) && p.refcount.refcount == refs0 &&
	      shim_same(&ss) && kents_same(kes) && it.head == head0);

	// 3. the device's cookie keys
	wg_cookie_checker_precompute_device_keys(&w.cookie_checker);
	if (id.ok) {
		m_label_key(ds.cookie_encryption_key, M_LABEL_COOKIE, id.pub);
		m_label_key(ds.message_mac1_key, M_LABEL_MAC1, id.pub);
	} else {
		bytes_set(ds.cookie_encryption_key, 0, 32);
		bytes_set(ds.message_mac1_key, 0, 32);
	}
	CHECK(dev_same(&ds, &w) && hs_same(&hs0, &p.handshake) && pr_same(&ps0, &p) && p.refcount.refcount == refs0 &&
	      shim_same(&ss) && kents_same(kes) && it.head == head0);

	// 4. P's cookie keys
	wg_cookie_checker_precompute_peer_keys(&p);
	m_label_key(ps0.cookie.cookie_decryption_key, M_LABEL_COOKIE, pub);
	m_label_key(ps0.cookie.message_mac1_key, M_LABEL_MAC1, pub);
	CHECK(dev_same(&ds, &w) && hs_same(&hs0, &p.handshake) && pr_same(&ps0, &p) && p.refcount.refcount == refs0 &&
	      shim_same(&ss) && kents_same(kes) && it.head == head0);

	// 5. a new peer Q: its handshake and cookie over ANY prior contents
	q.handshake.entry.peer = (nondet_u8() & 1) ? &p : NULL;
	q.handshake.entry.next = (nondet_u8() & 1) ? &p.handshake.entry : NULL;
	q.handshake.entry.hashed = nondet_u8() & 1;
	q.handshake.entry.type = (nondet_u8() & 1) ? INDEX_HASHTABLE_HANDSHAKE : INDEX_HASHTABLE_KEYPAIR;
	q.handshake.entry.index = nondet_u32();
	q.handshake.static_identity = (nondet_u8() & 1) ? &w.static_identity : NULL;
	nondet_bytes(q.handshake.remote_static, 32);
	nondet_bytes(q.handshake.precomputed_static_static, 32);
	nondet_bytes(q.handshake.preshared_key, 32);
	hs_randomize(&q.handshake);
	nondet_bytes(qpub, 32);
	nondet_bytes(psk, 32);
	use_psk = nondet_u8() & 1;
	wg_noise_handshake_init(&q.handshake, &w.static_identity, qpub, use_psk ? psk : NULL, &q);
	hq.peer = &q;
	hq.next = NULL;
	hq.hashed = false;
	hq.type = INDEX_HASHTABLE_HANDSHAKE;
	hq.index = 0;
	hq.state = HANDSHAKE_ZEROED;
	hq.last_initiation_consumption = 0;
	hq.static_identity = &w.static_identity;
	bytes_set(hq.ephemeral_private, 0, 32);
	bytes_copy(hq.remote_static, qpub, 32);
	bytes_set(hq.remote_ephemeral, 0, 32);
	m_precomputed(hq.precomputed_static_static, &id, qpub);
	if (use_psk)
		bytes_copy(hq.preshared_key, psk, 32);
	else
		bytes_set(hq.preshared_key, 0, 32);
	bytes_set(hq.hash, 0, 32);
	bytes_set(hq.chaining_key, 0, 32);
	bytes_set(hq.latest_timestamp, 0, 12);
	hq.remote_index = 0;
	CHECK(hs_same(&hq, &q.handshake));
	q.latest_cookie.birthdate = draw_u64();
	q.latest_cookie.is_valid = nondet_u8() & 1;
	nondet_bytes(q.latest_cookie.cookie, 16);
	q.latest_cookie.have_sent_mac1 = nondet_u8() & 1;
	nondet_bytes(q.latest_cookie.last_mac1_sent, 16);
	nondet_bytes(q.latest_cookie.cookie_decryption_key, 32);
	nondet_bytes(q.latest_cookie.message_mac1_key, 32);
	wg_cookie_init(&q.latest_cookie);
	CHECK(q.latest_cookie.birthdate == 0 && !q.latest_cookie.is_valid && bytes_zero(q.latest_cookie.cookie, 16) &&
	      !q.latest_cookie.have_sent_mac1 && bytes_zero(q.latest_cookie.last_mac1_sent, 16) &&
	      bytes_zero(q.latest_cookie.cookie_decryption_key, 32) && bytes_zero(q.latest_cookie.message_mac1_key, 32));
	CHECK(hs_same(&hq, &q.handshake));
	CHECK(dev_same(&ds, &w) && hs_same(&hs0, &p.handshake) && pr_same(&ps0, &p) && p.refcount.refcount == refs0 &&
	      shim_same(&ss) && kents_same(kes) && it.head == head0);

	// 6. the cookie checker over ANY prior secret, birthdate and device
	nondet_bytes(w.cookie_checker.secret, 32);
	w.cookie_checker.secret_birthdate = draw_u64();
	w.cookie_checker.device = (nondet_u8() & 1) ? &w : NULL;
	wg_cookie_checker_init(&w.cookie_checker, &w);
	bytes_copy(ds.secret, wg_shim_random_log, 32);
	ds.secret_birthdate = now;
	ds.checker_device = &w;
	CHECK(dev_same(&ds, &w) && hs_same(&hs0, &p.handshake) && pr_same(&ps0, &p) && p.refcount.refcount == refs0 &&
	      shim_same(&ss) && kents_same(kes) && it.head == head0);
	kents_free(kes);
	return 0;
}
