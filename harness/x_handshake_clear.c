// SPDX-License-Identifier: GPL-2.0
// Law `handshake_clear`: wg_noise_handshake_clear from ANY state destroys exactly the handshake's
// session secrets and its index, and nothing else.
//
// State: a device with ANY static private key; ANY number of peers (unique public keys) with ANY public and
// preshared keys, ANY mutable handshake state (common.h hs_randomize), ANY other mutable peer state (common.h
// peer_randomize_rest), any reference count below INT_MAX (common.h draw_peer_refs); each peer's handshake entry is
// in the device's index table or not (any), and ANY number of keypairs (whole objects of ANY content, common.h
// kents_add) of ANY peers are in the table too, possibly in their peers' slots; the handshake cleared is that of ANY
// peer P (hashed or not, in any state: clearing a cleared handshake is included).
// Claims (the model: handshake_zero of the WireGuard paper's state machine, and the index table's removal):
//  - P's handshake is exactly the zeroed one: state ZEROED, ephemeral private key, remote ephemeral key, hash,
//    chaining key and remote index all zero; its long-term configuration (remote static key, precomputed
//    static-static DH, preshared key, static identity) and its replay state (latest timestamp, last
//    consumption time) unchanged: a cleared handshake still rejects every initiation it rejected before;
//  - P's entry has left the index table (not hashed; its index, type and peer unchanged; its list link NULL if it
//    was hashed, else unchanged): no receiver index leads to P's handshake any more;
//  - the table holds exactly the other entries it held before, each once and unchanged (peer, type, index; every
//    keypair byte for byte);
//  - everything else is unchanged: the rest of P (cookie state, keypair slots, last sent handshake, dead flag,
//    ...) and its reference count, every other peer as a whole (its entry's list link excepted: the entry before
//    P's in the list now skips it), the device (identity, cookie checker, public-key table); nothing is
//    allocated or freed, no peer is released and no reference count warns (common.h shim_same).
#include "common.h"

int main(void)
{
	struct wg_device w;
	struct index_hashtable it;
	struct pubkey_hashtable pt;
	u8 raw[32], pub[32];
	struct hnode *peers = NULL, *nd, *target;
	struct kent *kes;
	struct dev_snap ds;
	struct shim_snap ss;
	struct noise_handshake *h;
	size_t n, i, hashed;

	wg_shim_boottime_ns = draw_boottime();
	nondet_bytes(raw, 32);
	setup_device(&w, &it, &pt, raw);
	n = draw_steps();
	for (i = 0; i < n; i++) {
		nondet_bytes(pub, 32);
		hnodes_add(&peers, &w, pub, i);
	}
	if (peers == NULL)
		return 0;
	for (nd = peers; nd; nd = nd->next) {
		hs_randomize(&nd->p->handshake);
		peer_randomize_rest(nd->p);
		if (nondet_u8() % 4 != 0)
			wg_index_hashtable_insert(&it, &nd->p->handshake.entry);
	}
	kes = kents_add(&it, peers, NULL, 1);
	target = hnodes_pick(peers);

	hnodes_snap(peers);
	kents_snap(kes);
	dev_take(&ds, &w);
	shim_take(&ss);
	h = &target->p->handshake;
	wg_noise_handshake_clear(h);

	// P's handshake: zeroed, unhashed, nothing else of P
	CHECK(hs_zeroed_from(&target->snap, h) && !h->entry.hashed && h->entry.index == target->snap.index);
	if (target->snap.hashed)
		CHECK(h->entry.next == NULL);
	else
		CHECK(h->entry.next == target->snap.next);
	CHECK(target->p->refcount.refcount == target->refs && pr_same(&target->rest, target->p));
	// every other peer as a whole, but its entry's list link; the table: exactly the other hashed entries
	hashed = 0;
	for (nd = peers; nd; nd = nd->next) {
		if (nd == target)
			continue;
		CHECK(hs_same_but_next(&nd->snap, &nd->p->handshake) && nd->p->refcount.refcount == nd->refs &&
		      pr_same(&nd->rest, nd->p));
		if (nd->snap.hashed) {
			CHECK(table_has(&it, &nd->p->handshake.entry));
			hashed++;
		}
	}
	CHECK(kents_same_but_next(kes, &it));
	CHECK(table_len(&it) == hashed + kents_hashed(kes));
	CHECK(dev_same(&ds, &w) && shim_same(&ss));

	kents_free(kes);
	hnodes_free(peers);
	return 0;
}
