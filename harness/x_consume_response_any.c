// SPDX-License-Identifier: GPL-2.0
// Law `consume_response_any`: wg_noise_handshake_consume_response on ANY message and ANY prior state.
//
// State: initiator device A with ANY static private key; ANY number of peers (unique public keys) with ANY public
// and preshared keys, ANY mutable handshake state (common.h hs_randomize), ANY other mutable peer state (common.h
// peer_randomize_rest: dead flag, last sent handshake, cookie state), any reference count below INT_MAX (common.h
// draw_peer_refs); each peer's handshake entry is in A's index table or not (any), and ANY number of keypairs (whole
// objects of ANY content, common.h kents_add) of ANY peers are in the table too, possibly in their peers' slots; one
// peer (B) has a public key whose private key the harness knows; ANY boot clock. Message: ANY 92 bytes (with the
// receiver index drawn, or one of the table's indices), or B's valid response to that peer's CURRENT state (built by
// the model from the peer's hash, chaining key, ephemeral and preshared key, any responder ephemeral), optionally
// with one byte changed.
// Claims (exact agreement with the model, common.h):
//  - the result is the peer the model accepts, or NULL; acceptance exactly when: A has an identity, the table's
//    entry with the receiver index exists and is a handshake entry, its peer's state is CREATED_INITIATION,
//    DH(E_a, E_msg) and DH(S_a, E_msg) are not zero and the empty payload's tag verifies under the key and hash
//    of Noise_IKpsk2 (psk mixed in);
//  - on acceptance, that handshake is exactly: state CONSUMED_RESPONSE, remote ephemeral = the message's, hash and
//    chaining key = the model's, remote index = the message's sender index; everything else of it and ALL the
//    rest of that peer (cookie state, keypair slots, last sent handshake, dead flag, ...), every other peer as a
//    whole, unchanged; the peer holds one more reference;
//  - on rejection NOTHING changes: every peer as a whole (handshake byte for byte, references, cookie state, ...);
//  - in both cases (whole-state frame): the device (identity, cookie checker, public-key table) and the
//    index table (its first entry, every entry's peer, type, index, membership and list link) and every keypair (byte
//    for byte) are unchanged, nothing is allocated or freed, no peer is released and no reference count warns; the
//    message is never modified.
#include "common.h"

int main(void)
{
	struct wg_device wa;
	struct index_hashtable ita;
	struct pubkey_hashtable pta;
	struct m_identity ia, ib;
	u8 raw_a[32], raw_b[32], pub[32], img[RESP_LEN], img_after[RESP_LEN];
	struct hnode *peers = NULL, *nb, *it, *target;
	struct kent *kes;
	struct dev_snap ds;
	struct shim_snap ss;
	struct index_hashtable_entry *head0;
	struct message_handshake_response *msg;
	struct m_state st;
	struct wg_peer *ret;
	struct index_hashtable_entry *e;
	size_t n, i;
	int mode;

	wg_shim_boottime_ns = draw_boottime();
	wg_noise_init();
	nondet_bytes(raw_a, 32);
	nondet_bytes(raw_b, 32);
	setup_device(&wa, &ita, &pta, raw_a);
	m_identity_of(&ia, raw_a);
	m_identity_of(&ib, raw_b);

	nb = hnodes_add(&peers, &wa, ib.pub, 0);
	n = draw_steps();
	for (i = 0; i < n; i++) {
		nondet_bytes(pub, 32);
		hnodes_add(&peers, &wa, pub, 1 + i);
	}
	for (it = peers; it; it = it->next) {
		hs_randomize(&it->p->handshake);
		peer_randomize_rest(it->p);
		if (nondet_u8() % 4 != 0)
			wg_index_hashtable_insert(&ita, &it->p->handshake.entry);
	}
	// keypairs of any peers, possibly in their slots (consume_response reads only their index-table part)
	kes = kents_add(&ita, peers, NULL, 1);

	msg = malloc(sizeof(*msg));
	if (msg != NULL) {
		fill_resp(msg);
		mode = nondet_u8() % 3;
		if (mode == 0 && ita.head != NULL && (nondet_u8() & 1)) {
			// any receiver index of the table
			size_t k = nondet_size();
			for (e = ita.head; e->next != NULL && k > 0; e = e->next)
				k--;
			msg->receiver_index = e->index;
		}
		if (mode != 0 && nb != NULL) {
			// B's response to its peer's current state, as the model builds it
			struct noise_handshake *h = &nb->p->handshake;
			struct m_response mr;
			struct m_state cur;
			u8 eraw[32], ei[32];
			nondet_bytes(eraw, 32);
			bytes_copy(cur.ck, h->chaining_key, 32);
			bytes_copy(cur.h, h->hash, 32);
			m_dh(ei, h->ephemeral_private, M_BASEPOINT);
			if (m_create_response(&mr, &cur, ei, ia.pub, h->preshared_key, eraw)) {
				msg->header.type = MESSAGE_HANDSHAKE_RESPONSE;
				msg->receiver_index = h->entry.index;
				bytes_copy(msg->unencrypted_ephemeral, mr.ephemeral, 32);
				bytes_copy(msg->encrypted_nothing, mr.enc_nothing, 16);
			}
			if (mode == 2) {
				size_t k = nondet_size() % 60;
				u8 d = (u8)(1 + nondet_u8() % 255);
				if (k < 12)
					msg->receiver_index ^= d;
				else if (k < 44)
					msg->unencrypted_ephemeral[k - 12] ^= d;
				else
					msg->encrypted_nothing[k - 44] ^= d;
			}
		}
		resp_img(img, msg);

		wg_shim_boottime_ns = draw_boottime();
		hnodes_snap(peers);
		kents_snap(kes);
		dev_take(&ds, &wa);
		head0 = ita.head;
		shim_take(&ss);
		ret = wg_noise_handshake_consume_response(msg, &wa);

		// the model: the table entry with that index
		target = NULL;
		if (ia.ok) {
			for (e = ita.head; e != NULL && e->index != msg->receiver_index; e = e->next)
				;
			if (e != NULL && e->type == INDEX_HASHTABLE_HANDSHAKE) {
				struct hnode *p = NULL;
				for (it = peers; it; it = it->next)
					if (&it->p->handshake.entry == e)
						p = it;
				if (p != NULL && p->snap.state == HANDSHAKE_CREATED_INITIATION) {
					struct m_state before;
					bytes_copy(before.ck, p->snap.chaining_key, 32);
					bytes_copy(before.h, p->snap.hash, 32);
					if (m_consume_response(&st, &before, p->snap.ephemeral_private, ia.priv, p->snap.preshared_key,
							       msg->unencrypted_ephemeral, msg->encrypted_nothing))
						target = p;
				}
			}
		}

		resp_img(img_after, msg);
		CHECK(bytes_eq(img, img_after, RESP_LEN));
		CHECK(dev_same(&ds, &wa) && ita.head == head0 && kents_same(kes) && shim_same(&ss));
		if (target == NULL) {
			CHECK(ret == NULL && hnodes_same_except(peers, NULL));
		} else {
			struct noise_handshake *h = &target->p->handshake;
			const struct hs_snap *s = &target->snap;
			CHECK(ret == target->p && target->p->refcount.refcount == target->refs + 1);
			wg_peer_put(ret);
			CHECK(hnodes_same_except(peers, target->p));
			CHECK(h->state == HANDSHAKE_CONSUMED_RESPONSE);
			CHECK(bytes_eq(h->remote_ephemeral, msg->unencrypted_ephemeral, 32));
			CHECK(bytes_eq(h->hash, st.h, 32) && bytes_eq(h->chaining_key, st.ck, 32));
			CHECK(h->remote_index == msg->sender_index);
			CHECK(h->entry.peer == s->peer && h->entry.next == s->next && h->entry.hashed == s->hashed &&
			      h->entry.type == s->type && h->entry.index == s->index && h->static_identity == s->static_identity &&
			      bytes_eq(h->ephemeral_private, s->ephemeral_private, 32) &&
			      bytes_eq(h->remote_static, s->remote_static, 32) &&
			      bytes_eq(h->precomputed_static_static, s->precomputed_static_static, 32) &&
			      bytes_eq(h->preshared_key, s->preshared_key, 32) &&
			      bytes_eq(h->latest_timestamp, s->latest_timestamp, 12) &&
			      h->last_initiation_consumption == s->last_initiation_consumption);
			CHECK(target->p->refcount.refcount == target->refs && pr_same(&target->rest, target->p));
		}
		free(msg);
	}
	kents_free(kes);
	hnodes_free(peers);
	return 0;
}
