// hs_unchanged.h: hs_laws.h, and a field-by-field copy and comparison of a peer's state, for the laws that say a
// call changes nothing (hs_reject_*). No models, no algorithms.
#include "hs_laws.h"
static void copy_peer(struct wg_peer *to, const struct wg_peer *from) {   // every handshake field, keypairs, references
	const struct noise_handshake *h = &from->handshake;
	to->handshake.entry.peer = h->entry.peer;
	to->handshake.entry.next = h->entry.next;
	to->handshake.entry.hashed = h->entry.hashed;
	to->handshake.entry.type = h->entry.type;
	to->handshake.entry.index = h->entry.index;
	to->handshake.static_identity = h->static_identity;
	to->handshake.state = h->state;
	to->handshake.last_initiation_consumption = h->last_initiation_consumption;
	to->handshake.remote_index = h->remote_index;
	for (size_t i = 0; i < 32; i++) {
		to->handshake.ephemeral_private[i] = h->ephemeral_private[i];
		to->handshake.remote_static[i] = h->remote_static[i];
		to->handshake.remote_ephemeral[i] = h->remote_ephemeral[i];
		to->handshake.precomputed_static_static[i] = h->precomputed_static_static[i];
		to->handshake.preshared_key[i] = h->preshared_key[i];
		to->handshake.hash[i] = h->hash[i];
		to->handshake.chaining_key[i] = h->chaining_key[i];
		if (i < 12)
			to->handshake.latest_timestamp[i] = h->latest_timestamp[i];
	}
	to->keypairs.current_keypair = from->keypairs.current_keypair;
	to->keypairs.previous_keypair = from->keypairs.previous_keypair;
	to->keypairs.next_keypair = from->keypairs.next_keypair;
	to->refcount.refcount = from->refcount.refcount;
}
static int same_peer(const struct wg_peer *p, const struct wg_peer *q) {  // what copy_peer copies is equal
	const struct noise_handshake *a = &p->handshake, *b = &q->handshake;
	return a->entry.peer == b->entry.peer && a->entry.next == b->entry.next && a->entry.hashed == b->entry.hashed &&
	       a->entry.type == b->entry.type && a->entry.index == b->entry.index &&
	       a->static_identity == b->static_identity && a->state == b->state && a->remote_index == b->remote_index &&
	       a->last_initiation_consumption == b->last_initiation_consumption &&
	       bytes_eq(a->ephemeral_private, b->ephemeral_private, 32) && bytes_eq(a->remote_static, b->remote_static, 32) &&
	       bytes_eq(a->remote_ephemeral, b->remote_ephemeral, 32) && bytes_eq(a->hash, b->hash, 32) &&
	       bytes_eq(a->precomputed_static_static, b->precomputed_static_static, 32) &&
	       bytes_eq(a->preshared_key, b->preshared_key, 32) && bytes_eq(a->chaining_key, b->chaining_key, 32) &&
	       bytes_eq(a->latest_timestamp, b->latest_timestamp, 12) &&
	       p->keypairs.current_keypair == q->keypairs.current_keypair &&
	       p->keypairs.previous_keypair == q->keypairs.previous_keypair &&
	       p->keypairs.next_keypair == q->keypairs.next_keypair && p->refcount.refcount == q->refcount.refcount;
}
