/* shimtest only: struct wg_peer for upstream peerlookup.c (the fields it uses) and upstream's
 * wg_peer_get_maybe_zero (peer.c at the pin). */
#ifndef _WG_PEER_H
#define _WG_PEER_H
#include "noise.h"
struct wg_peer {
	struct kref refcount;
	struct noise_handshake handshake;
	struct hlist_node pubkey_hash;
	int id;
};
static inline struct wg_peer *wg_peer_get_maybe_zero(struct wg_peer *peer)
{
	if (!peer || !kref_get_unless_zero(&peer->refcount))
		return NULL;
	return peer;
}
#endif
