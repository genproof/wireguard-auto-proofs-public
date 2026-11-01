/* SPDX-License-Identifier: GPL-2.0 */
/*
 * QUICKPROOF S14/S15 SHIM for drivers/net/wireguard/peerlookup.h: the two lookup tables of a device, as linked lists.
 *
 * Upstream: hash tables (2^13 index buckets, 2^11 siphash-keyed public-key buckets) with RCU.  Here:
 *   - the index table is a singly linked list of entries; wg_index_hashtable_insert/replace/remove/lookup have
 *     upstream's observable behaviour (patch/wg_shim.c): insert first unhashes the entry, then draws random
 *     32-bit indices (get_random_u32) until one is not in use and adds the entry; replace gives the new entry the
 *     old one's index and position and unhashes the old one, or returns false if the old one is not hashed;
 *     lookup finds the entry with that index, returns it only if its type is in the mask, and takes a reference
 *     to its peer;
 *   - the public-key table is a list of peers (peer->pubkey_next); lookup compares handshake.remote_static and
 *     takes a reference to the peer.
 * The table contents are harness-visible (the laws check them).
 */
#ifndef _WG_PEERLOOKUP_H
#define _WG_PEERLOOKUP_H

#include "messages.h"

struct wg_peer;

struct pubkey_hashtable {
	struct wg_peer *head;
};

struct index_hashtable {
	struct index_hashtable_entry *head;
};

enum index_hashtable_type {
	INDEX_HASHTABLE_HANDSHAKE = 1U << 0,
	INDEX_HASHTABLE_KEYPAIR = 1U << 1
};

struct index_hashtable_entry {
	struct wg_peer *peer;
	struct index_hashtable_entry *next;   /* list link (upstream: struct hlist_node index_hash) */
	bool hashed;                          /* in the table (upstream: !hlist_unhashed) */
	enum index_hashtable_type type;
	__le32 index;
};

struct wg_peer *wg_pubkey_hashtable_lookup(struct pubkey_hashtable *table,
					   const u8 pubkey[NOISE_PUBLIC_KEY_LEN]);

__le32 wg_index_hashtable_insert(struct index_hashtable *table,
				 struct index_hashtable_entry *entry);
bool wg_index_hashtable_replace(struct index_hashtable *table,
				struct index_hashtable_entry *old,
				struct index_hashtable_entry *new);
void wg_index_hashtable_remove(struct index_hashtable *table,
			       struct index_hashtable_entry *entry);
struct index_hashtable_entry *
wg_index_hashtable_lookup(struct index_hashtable *table,
			  const enum index_hashtable_type type_mask,
			  const __le32 index, struct wg_peer **peer);

#endif /* _WG_PEERLOOKUP_H */
