/* shimtest: the table API over upstream drivers/net/wireguard/peerlookup.c (fetched at the pin). */
#include "peerlookup.c"
#include "shimtest.h"

static struct index_hashtable *itab;
static struct pubkey_hashtable *ptab;
static struct index_hashtable_entry ent[NENT];
static struct wg_peer peers[NPEER];

void t_init(void)
{
	itab = wg_index_hashtable_alloc();
	ptab = wg_pubkey_hashtable_alloc();
	for (int i = 0; i < NENT; i++) {
		INIT_HLIST_NODE(&ent[i].index_hash);
		ent[i].index = 0;
	}
	for (int i = 0; i < NPEER; i++) {
		peers[i].refcount.refcount = 1;
		peers[i].id = i;
		INIT_HLIST_NODE(&peers[i].pubkey_hash);
	}
}
void t_entry(int e, int peer, int type) { ent[e].peer = &peers[peer]; ent[e].type = type; }
void t_peer_key(int p, const u8 key[32]) { memcpy(peers[p].handshake.remote_static, key, 32); }
void t_peer_ref(int p, unsigned r) { peers[p].refcount.refcount = r; }
unsigned t_peer_refs(int p) { return peers[p].refcount.refcount; }
void t_padd(int p) { wg_pubkey_hashtable_add(ptab, &peers[p]); }
int t_plookup(const u8 key[32])
{
	struct wg_peer *p = wg_pubkey_hashtable_lookup(ptab, key);
	return p ? p->id : -1;
}
u32 t_insert(int e) { return wg_index_hashtable_insert(itab, &ent[e]); }
int t_replace(int o, int n) { return wg_index_hashtable_replace(itab, &ent[o], &ent[n]); }
void t_remove(int e) { wg_index_hashtable_remove(itab, &ent[e]); }
int t_lookup(u32 index, int mask, int *peer)
{
	struct wg_peer *p = NULL;
	struct index_hashtable_entry *r = wg_index_hashtable_lookup(itab, mask, index, &p);
	*peer = p ? p->id : -1;
	return r ? (int)(r - ent) : -1;
}
int t_hashed(int e) { return !hlist_unhashed(&ent[e].index_hash); }
u32 t_index(int e) { return ent[e].index; }
int t_entry_peer(int e) { return ent[e].peer ? ent[e].peer->id : -1; }
