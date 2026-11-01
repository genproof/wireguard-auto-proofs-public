// SPDX-License-Identifier: GPL-2.0
/*
 * wg_shim.c: the kernel environment of the WireGuard handshake in plain C.  QUICKPROOF SHIM (not upstream code);
 * every item is a row of DEVIATIONS.md (ids S04..S18).
 *
 * A library unit like the code under test: it is verified with it, and the laws see its state (clocks,
 * random log, allocation counters, tables).  Everything here is single-threaded.
 */
#include "quickproof_kernel.h"
#include "quickproof_net.h"
#include <crypto/utils.h>
#include "peer.h"
#include "device.h"
#include "timers.h"
#include "ratelimiter.h"
#include "quickproof.h"

/* ---- QUICKPROOF S06 clocks: set by the harness (any value it draws) ---- */
u64 wg_shim_boottime_ns;          /* ktime_get_coarse_boottime_ns() */
s64 wg_shim_real_sec;             /* ktime_get_real_ts64(): tv_sec */
long wg_shim_real_nsec;           /* ktime_get_real_ts64(): tv_nsec, in [0, NSEC_PER_SEC) */

u64 ktime_get_coarse_boottime_ns(void)
{
	return wg_shim_boottime_ns;
}

void ktime_get_real_ts64(struct timespec64 *ts)
{
	ts->tv_sec = wg_shim_real_sec;
	ts->tv_nsec = wg_shim_real_nsec;
}

/* ---- QUICKPROOF S07 randomness: any bytes (nondet_*), the last draw logged for the laws ---- */
u8 wg_shim_random_log[32];        /* the first (at most 32) bytes of the last get_random_bytes* call */
u8 wg_shim_random_log_prev[32];   /* the same for the call before */
u32 wg_shim_random_u32;           /* the last get_random_u32() */

void get_random_bytes(void *buf, size_t len)
{
	u8 *b = (u8 *)buf;
	size_t i;

	nondet_bytes(b, len);
	for (i = 0; i < 32; i++)
		wg_shim_random_log_prev[i] = wg_shim_random_log[i];
	for (i = 0; i < len && i < 32; i++)
		wg_shim_random_log[i] = b[i];
}

void get_random_bytes_wait(void *buf, size_t len)
{
	get_random_bytes(buf, len);
}

u32 get_random_u32(void)
{
	wg_shim_random_u32 = nondet_u32();
	return wg_shim_random_u32;
}

/* ---- QUICKPROOF S05 allocation: calloc/free, counted ---- */
unsigned long wg_shim_allocs;         /* successful kzalloc calls */
unsigned long wg_shim_alloc_failures; /* kzalloc calls that returned NULL */
unsigned long wg_shim_frees;          /* kfree/kfree_sensitive calls with a non-NULL pointer */

bool wg_shim_fail_next_alloc;         /* test knob (patch/diff.c): the next kzalloc returns NULL */

void *kzalloc(size_t size, gfp_t flags)
{
	void *p;

	if (wg_shim_fail_next_alloc) {
		wg_shim_fail_next_alloc = false;
		wg_shim_alloc_failures++;
		return NULL;
	}
	p = calloc(1, size);

	(void)flags;
	if (p)
		wg_shim_allocs++;
	else
		wg_shim_alloc_failures++;
	return p;
}

void kfree(const void *p)
{
	if (p) {
		wg_shim_frees++;
		free((void *)p);
	}
}

void kfree_sensitive(const void *p)
{
	kfree(p);
}

/* ---- QUICKPROOF S08 the zero page ---- */
const u8 quickproof_zero_page[64];

/* ---- QUICKPROOF S09 crypto/utils.h: plain C ---- */
unsigned long __crypto_memneq(const void *a, const void *b, size_t size)
{
	const u8 *x = (const u8 *)a;
	const u8 *y = (const u8 *)b;
	unsigned long neq = 0;
	size_t i;

	for (i = 0; i < size; i++)
		neq |= (unsigned long)(x[i] ^ y[i]);
	return neq;
}

void __crypto_xor(u8 *dst, const u8 *src1, const u8 *src2, unsigned int len)
{
	unsigned int i;

	for (i = 0; i < len; i++)
		dst[i] = src1[i] ^ src2[i];
}

/* ---- QUICKPROOF S04 refcount_t: include/linux/refcount.h (__refcount_add_not_zero, __refcount_add,
 * __refcount_sub_and_test with i = 1) and lib/refcount.c (refcount_warn_saturate) at the pinned commit, one thread.
 * The count is the bits of the kernel's int; `old < 0` is wg_shim_refcount_neg(old).  patch/tests/refcount_check.sh
 * runs these against the kernel's own text on every edge value. ---- */
unsigned long wg_shim_refcount_warn[5];   /* refcount_warn_saturate calls, by enum refcount_saturation_type */

/* refcount_warn_saturate: refcount_set(r, REFCOUNT_SATURATED), then the WARN_ONCE of type t (recorded) */
static void wg_shim_refcount_warn_saturate(unsigned int *r, enum refcount_saturation_type t)
{
	*r = REFCOUNT_SATURATED;
	wg_shim_refcount_warn[t]++;
}

/* the kernel's `v < 0` on an int with these bits */
static bool wg_shim_refcount_neg(unsigned int v)
{
	return v >= 0x80000000u;
}

/* refcount_inc_not_zero: no change at 0 (false); else +1, saturating at INT_MAX + 1 or from a negative count (true) */
bool wg_shim_refcount_inc_not_zero(unsigned int *r)
{
	unsigned int old = *r;

	if (old == 0)
		return false;
	*r = old + 1u;
	if (wg_shim_refcount_neg(old) || wg_shim_refcount_neg(old + 1u))
		wg_shim_refcount_warn_saturate(r, REFCOUNT_ADD_NOT_ZERO_OVF);
	return true;
}

/* refcount_inc: +1; an increment of 0 saturates (use after free), so does one at INT_MAX or of a negative count */
void wg_shim_refcount_inc(unsigned int *r)
{
	unsigned int old = *r;

	*r = old + 1u;
	if (old == 0)
		wg_shim_refcount_warn_saturate(r, REFCOUNT_ADD_UAF);
	else if (wg_shim_refcount_neg(old) || wg_shim_refcount_neg(old + 1u))
		wg_shim_refcount_warn_saturate(r, REFCOUNT_ADD_OVF);
}

/* refcount_dec_and_test: -1; true exactly when the count goes from 1 to 0; a decrement of 0 or of a negative
 * (saturated) count saturates again (underflow) and is false */
bool wg_shim_refcount_dec_and_test(unsigned int *r)
{
	unsigned int old = *r;

	*r = old - 1u;
	if (!wg_shim_refcount_neg(old) && old == 1u)
		return true;
	if (old == 0 || wg_shim_refcount_neg(old))
		wg_shim_refcount_warn_saturate(r, REFCOUNT_SUB_UAF);
	return false;
}

/* ---- QUICKPROOF S12 peers: references counted, never freed (peers belong to the harness) ---- */
unsigned long wg_shim_peer_released;   /* times a peer's reference count reached 0 */

struct wg_peer *wg_peer_get_maybe_zero(struct wg_peer *peer)
{
	if (!peer || !kref_get_unless_zero(&peer->refcount))
		return NULL;
	return peer;
}

static void wg_shim_peer_release(struct kref *refcount)
{
	(void)refcount;
	wg_shim_peer_released++;
}

void wg_peer_put(struct wg_peer *peer)
{
	if (!peer)
		return;
	kref_put(&peer->refcount, wg_shim_peer_release);
}

/* ---- QUICKPROOF S14 the public-key table: a list of peers ---- */
struct wg_peer *wg_pubkey_hashtable_lookup(struct pubkey_hashtable *table,
					   const u8 pubkey[NOISE_PUBLIC_KEY_LEN])
{
	struct wg_peer *iter_peer, *peer = NULL;

	for (iter_peer = table->head; iter_peer; iter_peer = iter_peer->pubkey_next) {
		if (!memcmp(pubkey, iter_peer->handshake.remote_static, NOISE_PUBLIC_KEY_LEN)) {
			peer = iter_peer;
			break;
		}
	}
	return wg_peer_get_maybe_zero(peer);
}

/* ---- QUICKPROOF S15 the index table: a list of entries ---- */
void wg_index_hashtable_remove(struct index_hashtable *table,
			       struct index_hashtable_entry *entry)
{
	struct index_hashtable_entry **link;

	if (!entry->hashed)
		return;
	for (link = &table->head; *link; link = &(*link)->next) {
		if (*link == entry) {
			*link = entry->next;
			break;
		}
	}
	entry->next = NULL;
	entry->hashed = false;
}

static bool wg_shim_index_in_use(struct index_hashtable *table, __le32 index)
{
	struct index_hashtable_entry *e;

	for (e = table->head; e; e = e->next)
		if (e->index == index)
			return true;
	return false;
}

__le32 wg_index_hashtable_insert(struct index_hashtable *table,
				 struct index_hashtable_entry *entry)
{
	wg_index_hashtable_remove(table, entry);
	do {
		entry->index = (__le32)get_random_u32();
	} while (wg_shim_index_in_use(table, entry->index));
	entry->next = table->head;
	entry->hashed = true;
	table->head = entry;
	return entry->index;
}

bool wg_index_hashtable_replace(struct index_hashtable *table,
				struct index_hashtable_entry *old,
				struct index_hashtable_entry *new)
{
	struct index_hashtable_entry **link;

	if (!old->hashed)
		return false;
	new->index = old->index;
	for (link = &table->head; *link; link = &(*link)->next) {
		if (*link == old) {
			*link = new;
			break;
		}
	}
	new->next = old->next;
	new->hashed = true;
	old->next = NULL;
	old->hashed = false;
	return true;
}

struct index_hashtable_entry *
wg_index_hashtable_lookup(struct index_hashtable *table,
			  const enum index_hashtable_type type_mask,
			  const __le32 index, struct wg_peer **peer)
{
	struct index_hashtable_entry *iter_entry, *entry = NULL;

	for (iter_entry = table->head; iter_entry; iter_entry = iter_entry->next) {
		if (iter_entry->index == index) {
			if (iter_entry->type & type_mask)
				entry = iter_entry;
			break;
		}
	}
	if (entry) {
		entry->peer = wg_peer_get_maybe_zero(entry->peer);
		if (entry->peer)
			*peer = entry->peer;
		else
			entry = NULL;
	}
	return entry;
}

/* ---- QUICKPROOF S17 the rate limiter: the harness decides ---- */
bool wg_shim_ratelimit_allow;

bool wg_ratelimiter_allow(struct sk_buff *skb, struct net *net)
{
	(void)skb;
	(void)net;
	return wg_shim_ratelimit_allow;
}

/* ---- QUICKPROOF S18 wg_birthdate_has_expired: upstream's body (drivers/net/wireguard/timers.c) ---- */
bool wg_birthdate_has_expired(u64 birthday_nanoseconds, u64 expiration_seconds)
{
	return (s64)(birthday_nanoseconds + expiration_seconds * NSEC_PER_SEC)
		<= (s64)ktime_get_coarse_boottime_ns();
}
