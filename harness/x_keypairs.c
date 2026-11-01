// SPDX-License-Identifier: GPL-2.0
// Law `keypairs`: keypair rotation and lifetime against a shadow model, over ANY sequence of operations.
//
// One peer P of a device (any identity), with ANY other mutable state (common.h peer_randomize_rest);
// ANY number of other peers of the device with ANY state (handshake, cookie, ...), their handshake entries in the
// index table or not, and ANY number of keypairs of theirs (whole objects of ANY content, common.h kents_add) in the
// table, possibly in their slots.  A sequence of ANY length of operations, each one of:
//   - wg_noise_handshake_begin_session after setting P's handshake to ANY mutable state (common.h hs_randomize: any
//     of the five states - CREATED_RESPONSE: responder, CONSUMED_RESPONSE: initiator -, any chaining key, remote
//     index, ephemeral keys, hash, latest timestamp, last consumption), its index entry hashed or not, P dead or
//     not; the allocation may fail;
//   - wg_noise_received_with_keypair with ANY live keypair (current, previous, next or one only a reference
//     holder keeps), a keypair of another peer, or NULL: receive.c
//     always passes the keypair it looked up, but the function's behaviour on NULL is defined and claimed too (with
//     no next keypair, NULL is the next keypair and the slots rotate);
//   - wg_noise_expire_current_peer_keypairs;  - wg_noise_keypairs_clear;
//   - wg_noise_keypair_get of NULL or any live keypair (the harness keeps the reference);
//   - wg_noise_keypair_put of ANY kept reference (any keypair the harness holds one of), with unreference_now true
//     or false, or of NULL;
//   - the data path's use of ANY live keypair: its sending counter and its receiving counter set to
//     ANY values (what send.c / receive.c do; out of scope themselves);
// with the boot clock moving forward by any amount.  No bound on the number of operations, of sessions or of
// references (as the kernel does it: the reference count is the kernel's refcount_t, which the
// shim models exactly - quickproof_kref.h, S04 - and the 64-bit keypair counter wraps like the kernel's atomic).
// Shadow model (in this file): the three slots (previous, current, next), every live keypair with its reference
// count, index-table membership and index, keys, validity, birthdate, role, remote index and internal id; the
// rotation rules of the WireGuard paper (initiator: the new keypair becomes current, the old current previous or,
// if a next keypair was waiting, that one previous and the old current is dropped; responder: the new keypair
// waits as next and previous is dropped; confirmation (received_with_keypair of next): next becomes current,
// current previous, previous dropped); "dropped" = unhashed now and one reference less; the reference count as
// include/linux/refcount.h documents refcount_t: +1 per get and -1 per put while it is below INT_MAX = 2^31 - 1,
// a keypair is freed exactly when its last reference goes; a get that finds INT_MAX references SATURATES the
// count (REFCOUNT_SATURATED = 0xc0000000, the kernel's warning "saturated; leaking memory"); a saturated count
// never changes again (every later put is the kernel's warning "underflow; use-after-free" on the saturated
// count, and does nothing else), and a saturated keypair is never freed: it is leaked, as the kernel leaks it.
// Claims after EVERY operation: return values, slot pointers, every live keypair's fields, reference counts
// (exactly the model's, the saturated value included) and table membership (the table holds exactly the hashed
// live keypairs, P's handshake entry if hashed and the other peers' entries, with unique indices), P's handshake
// (zeroed by begin_session and expire, else unchanged), expire invalidates the sending keys of current and next
// and resets last_sent_handshake to now - 6 s; allocations minus frees = live keypairs; the kernel's refcount_t
// warnings are exactly the model's: NEVER an increment from 0 ("addition on 0; use-after-free"), never an
// underflow of a count that is not saturated, never kref_get's overflow or a decrement to 0 without release - the
// only warnings are a get at INT_MAX (saturation) and the puts of an already saturated count.  A saturated keypair
// stays readable and unchanged (the model compares its every field after every operation: it is never freed, so
// never used after free).  At the end, clear and putting every kept reference free every keypair that never
// saturated; the saturated ones (and only they) are leaked.
// Also, after EVERY operation: a new keypair starts with fresh counters (sending counter 0, replay
// window counter 0 with an empty bitmap); no operation ever changes the counters of a live keypair (rotation and
// teardown never reset or rewind a nonce counter); P's handshake is checked after EVERY operation (whole, against
// the model's copy); the rest of P (cookie state, dead flag, last sent handshake but by expire, internal id,
// public-key table link) and its reference count, every other peer as a whole and its keypairs (every byte), and the
// device (identity, cookie checker, public-key table), never change.
#include "common.h"

// the model's reference count: refcount_t as include/linux/refcount.h documents it (written from the documentation,
// not from the shim): INT_MAX is the largest count, REFCOUNT_SATURATED = INT_MIN / 2 the sticky saturated value
#define M_INT_MAX 0x7fffffffu
#define M_SATURATED 0xc0000000u

struct mk {
	struct noise_keypair *kp;
	unsigned int refs;                  // the kernel's count (M_SATURATED once saturated)
	u64 held;                           // references the harness holds
	bool hashed;
	__le32 index;
	u8 send[32];
	u8 recv[32];
	bool send_valid;
	bool recv_valid;
	bool initiator;
	__le32 remote_index;
	u64 birth;
	u64 id;
	s64 scnt;                           // the sending counter
	u64 rcnt;                           // the replay window's counter
	struct mk *next;
};

static struct mk *live;                 // every live keypair of the model
static struct mk *s_prev, *s_cur, *s_next;
static unsigned long m_frees;           // model: frees so far
static unsigned long m_warn[5];         // model: refcount_t warnings, by type (enum refcount_saturation_type)
static unsigned long warn0[5];          // the shim's warning counters at the start
static struct hs_snap hsm;              // model of P's handshake
static struct pr_snap prm;              // model of the rest of P (its keypair slots: s_prev/s_cur/s_next)
static unsigned int prefs;              // P's reference count (constant)
static struct dev_snap dsm;             // the device (constant)
static struct hnode *others;            // the other peers of the device (constant)
static struct kent *kes;                // keypairs of the other peers (constant)

static void mk_unlink(struct mk *k)
{
	struct mk **l;
	for (l = &live; *l; l = &(*l)->next)
		if (*l == k) {
			*l = k->next;
			break;
		}
}

// wg_noise_keypair_get(k) of a live keypair (its count is never 0): one reference more; at INT_MAX, or when
// saturated, the count saturates (warning "saturated; leaking memory")
static void m_get(struct mk *k)
{
	if (k->refs == M_INT_MAX || k->refs == M_SATURATED) {
		k->refs = M_SATURATED;
		m_warn[REFCOUNT_ADD_NOT_ZERO_OVF]++;
	} else {
		k->refs++;
	}
}

// wg_noise_keypair_put(k, unref): unhashed if unref; one reference less, freed at the last one; a saturated count
// stays saturated (warning "underflow; use-after-free" on the saturated count) and the keypair is never freed
static void m_put(struct mk *k, int unref)
{
	if (k == NULL)
		return;
	if (unref)
		k->hashed = false;
	if (k->refs == M_SATURATED) {
		m_warn[REFCOUNT_SUB_UAF]++;
		return;
	}
	k->refs--;
	if (k->refs == 0) {
		mk_unlink(k);
		free(k);
		m_frees++;
	}
}

// the rest of P (pr_snap) but the keypair slots, which check_all compares with the model's slots
static int rest_same(const struct pr_snap *s, const struct wg_peer *p)
{
	return s->device == p->device && s->is_dead == p->is_dead &&
	       s->last_sent_handshake == p->last_sent_handshake.counter && ck_same(&s->cookie, &p->latest_cookie) &&
	       s->internal_id == p->internal_id && s->pubkey_next == p->pubkey_next;
}

// the refcount_t warnings since the start are the model's
static int warn_same(void)
{
	int i;
	for (i = 0; i < 5; i++)
		if (wg_shim_refcount_warn[i] - warn0[i] != m_warn[i])
			return 0;
	return 1;
}

static int check_all(struct wg_peer *p, struct index_hashtable *t, struct wg_device *w)
{
	struct mk *k;
	struct hnode *o;
	size_t hashed = 0;
	if (!hs_same_but_next(&hsm, &p->handshake) || !rest_same(&prm, p) || p->refcount.refcount != prefs ||
	    !dev_same(&dsm, w) || !warn_same())
		return 0;
	if (p->keypairs.previous_keypair != (s_prev ? s_prev->kp : NULL) ||
	    p->keypairs.current_keypair != (s_cur ? s_cur->kp : NULL) ||
	    p->keypairs.next_keypair != (s_next ? s_next->kp : NULL))
		return 0;
	for (k = live; k; k = k->next) {
		struct noise_keypair *kp = k->kp;
		if (kp->refcount.refcount != k->refs || kp->entry.hashed != k->hashed || kp->entry.index != k->index ||
		    kp->entry.type != INDEX_HASHTABLE_KEYPAIR || kp->entry.peer != p ||
		    !bytes_eq(kp->sending.key, k->send, 32) || !bytes_eq(kp->receiving.key, k->recv, 32) ||
		    kp->sending.is_valid != k->send_valid || kp->receiving.is_valid != k->recv_valid ||
		    kp->sending.birthdate != k->birth || kp->receiving.birthdate != k->birth ||
		    kp->i_am_the_initiator != k->initiator || kp->remote_index != k->remote_index || kp->internal_id != k->id ||
		    kp->sending_counter.counter != k->scnt || kp->receiving_counter.counter != k->rcnt)
			return 0;
		if (k->hashed) {
			if (!table_has(t, &kp->entry) || !table_index_unique(t, k->index))
				return 0;
			hashed++;
		}
	}
	if (p->handshake.entry.hashed) {
		if (!table_has(t, &p->handshake.entry) || !table_index_unique(t, p->handshake.entry.index))
			return 0;
		hashed++;
	}
	// the other peers as a whole (but their entries' list links: an entry before them may have left the table),
	// their entries still in the table, and their keypairs (every byte)
	for (o = others; o; o = o->next) {
		if (!hs_same_but_next(&o->snap, &o->p->handshake) || o->p->refcount.refcount != o->refs ||
		    !pr_same(&o->rest, o->p))
			return 0;
		if (o->snap.hashed) {
			if (!table_has(t, &o->p->handshake.entry))
				return 0;
			hashed++;
		}
	}
	if (!kents_same_but_next(kes, t))
		return 0;
	return table_len(t) == hashed + kents_hashed(kes);
}

// any live keypair of the model (NULL if there is none)
static struct mk *pick_live(void)
{
	struct mk *k = live;
	size_t n = nondet_size();
	if (k == NULL)
		return NULL;
	while (n > 0 && k->next != NULL) {
		k = k->next;
		n--;
	}
	return k;
}

// any live keypair of which the harness holds a reference (NULL if there is none)
static struct mk *pick_held(void)
{
	struct mk *k, *r = NULL;
	size_t n = nondet_size();
	for (k = live; k; k = k->next)
		if (k->held > 0) {
			r = k;
			if (n == 0)
				break;
			n--;
		}
	return r;
}

int main(void)
{
	struct wg_device w;
	struct index_hashtable t;
	struct pubkey_hashtable pt;
	struct wg_peer p;
	u8 raw[32], pub[32];
	struct hs_snap snap;
	struct hnode *o;
	struct mk *k, *kn;
	size_t steps, i, n;
	u64 now, next_id = 0;
	int id_known = 0;
	unsigned long allocs0, frees0, nlive;

	live = NULL;
	s_prev = s_cur = s_next = NULL;
	m_frees = 0;
	for (i = 0; i < 5; i++)
		m_warn[i] = 0;
	others = NULL;
	now = draw_boottime();
	wg_shim_boottime_ns = now;
	wg_noise_init();
	nondet_bytes(raw, 32);
	nondet_bytes(pub, 32);
	setup_device(&w, &t, &pt, raw);
	setup_peer(&p, &w, pub, NULL, 1);
	peer_randomize_rest(&p);
	// other peers (public keys unique: not P's either), any state, entries hashed or not; keypair
	// entries of theirs
	n = draw_steps();
	for (i = 0; i < n; i++) {
		u8 opub[32];
		nondet_bytes(opub, 32);
		if (!bytes_eq(opub, pub, 32))
			hnodes_add(&others, &w, opub, 2 + i);
	}
	for (o = others; o; o = o->next) {
		hs_randomize(&o->p->handshake);
		peer_randomize_rest(o->p);
		if (nondet_u8() % 4 != 0)
			wg_index_hashtable_insert(&t, &o->p->handshake.entry);
	}
	kes = kents_add(&t, others, NULL, 1);
	hnodes_snap(others);
	kents_snap(kes);
	hs_take(&hsm, &p.handshake);
	pr_take(&prm, &p);
	prefs = p.refcount.refcount;
	dev_take(&dsm, &w);
	allocs0 = wg_shim_allocs;
	frees0 = wg_shim_frees;
	for (i = 0; i < 5; i++)
		warn0[i] = wg_shim_refcount_warn[i];

	steps = draw_steps();
	for (i = 0; i < steps; i++) {
		int op = nondet_u8() % 8;
		{
			u64 d = draw_u64() >> (nondet_u8() % 64);
			if (d < ((1ULL << 62) - now))
				now += d;
			wg_shim_boottime_ns = now;
		}
		if (op == 0) {
			// begin_session in any state (no bound on their number: the keypair counter wraps, as the kernel's
			// atomic64_t, and so does the model's next_id)
			enum noise_handshake_state st;
			unsigned long a0 = wg_shim_allocs, f0 = wg_shim_alloc_failures, fr0 = wg_shim_frees;
			bool r, dead = (nondet_u8() % 8) == 0;
			k = malloc(sizeof(*k));   // the model's node for a new keypair
			if (k == NULL)
				continue;
			hs_randomize(&p.handshake);   // ANY mutable handshake state
			st = p.handshake.state;
			if (nondet_u8() & 1)
				wg_index_hashtable_insert(&t, &p.handshake.entry);
			p.is_dead = dead;
			prm.is_dead = dead;
			hs_take(&snap, &p.handshake);
			r = wg_noise_handshake_begin_session(&p.handshake, &p.keypairs);
			if (st != HANDSHAKE_CREATED_RESPONSE && st != HANDSHAKE_CONSUMED_RESPONSE) {
				CHECK(!r && hs_same(&snap, &p.handshake) && wg_shim_allocs == a0 && wg_shim_alloc_failures == f0);
				free(k);
			} else if (wg_shim_alloc_failures != f0) {
				CHECK(!r && hs_same(&snap, &p.handshake) && wg_shim_allocs == a0);
				free(k);
			} else {
				struct noise_keypair *kp = NULL;
				u8 first[32], second[32];
				CHECK(wg_shim_allocs == a0 + 1);
				m_transport(first, second, snap.chaining_key);
				// the handshake is zeroed; its entry moves to the keypair (if hashed and P is not dead)
				CHECK(hs_zeroed_from(&snap, &p.handshake));
				if (dead) {
					CHECK(!r && wg_shim_frees == fr0 + 1 && p.handshake.entry.hashed == snap.hashed &&
					      p.handshake.entry.index == snap.index);
					m_frees++;
					if (id_known)
						next_id++;
					free(k);
				} else {
					struct mk *old;
					int initiator = st == HANDSHAKE_CONSUMED_RESPONSE;
					if (initiator)
						kp = p.keypairs.current_keypair;
					else
						kp = p.keypairs.next_keypair;
					CHECK(kp != NULL);
					// fresh counters (keypair_create's kzalloc)
					CHECK(kp->sending_counter.counter == 0 && replay_counter_fresh(&kp->receiving_counter));
					k->scnt = 0;
					k->rcnt = 0;
					k->kp = kp;
					k->refs = 1;
					k->held = 0;
					k->initiator = initiator;
					k->remote_index = snap.remote_index;
					k->birth = now;
					k->send_valid = k->recv_valid = true;
					bytes_copy(k->send, initiator ? first : second, 32);
					bytes_copy(k->recv, initiator ? second : first, 32);
					if (!id_known) {
						next_id = kp->internal_id;
						id_known = 1;
					}
					k->id = next_id;
					next_id++;
					k->next = live;
					live = k;
					// replace: the handshake's index moves to the keypair if the handshake was hashed
					k->hashed = snap.hashed;
					k->index = snap.hashed ? snap.index : 0;
					CHECK(r == snap.hashed && !p.handshake.entry.hashed);
					// add_new_keypair
					if (initiator) {
						if (s_next != NULL) {
							old = s_prev;
							s_prev = s_next;
							s_next = NULL;
							m_put(s_cur, 1);
						} else {
							old = s_prev;
							s_prev = s_cur;
						}
						m_put(old, 1);
						s_cur = k;
					} else {
						old = s_next;
						s_next = k;
						m_put(old, 1);
						old = s_prev;
						s_prev = NULL;
						m_put(old, 1);
					}
				}
			}
			hs_take(&hsm, &p.handshake);   // checked above (hs_same / hs_zeroed_from)
		} else if (op == 1) {
			// received_with_keypair of any live keypair, or of NULL: with no next keypair NULL is
			// "the next keypair" and the slots rotate (current to previous, previous dropped, current NULL)
			struct mk *old;
			bool r;
			if (kes != NULL && nondet_u8() % 8 == 0) {
				// a keypair of ANOTHER peer (never P's next keypair): nothing happens
				struct kent *e = kes;
				size_t m = nondet_size();
				while (m > 0 && e->next != NULL) {
					e = e->next;
					m--;
				}
				r = wg_noise_received_with_keypair(&p.keypairs, &e->kp);
				CHECK(!r);
				CHECK(check_all(&p, &t, &w));
				continue;
			}
			k = (nondet_u8() % 4 == 0) ? NULL : pick_live();
			r = wg_noise_received_with_keypair(&p.keypairs, k != NULL ? k->kp : NULL);
			if (k == s_next) {
				CHECK(r);
				old = s_prev;
				s_prev = s_cur;
				m_put(old, 1);
				s_cur = k;
				s_next = NULL;
			} else {
				CHECK(!r);
			}
		} else if (op == 2) {
			// expire
			hs_take(&snap, &p.handshake);
			wg_noise_expire_current_peer_keypairs(&p);
			CHECK(hs_zeroed_from(&snap, &p.handshake) && !p.handshake.entry.hashed);
			CHECK(p.last_sent_handshake.counter == (s64)(now - (u64)6 * 1000000000));
			hs_take(&hsm, &p.handshake);   // checked above (hs_zeroed_from, unhashed)
			prm.last_sent_handshake = p.last_sent_handshake.counter;
			if (s_next != NULL)
				s_next->send_valid = false;
			if (s_cur != NULL)
				s_cur->send_valid = false;
		} else if (op == 3) {
			// clear: next, previous, current, in that order
			struct mk *old;
			wg_noise_keypairs_clear(&p.keypairs);
			old = s_next;
			s_next = NULL;
			m_put(old, 1);
			old = s_prev;
			s_prev = NULL;
			m_put(old, 1);
			old = s_cur;
			s_cur = NULL;
			m_put(old, 1);
		} else if (op == 7) {
			// the data path uses any live keypair (sends and receives): any counter values
			k = pick_live();
			if (k == NULL)
				continue;
			k->kp->sending_counter.counter = (s64)draw_u64();
			k->kp->receiving_counter.counter = draw_u64();
			k->scnt = k->kp->sending_counter.counter;
			k->rcnt = k->kp->receiving_counter.counter;
		} else if (op == 4 || op == 5) {
			// get a reference to NULL or any live keypair; the harness keeps it.  (No bound;
			// the count saturates at INT_MAX as the kernel's refcount_t does - the model above)
			struct noise_keypair *r;
			k = (nondet_u8() % 4 == 0) ? NULL : pick_live();
			r = wg_noise_keypair_get(k ? k->kp : NULL);
			if (k == NULL) {
				CHECK(r == NULL);
			} else {
				CHECK(r == k->kp);   // also when saturated (refcount_inc_not_zero is then true)
				m_get(k);
				k->held++;
			}
		} else {
			// put any kept reference, or NULL when none is kept: nothing happens
			int unref = nondet_u8() & 1;
			k = pick_held();
			if (k == NULL) {
				wg_noise_keypair_put(NULL, unref);
			} else {
				k->held--;
				wg_noise_keypair_put(k->kp, unref);
				m_put(k, unref);
			}
		}
		CHECK(check_all(&p, &t, &w));
		CHECK(wg_shim_frees - frees0 == m_frees);
	}

	// the end: clear, drop the kept references; every keypair that never saturated is freed, the saturated ones
	// (and only they) are leaked: still live, unchanged, never freed
	wg_noise_keypairs_clear(&p.keypairs);
	{
		struct mk *old;
		old = s_next; s_next = NULL; m_put(old, 1);
		old = s_prev; s_prev = NULL; m_put(old, 1);
		old = s_cur; s_cur = NULL; m_put(old, 1);
	}
	for (k = live; k; k = kn) {
		kn = k->next;   // m_put may free k
		while (k->held > 0) {
			k->held--;
			wg_noise_keypair_put(k->kp, false);
			if (k->refs == 1) {   // the last reference: k is freed
				m_put(k, 0);
				break;
			}
			m_put(k, 0);
		}
	}
	CHECK(check_all(&p, &t, &w));
	nlive = 0;
	for (k = live; k; k = k->next) {
		CHECK(k->refs == M_SATURATED && !k->hashed);
		nlive++;
	}
	CHECK(wg_shim_allocs - allocs0 == wg_shim_frees - frees0 + nlive);
	CHECK(wg_shim_refcount_warn[REFCOUNT_ADD_UAF] == warn0[REFCOUNT_ADD_UAF] &&
	      wg_shim_refcount_warn[REFCOUNT_ADD_OVF] == warn0[REFCOUNT_ADD_OVF] &&
	      wg_shim_refcount_warn[REFCOUNT_DEC_LEAK] == warn0[REFCOUNT_DEC_LEAK]);
	kents_free(kes);
	hnodes_free(others);
	return 0;
}
