// SPDX-License-Identifier: GPL-2.0
// Shared helpers for the transport data-path laws (transport_order, transport_len,
// transport_keepalive, transport_send_nonce).  They use the project's ONE harness/common.h -- the same reference
// primitives ref_* (ref_aead_decrypt), byte helpers (le32/le64 load/store, bytes_eq), draws (draw_steps,
// draw_size, draw_u64) and kernel crypto declarations as every other law -- and nothing of their own beyond the
// replay-window shadow model below, which is the model of the law `counter` (counter.c) written as functions.
//
// WHAT THESE LAWS MODEL.  The receive data path of drivers/net/wireguard/receive.c is a two-stage pipeline:
//   stage 1  wg_packet_decrypt_worker -> decrypt_packet(): AEAD-verifies the packet with the keypair's
//            receiving key at the nonce in the message_data header; marks the skb CRYPTED or DEAD; the replay
//            counter is NOT touched here;
//   stage 2  wg_packet_rx_poll(): for a CRYPTED skb only, calls counter_validate(&keypair->receiving_counter,
//            nonce); only an accepted (non-replay) packet reaches wg_packet_consume_data_done(), which delivers
//            the plaintext (and treats a zero-length plaintext as a keepalive).
// The stage wiring itself (sk_buff, scatterlist, skb_cow_data, napi_gro_receive, rcu, the per-peer queues) is
// NOT extractable to Clight (DEVIATIONS.md L15).  These laws therefore compose the
// REAL functions the pipeline composes -- the kernel's chacha20poly1305_decrypt (the AEAD decrypt_packet runs) and
// the extracted wg_counter_validate (counter_validate, patch/counter_validate.c, byte for byte) -- in the
// pipeline's order, exactly as replay.c composes the real consume_initiation with its own event loop, and CHECK the
// data-path invariants against a shadow model.  A harness bug or an ordering mistake (validate before auth) is caught by
// construction; what is assumed (not re-proved) is only that receive.c wires these two real functions in this
// order (DEVIATIONS.md L15: the PACKET_STATE_CRYPTED gate of wg_packet_rx_poll).  This is stated with each law.
#ifndef WG_TRANSPORT_H
#define WG_TRANSPORT_H

#include "common.h"

// the extracted replay window (patch/counter_validate.c, counter_validate byte for byte), callable by harnesses
bool wg_counter_validate(struct noise_replay_counter *counter, u64 their_counter);

// RFC 6479 window constants, computed here (as counter.c does), not taken from messages.h.
#define M_W 8128ULL                                  // COUNTER_WINDOW_SIZE = 8192 - 64
#define M_R (0xffffffffffffffffULL - M_W - 1)        // REJECT_AFTER_MESSAGES

// ----- shadow model of the receive replay window (the accepted set + top): counter.c's model, same predicate -----
struct wacc {
	u64 n;
	struct wacc *next;
};

struct wmodel {
	struct wacc *set;
	u64 top;
};

static void wm_init(struct wmodel *m)
{
	m->set = NULL;
	m->top = 0;
}

// the verdict counter_validate must give for nonce n against this model (see counter.c)
static int wm_accepts(const struct wmodel *m, u64 n)
{
	const struct wacc *a;
	for (a = m->set; a; a = a->next)
		if (a->n == n)
			return 0;
	return m->top < M_R + 1 && n < M_R && n + 1 + M_W >= m->top;
}

// record an accepted nonce and advance top; drop nonces the window has left behind (never accepted again)
static int wm_commit(struct wmodel *m, u64 n)
{
	struct wacc *a, **l;
	a = malloc(sizeof(*a));
	if (a == NULL)
		return 0;
	a->n = n;
	a->next = m->set;
	m->set = a;
	if (n + 1 > m->top)
		m->top = n + 1;
	for (l = &m->set; *l;) {
		if ((*l)->n + 1 + M_W < m->top) {
			a = *l;
			*l = a->next;
			free(a);
		} else {
			l = &(*l)->next;
		}
	}
	return 1;
}

static void wm_free(struct wmodel *m)
{
	struct wacc *a;
	while (m->set) {
		a = m->set->next;
		free(m->set);
		m->set = a;
	}
}

// a fresh receiving replay counter (zeroed, as kzalloc'd in keypair_create)
static void rc_init(struct noise_replay_counter *c)
{
	size_t i;
	c->counter = 0;
	for (i = 0; i < COUNTER_BITS_TOTAL / BITS_PER_LONG; i++)
		c->backtrack[i] = 0;
}

// a snapshot of the whole replay counter, to prove "no state change on a bad tag"
struct rc_snap {
	u64 counter;
	unsigned long backtrack[COUNTER_BITS_TOTAL / BITS_PER_LONG];
};

static void rc_take(struct rc_snap *s, const struct noise_replay_counter *c)
{
	size_t i;
	s->counter = c->counter;
	for (i = 0; i < COUNTER_BITS_TOTAL / BITS_PER_LONG; i++)
		s->backtrack[i] = c->backtrack[i];
}

static int rc_same(const struct rc_snap *s, const struct noise_replay_counter *c)
{
	size_t i;
	if (s->counter != c->counter)
		return 0;
	for (i = 0; i < COUNTER_BITS_TOTAL / BITS_PER_LONG; i++)
		if (s->backtrack[i] != c->backtrack[i])
			return 0;
	return 1;
}

#endif /* WG_TRANSPORT_H */
