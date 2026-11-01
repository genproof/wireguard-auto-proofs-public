// SPDX-License-Identifier: GPL-2.0
// Law `counter`: the data-path replay window counter_validate (drivers/net/wireguard/receive.c, RFC 6479,
// extracted unchanged in patch/counter_validate.c) against a shadow model, over ANY sequence of counters.
//
// A fresh replay counter (zeroed, as kzalloc'd in keypair_create) and a sequence of ANY length of ANY 64-bit
// nonces (the harness also draws them near the highest accepted one and near REJECT_AFTER_MESSAGES).
// Shadow model: the set A of accepted nonces and top = 1 + the largest accepted nonce (0 if none).  With
// W = COUNTER_WINDOW_SIZE = 8192 - 64 = 8128 and R = REJECT_AFTER_MESSAGES = 2^64 - 1 - W - 1 (computed here, not
// taken from messages.h), nonce n is accepted exactly when
//     top < R + 1  and  n < R  and  n + 1 + W >= top  and  n is not in A;
// then n joins A and top becomes max(top, n + 1).
// Claims after every call: the return value is the model's, and counter->counter == top.  (In words: every
// nonce is accepted at most once, nonces below R only, nothing older than the window of W nonces behind the
// highest, and everything else that is new is accepted: the bitmap never forgets a nonce inside the window.)
#include "common.h"

bool wg_counter_validate(struct noise_replay_counter *counter, u64 their_counter);

#define M_W 8128ULL
#define M_R (0xffffffffffffffffULL - M_W - 1)

struct acc {
	u64 n;
	struct acc *next;
};

int main(void)
{
	struct noise_replay_counter c;
	struct acc *set = NULL, *a, **l;
	u64 top = 0, n;
	size_t steps, i;
	int in, ok;
	bool r;

	c.counter = 0;
	for (i = 0; i < COUNTER_BITS_TOTAL / BITS_PER_LONG; i++)
		c.backtrack[i] = 0;
	steps = draw_steps();
	for (i = 0; i < steps; i++) {
		switch (nondet_u8() % 5) {
		case 0: n = top + (u64)(nondet_u32() % 200) - 100; break;           // around the top
		case 1: n = top - (u64)(nondet_u32() % 9000); break;                // inside and just outside the window
		case 4: n = top - M_W - 1 + (u64)(nondet_u32() % 5) - 2; break;     // the window's edge
		case 2: n = M_R + (u64)(nondet_u32() % 8) - 4; break;               // around the limit
		default: n = draw_u64(); break;
		}
		r = wg_counter_validate(&c, n);
		in = 0;
		for (a = set; a; a = a->next)
			if (a->n == n)
				in = 1;
		ok = top < M_R + 1 && n < M_R && n + 1 + M_W >= top && !in;
		CHECK(r == ok);
		if (ok) {
			a = malloc(sizeof(*a));
			if (a == NULL)
				break;
			a->n = n;
			a->next = set;
			set = a;
			if (n + 1 > top)
				top = n + 1;
		}
		CHECK(c.counter == top);
		// forget the nonces the window has left behind (the model accepts none of them again anyway)
		for (l = &set; *l;) {
			if ((*l)->n + 1 + M_W < top) {
				a = *l;
				*l = a->next;
				free(a);
			} else {
				l = &(*l)->next;
			}
		}
	}
	while (set) {
		a = set->next;
		free(set);
		set = a;
	}
	return 0;
}
