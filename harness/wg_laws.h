// wg_laws.h: trivial helpers shared by the WireGuard laws (each law includes it once). No models, no algorithms.
#include "quickproof.h"
#include "noise.h"
#include <crypto/blake2s.h>
#include <crypto/chacha.h>
#include <crypto/poly1305.h>
#include <crypto/chacha20poly1305.h>
bool wg_counter_validate(struct noise_replay_counter *counter, u64 nonce);   // receive.c's counter_validate (S19)
#define REJECT_AFTER (U64_MAX - COUNTER_WINDOW_SIZE - 1)   // messages.h: REJECT_AFTER_MESSAGES, 2^64 - 8130
static size_t upto(size_t max) {                      // any value from 0 to max
	size_t value = nondet_size();
	return value < max ? value : max;
}
static u64 any_u64(void) {                            // any 64-bit value
	u64 high = nondet_u32();
	return high << 32 | nondet_u32();
}
static u8 *any_bytes(size_t n) {                      // a new object of n arbitrary bytes (NULL if malloc fails)
	u8 *bytes = malloc(n);
	if (bytes != NULL && n != 0)
		nondet_bytes(bytes, n);
	return bytes;
}
static u8 *copy_of(const u8 *source, size_t n) {      // a new object holding source[0..n-1]
	u8 *copy = malloc(n);
	for (size_t i = 0; copy != NULL && i < n; i++)
		copy[i] = source[i];
	return copy;
}
static int bytes_eq(const u8 *a, const u8 *b, size_t n) {   // a[0..n-1] == b[0..n-1]
	for (size_t i = 0; i < n; i++)
		if (a[i] != b[i])
			return 0;
	return 1;
}
static void new_counter(struct noise_replay_counter *c) {    // a new key's replay counter: zero (keypair_create)
	c->counter = 0;
	for (size_t i = 0; i < COUNTER_BITS_TOTAL / BITS_PER_LONG; i++)
		c->backtrack[i] = 0;
}
