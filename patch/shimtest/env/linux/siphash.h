/* shimtest only: siphash chooses a bucket of the public-key table; any function gives the same observable
 * results (a lookup compares the full key within the bucket of that key), so a simple one is used. */
#ifndef SHIMTEST_SIPHASH_H
#define SHIMTEST_SIPHASH_H
#include "quickproof_kernel.h"
typedef struct { u64 key[2]; } siphash_key_t;
static inline u64 siphash(const void *data, size_t len, const siphash_key_t *key)
{
	const u8 *d = data;
	u64 h = key->key[0] ^ 0xcbf29ce484222325ULL;
	for (size_t i = 0; i < len; i++)
		h = (h ^ d[i]) * 0x100000001b3ULL;
	return h;
}
#endif
