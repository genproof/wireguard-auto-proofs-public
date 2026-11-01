// SPDX-License-Identifier: GPL-2.0
// Law `prim_poly1305`: the kernel's Poly1305 (lib/crypto/poly1305.c over poly1305-donna32.c) is Poly1305 (RFC 8439
// 2.5, the TweetNaCl-style reference ref_poly1305 of common.h), through its own streaming API.
//
// For ANY 32-byte key and ANY message of any length (exact-size buffer) fed to poly1305_update in ANY split into
// chunks (empty ones included; each chunk of ANY size_t length, the parameter being a size_t with patch P22 of
// the series; chunks of 2^32 bytes and more run poly1305_update's UINT_MAX loop):
//  - poly1305_final writes exactly the reference tag into a 16-byte buffer;
//  - the context is all zero afterwards (poly1305_final clears it);
//  - the message and key are not modified.
// (The AEAD law only reaches whole 16-byte blocks; this law covers the partial final block.)
// FALSE on unmodified upstream for a chunk of 2^32 - buflen bytes or more with 1..15 bytes buffered (buflen +
// nbytes wrapped) and, with the parameter a size_t, for any chunk of 2^32 bytes or more (upstream's parameter is
// an unsigned int: only length mod 2^32 bytes would be hashed); the code under test carries patch 4/5 of the
// lib/crypto series (P22, DEVIATIONS.md), applied verbatim.
// Buffer lengths above PTRDIFF_MAX (2^63 - 1) end the run: no real C implementation creates an object larger than
// PTRDIFF_MAX (pointer differences inside it must fit ptrdiff_t; glibc's malloc returns NULL beyond it), but
// CompCert's memory model and VST's malloc_spec' allow objects of up to 2^64 - 1 bytes, which would make the law
// cover buffers that cannot exist (e.g. blake2s_update's DIV_ROUND_UP(inlen, 64) wraps for inlen >= 2^64 - 63).
// This is an assumption about the environment, recorded as DEVIATIONS.md L13; it may later move into the
// framework's malloc specification.
#include "common.h"
#include <crypto/poly1305.h>

int main(void)
{
	struct poly1305_desc_ctx d;
	u8 key[32], key0[32];
	u8 *msg, *copy, *tag, ref[16];
	size_t n, pos, i;

	nondet_bytes(key, 32);
	bytes_copy(key0, key, 32);
	n = draw_size();
	if (n > PTRDIFF_MAX)   /* no C object is larger than PTRDIFF_MAX: see the header comment */
		return 0;
	msg = malloc(n);
	copy = malloc(n);
	tag = malloc(16);
	if ((msg == NULL || copy == NULL) || tag == NULL) {
		free(msg); free(copy); free(tag);
		return 0;
	}
	nondet_bytes(msg, n);
	bytes_copy(copy, msg, n);
	poly1305_init(&d, key);
	pos = 0;
	while (pos < n) {
		size_t c = nondet_size();
		if (c > n - pos)
			c = n - pos;
		poly1305_update(&d, msg + pos, c);
		pos += c;
	}
	poly1305_final(&d, tag);
	ref_poly1305(ref, key, msg, n);
	CHECK(bytes_eq(tag, ref, 16));
	CHECK(bytes_zero(d.buf, 16) && d.buflen == 0);
	for (i = 0; i < 4; i++)
		CHECK(d.s[i] == 0);
	for (i = 0; i < 5; i++)
		CHECK(d.state.h.h[i] == 0 && d.state.core_r.key.r[i] == 0);
	for (i = 0; i < 4; i++)
		CHECK(d.state.core_r.precomputed_s.r[i] == 0);
	CHECK(bytes_eq(msg, copy, n) && bytes_eq(key, key0, 32));
	free(msg); free(copy); free(tag);
	return 0;
}
