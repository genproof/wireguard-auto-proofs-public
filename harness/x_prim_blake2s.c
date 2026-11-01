// SPDX-License-Identifier: GPL-2.0
// Law `prim_blake2s`: the kernel's BLAKE2s (lib/crypto/blake2s.c, generic compression, include/crypto/blake2s.h)
// is BLAKE2s (RFC 7693, the reference ref_blake2s of common.h).
//
// For ANY output length 1..32, ANY key of 0..32 bytes (0: blake2s_init, else blake2s_init_key; the documented
// ranges), ANY message of any length (exact-size buffer), fed to blake2s_update in ANY split into chunks
// (including empty chunks):
//  - blake2s_final writes exactly the reference digest into an output buffer of exactly outlen bytes;
//  - the context is all zero afterwards (documented: "After finishing, this zeroizes @ctx");
//  - the one-shot inline blake2s(key or NULL, keylen, msg, len, out, outlen) gives the same digest;
//  - the message and the key are not modified.
// Buffer lengths above PTRDIFF_MAX (2^63 - 1) end the run: no real C implementation creates an object larger than
// PTRDIFF_MAX (pointer differences inside it must fit ptrdiff_t; glibc's malloc returns NULL beyond it), but
// CompCert's memory model and VST's malloc_spec' allow objects of up to 2^64 - 1 bytes, which would make the law
// cover buffers that cannot exist (e.g. blake2s_update's DIV_ROUND_UP(inlen, 64) wraps for inlen >= 2^64 - 63).
// This is an assumption about the environment, recorded as DEVIATIONS.md L13; it may later move into the
// framework's malloc specification.
#include "common.h"

int main(void)
{
	struct blake2s_ctx ctx;
	size_t keylen, outlen, n, pos, i;
	u8 key[32], key_copy[32];
	u8 *msg, *copy, *out, *ref, *out2;

	outlen = 1 + nondet_u8() % 32;
	keylen = nondet_u8() % 33;
	nondet_bytes(key, 32);
	bytes_copy(key_copy, key, 32);
	n = draw_size();
	if (n > PTRDIFF_MAX)   /* no C object is larger than PTRDIFF_MAX: see the header comment */
		return 0;
	msg = malloc(n);
	copy = malloc(n);
	out = malloc(outlen);
	ref = malloc(outlen);
	out2 = malloc(outlen);
	if ((msg == NULL || copy == NULL) || out == NULL || ref == NULL || out2 == NULL) {
		free(msg); free(copy); free(out); free(ref); free(out2);
		return 0;
	}
	nondet_bytes(msg, n);
	bytes_copy(copy, msg, n);

	if (keylen > 0)
		blake2s_init_key(&ctx, outlen, key, keylen);
	else
		blake2s_init(&ctx, outlen);
	pos = 0;
	while (pos < n) {
		size_t c = nondet_size();
		if (c > n - pos)
			c = n - pos;
		blake2s_update(&ctx, msg + pos, c);
		pos += c;
	}
	if (nondet_u8() & 1)
		blake2s_update(&ctx, msg, 0);
	blake2s_final(&ctx, out);

	ref_blake2s(ref, outlen, key, keylen, msg, n);
	CHECK(bytes_eq(out, ref, outlen));
	for (i = 0; i < 8; i++)
		CHECK(ctx.h[i] == 0);
	CHECK(ctx.t[0] == 0 && ctx.t[1] == 0 && ctx.f[0] == 0 && ctx.f[1] == 0);
	CHECK(bytes_zero(ctx.buf, 64) && ctx.buflen == 0 && ctx.outlen == 0);

	blake2s(keylen > 0 ? key : NULL, keylen, msg, n, out2, outlen);
	CHECK(bytes_eq(out2, ref, outlen));
	CHECK(bytes_eq(msg, copy, n) && bytes_eq(key, key_copy, 32));

	free(msg); free(copy); free(out); free(ref); free(out2);
	return 0;
}
