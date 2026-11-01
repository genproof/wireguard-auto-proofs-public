// SPDX-License-Identifier: GPL-2.0
// The body of law prim_aead (LEN_LIMIT: the largest message and associated-data length drawn, SIZE_MAX there).
//
// For ANY key, nonce (64-bit, or 24 bytes for XChaCha), associated data and message (exact-size buffers):
//  - chacha20poly1305_encrypt / xchacha20poly1305_encrypt write exactly the RFC 8439 ciphertext || tag of the
//    reference (common.h) into a buffer of exactly len + 16 bytes;
//  - decrypting that output succeeds and gives back the message;
//  - decrypting ANY bytes of any length (random, or the ciphertext with one byte changed) into a buffer of
//    exactly max(len - 16, 0) bytes: succeeds exactly when the reference tag verifies, and then writes the
//    reference plaintext; on failure the output buffer is unchanged;
//  - inputs are not modified.
// Drawn buffer lengths above PTRDIFF_MAX end the run (no C object is that large): see prim_aead.c, DEVIATIONS.md L13.
#include "common.h"

// decryption of ANY bytes: random of any length, or the ciphertext ct (n + 16 bytes) with one byte changed
static void check_decrypt_any(int x, const u8 key[32], u64 nonce, const u8 xnonce[24], const u8 *ad, size_t adlen,
			      const u8 *ct, size_t n)
{
	size_t m, dn, i;
	u8 *c2, *d2, *d2_before, *rd2;
	int ok, rok;

	if (nondet_u8() & 1) {
		m = n + 16;
		c2 = malloc(m);
		if (c2 == NULL)
			return;
		bytes_copy(c2, ct, m);
		i = nondet_size();
		if (i < m)
			c2[i] ^= (u8)(1 + nondet_u8() % 255);
	} else {
		m = draw_size();
		if (m > PTRDIFF_MAX)   /* no C object is larger than PTRDIFF_MAX: see the header comment */
			return;
		if (m > LEN_LIMIT)
			return;
		c2 = malloc(m);
		if (c2 == NULL)
			return;
		nondet_bytes(c2, m);
	}
	dn = m >= 16 ? m - 16 : 0;
	d2 = malloc(dn);
	d2_before = malloc(dn);
	rd2 = malloc(dn);
	if (d2 == NULL || d2_before == NULL || rd2 == NULL) {
		free(c2); free(d2); free(d2_before); free(rd2);
		return;
	}
	nondet_bytes(d2, dn);
	bytes_copy(d2_before, d2, dn);
	ok = x ? xchacha20poly1305_decrypt(d2, c2, m, ad, adlen, xnonce, key)
	       : chacha20poly1305_decrypt(d2, c2, m, ad, adlen, nonce, key);
	rok = x ? ref_xaead_decrypt(rd2, c2, m, ad, adlen, xnonce, key)
		: ref_aead_decrypt(rd2, c2, m, ad, adlen, nonce, key);
	CHECK(ok == rok);
	if (ok)
		CHECK(bytes_eq(d2, rd2, dn));
	else
		CHECK(bytes_eq(d2, d2_before, dn));
	free(c2); free(d2); free(d2_before); free(rd2);
}

int main(void)
{
	u8 key[32], xnonce[24];
	u64 nonce;
	size_t adlen, n;
	u8 *ad, *pt, *ct, *rct, *dec, *ad_copy, *pt_copy;
	int x, ok;

	x = nondet_u8() & 1;
	nondet_bytes(key, 32);
	nondet_bytes(xnonce, 24);
	nonce = draw_u64();
	adlen = draw_size();
	if (adlen > PTRDIFF_MAX)   /* no C object is larger than PTRDIFF_MAX: see the header comment */
		return 0;
	n = draw_size();
	if (n > PTRDIFF_MAX - 16)   /* no C object is larger than PTRDIFF_MAX, and ct/rct are n + 16 bytes */
		return 0;
	if (adlen > LEN_LIMIT || n > LEN_LIMIT || n > SIZE_MAX - 16)
		return 0;
	ad = malloc(adlen);
	ad_copy = malloc(adlen);
	pt = malloc(n);
	pt_copy = malloc(n);
	ct = malloc(n + 16);
	rct = malloc(n + 16);
	dec = malloc(n);
	if ((ad == NULL || ad_copy == NULL) || (pt == NULL || pt_copy == NULL || dec == NULL) ||
	    ct == NULL || rct == NULL) {
		free(ad); free(ad_copy); free(pt); free(pt_copy); free(ct); free(rct); free(dec);
		return 0;
	}
	nondet_bytes(ad, adlen);
	bytes_copy(ad_copy, ad, adlen);
	nondet_bytes(pt, n);
	bytes_copy(pt_copy, pt, n);

	if (x) {
		xchacha20poly1305_encrypt(ct, pt, n, ad, adlen, xnonce, key);
		ref_xaead_encrypt(rct, pt, n, ad, adlen, xnonce, key);
	} else {
		chacha20poly1305_encrypt(ct, pt, n, ad, adlen, nonce, key);
		ref_aead_encrypt(rct, pt, n, ad, adlen, nonce, key);
	}
	CHECK(bytes_eq(ct, rct, n + 16));
	ok = x ? xchacha20poly1305_decrypt(dec, ct, n + 16, ad, adlen, xnonce, key)
	       : chacha20poly1305_decrypt(dec, ct, n + 16, ad, adlen, nonce, key);
	CHECK(ok && bytes_eq(dec, pt, n));

	check_decrypt_any(x, key, nonce, xnonce, ad, adlen, ct, n);
	CHECK(bytes_eq(ad, ad_copy, adlen) && bytes_eq(pt, pt_copy, n));
	free(ad); free(ad_copy); free(pt); free(pt_copy); free(ct); free(rct); free(dec);
	return 0;
}
