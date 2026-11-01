// SPDX-License-Identifier: GPL-2.0
// Shared by the harnesses (the specs).  A harness draws everything from quickproof.h's nondet_* and
// executes undefined behaviour (check_failed) when a property fails.
//
// Two layers of reference code, both part of the claim:
//
// 1. REFERENCE PRIMITIVES (ref_*): BLAKE2s (RFC 7693), ChaCha20 and HChaCha20 (RFC 8439, XChaCha draft),
//    Poly1305 (the TweetNaCl byte-limb algorithm), ChaCha20-Poly1305 and XChaCha20-Poly1305 (RFC 8439
//    construction), X25519 (TweetNaCl's crypto_scalarmult).  Written independently of the kernel code, as
//    plainly as possible; the prim_* laws compare the kernel's primitives with them.  (patch/tests/refkat.c
//    checks them natively against the RFC test vectors.)
//
// 2. THE PROTOCOL MODEL (m_*): Noise_IKpsk2 as WireGuard specifies it (the WireGuard paper, section 5.4, and
//    wireguard.com/protocol), written from the specification, not from noise.c.  It calls the KERNEL'S
//    primitive functions for the cryptography (curve25519_generic, blake2s_init/update/final and the inline
//    blake2s(), chacha20poly1305_encrypt/decrypt, xchacha20poly1305_encrypt/decrypt): the handshake laws claim
//    the protocol logic RELATIVE TO THE PRIMITIVES, and the prim_* laws tie the primitives to the references.
//    Everything else - HMAC, HKDF, the chaining of hashes and keys, TAI64N, the message layout, mac1/mac2, the
//    cookie, the acceptance conditions - is the model's own code.
//
// Sizes: no artificial bound: N_MAX defaults to SIZE_MAX; the small sizes of native test runs come from env.c
// (and from -DN_MAX if a run passes one).  The boot clock is below 2^62 ns (146 years of uptime):
// see draw_boottime.
#ifndef WG_HARNESS_COMMON_H
#define WG_HARNESS_COMMON_H

#include "quickproof.h"
#include "quickproof_kernel.h"
#include "noise.h"
#include "cookie.h"
#include "peer.h"
#include "device.h"
#include "messages.h"
#include <crypto/blake2s.h>
#include <crypto/chacha20poly1305.h>
#include <crypto/curve25519.h>

// N_MAX bounds sizes (bytes), STEPS_MAX bounds counts (operations, peers, table entries).  Both are SIZE_MAX for
// the contracts (clightgen), i.e. no bound.  Under CompCert's interpreter (quickproof/tools/interp.sh defines GP_RUNS
// on the command line) they are small, like those of env.c in native runs: the interpreter keeps every memory block of the run,
// and a long sequence of X25519 calls exhausts memory (72 GB seen).  -DN_MAX / -DSTEPS_MAX override both.
#ifndef N_MAX
#ifdef GP_RUNS
#define N_MAX 70
#else
#define N_MAX SIZE_MAX
#endif
#endif
#ifndef STEPS_MAX
#ifdef GP_RUNS
#define STEPS_MAX 3
#else
#define STEPS_MAX SIZE_MAX
#endif
#endif

// ---------------------------------------------------------------------------------------------------------------
// checks and small helpers
// ---------------------------------------------------------------------------------------------------------------

static void check_failed(void)
{
	int *p = NULL;
	*p = 0;
}

#define CHECK(c) do { if (!(c)) check_failed(); } while (0)

static int bytes_eq(const u8 *a, const u8 *b, size_t n)
{
	size_t i;
	for (i = 0; i < n; i++)
		if (a[i] != b[i])
			return 0;
	return 1;
}

static int bytes_zero(const u8 *a, size_t n)
{
	size_t i;
	for (i = 0; i < n; i++)
		if (a[i] != 0)
			return 0;
	return 1;
}

static void bytes_copy(u8 *d, const u8 *s, size_t n)
{
	size_t i;
	for (i = 0; i < n; i++)
		d[i] = s[i];
}

static void bytes_set(u8 *d, u8 v, size_t n)
{
	size_t i;
	for (i = 0; i < n; i++)
		d[i] = v;
}

// a size with no bound but N_MAX (SIZE_MAX by default)
static size_t draw_size(void)
{
	size_t n = nondet_size();
	return n <= N_MAX ? n : n % N_MAX;
}

// a count (of operations, peers, entries) with no bound but STEPS_MAX (SIZE_MAX by default)
static size_t draw_steps(void)
{
	size_t n = nondet_size();
	return n <= STEPS_MAX ? n : n % STEPS_MAX;
}

static u64 draw_u64(void)
{
	u64 hi = nondet_u32();
	return (hi << 32) | nondet_u32();
}

// The boot clock (ktime_get_coarse_boottime_ns): any value below 2^62 ns.  ASSUMPTION of the laws: the kernel
// compares clock values as s64 sums (last + 20 ms, birthdate + 120 s); with the kernel's -fno-strict-overflow
// these wrap, and CompCert wraps too, but a boot clock near 2^63 ns (292 years) never occurs, and native UBSan
// runs would flag the wrap.
static u64 draw_boottime(void)
{
	return draw_u64() & ((1ULL << 62) - 1);
}

extern u64 wg_shim_boottime_ns;
extern s64 wg_shim_real_sec;
extern long wg_shim_real_nsec;
extern u8 wg_shim_random_log[32];
extern u8 wg_shim_random_log_prev[32];
extern u32 wg_shim_random_u32;
extern unsigned long wg_shim_allocs;
extern unsigned long wg_shim_alloc_failures;
extern unsigned long wg_shim_frees;
extern unsigned long wg_shim_peer_released;
extern bool wg_shim_ratelimit_allow;

static void le32_store(u8 *p, u32 v)
{
	p[0] = (u8)v;
	p[1] = (u8)(v >> 8);
	p[2] = (u8)(v >> 16);
	p[3] = (u8)(v >> 24);
}

static u32 le32_load(const u8 *p)
{
	return (u32)p[0] | ((u32)p[1] << 8) | ((u32)p[2] << 16) | ((u32)p[3] << 24);
}

static void le64_store(u8 *p, u64 v)
{
	le32_store(p, (u32)v);
	le32_store(p + 4, (u32)(v >> 32));
}

// ---------------------------------------------------------------------------------------------------------------
// 1. reference primitives
// ---------------------------------------------------------------------------------------------------------------

// BLAKE2s (RFC 7693): h = IV with the parameter block; the key (if any) padded to one block, then the message;
// every block but the last compressed with the byte count so far, the last one (zero padded) with the total and
// the final flag.  An empty unkeyed message is one zero block.
static const u32 RB2S_IV[8] = { 0x6A09E667u, 0xBB67AE85u, 0x3C6EF372u, 0xA54FF53Au,
				0x510E527Fu, 0x9B05688Cu, 0x1F83D9ABu, 0x5BE0CD19u };
static const u8 RB2S_SIGMA[10][16] = {
	{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 },
	{ 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 },
	{ 11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4 },
	{ 7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8 },
	{ 9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13 },
	{ 2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9 },
	{ 12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11 },
	{ 13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10 },
	{ 6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5 },
	{ 10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0 },
};

static u32 rb2s_rotr(u32 x, unsigned int n)
{
	return (x >> n) | (x << (32 - n));
}

static void rb2s_g(u32 v[16], int a, int b, int c, int d, u32 x, u32 y)
{
	v[a] = v[a] + v[b] + x;
	v[d] = rb2s_rotr(v[d] ^ v[a], 16);
	v[c] = v[c] + v[d];
	v[b] = rb2s_rotr(v[b] ^ v[c], 12);
	v[a] = v[a] + v[b] + y;
	v[d] = rb2s_rotr(v[d] ^ v[a], 8);
	v[c] = v[c] + v[d];
	v[b] = rb2s_rotr(v[b] ^ v[c], 7);
}

static void rb2s_compress(u32 h[8], const u8 block[64], u64 t, int last)
{
	u32 m[16], v[16];
	int i, r;

	for (i = 0; i < 16; i++)
		m[i] = le32_load(block + 4 * i);
	for (i = 0; i < 8; i++) {
		v[i] = h[i];
		v[i + 8] = RB2S_IV[i];
	}
	v[12] ^= (u32)t;
	v[13] ^= (u32)(t >> 32);
	if (last)
		v[14] = ~v[14];
	for (r = 0; r < 10; r++) {
		const u8 *s = RB2S_SIGMA[r];
		rb2s_g(v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
		rb2s_g(v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
		rb2s_g(v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
		rb2s_g(v, 3, 7, 11, 15, m[s[6]], m[s[7]]);
		rb2s_g(v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
		rb2s_g(v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
		rb2s_g(v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
		rb2s_g(v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
	}
	for (i = 0; i < 8; i++)
		h[i] ^= v[i] ^ v[i + 8];
}

// out[0..outlen) = BLAKE2s-outlen(key[0..keylen), in[0..inlen)); 1 <= outlen <= 32, keylen <= 32.
static void ref_blake2s(u8 *out, size_t outlen, const u8 *key, size_t keylen, const u8 *in, size_t inlen)
{
	u32 h[8];
	u8 block[64];
	u64 total = (keylen > 0 ? 64 : 0) + (u64)inlen;   // bytes of the padded key block + the message
	u64 done = 0;
	size_t pos = 0;   // position in `in`
	int i;

	for (i = 0; i < 8; i++)
		h[i] = RB2S_IV[i];
	h[0] ^= 0x01010000u ^ ((u32)keylen << 8) ^ (u32)outlen;
	if (keylen > 0) {
		bytes_set(block, 0, 64);
		bytes_copy(block, key, keylen);
		done = 64;
		rb2s_compress(h, block, done, inlen == 0);
	}
	if (keylen == 0 || inlen > 0) {
		// the message blocks: all full blocks but the last, then the last (possibly partial or empty) block
		while (inlen - pos > 64) {
			bytes_copy(block, in + pos, 64);
			pos += 64;
			done += 64;
			rb2s_compress(h, block, done, 0);
		}
		bytes_set(block, 0, 64);
		bytes_copy(block, in + pos, inlen - pos);
		rb2s_compress(h, block, total, 1);
	}
	for (i = 0; (size_t)i < outlen; i++)
		out[i] = (u8)(h[i / 4] >> (8 * (i % 4)));
}

// ChaCha20 (RFC 8439 2.3), with the kernel's nonce layout: state words 12..15 are four little-endian words.
static u32 rc_rotl(u32 x, unsigned int n)
{
	return (x << n) | (x >> (32 - n));
}

static void rc_qr(u32 x[16], int a, int b, int c, int d)
{
	x[a] += x[b]; x[d] = rc_rotl(x[d] ^ x[a], 16);
	x[c] += x[d]; x[b] = rc_rotl(x[b] ^ x[c], 12);
	x[a] += x[b]; x[d] = rc_rotl(x[d] ^ x[a], 8);
	x[c] += x[d]; x[b] = rc_rotl(x[b] ^ x[c], 7);
}

static void rc_rounds(u32 x[16])
{
	int i;
	for (i = 0; i < 10; i++) {
		rc_qr(x, 0, 4, 8, 12);
		rc_qr(x, 1, 5, 9, 13);
		rc_qr(x, 2, 6, 10, 14);
		rc_qr(x, 3, 7, 11, 15);
		rc_qr(x, 0, 5, 10, 15);
		rc_qr(x, 1, 6, 11, 12);
		rc_qr(x, 2, 7, 8, 13);
		rc_qr(x, 3, 4, 9, 14);
	}
}

static void rc_setup(u32 s[16], const u8 key[32], const u32 w12, const u32 w13, const u32 w14, const u32 w15)
{
	int i;
	s[0] = 0x61707865u;
	s[1] = 0x3320646eu;
	s[2] = 0x79622d32u;
	s[3] = 0x6b206574u;
	for (i = 0; i < 8; i++)
		s[4 + i] = le32_load(key + 4 * i);
	s[12] = w12;
	s[13] = w13;
	s[14] = w14;
	s[15] = w15;
}

// one 64-byte keystream block for block counter `ctr` and the 64-bit nonce n (words 13 = 0, 14..15 = n)
static void ref_chacha20_block(u8 out[64], const u8 key[32], u32 ctr, u64 n)
{
	u32 s[16], x[16];
	int i;
	rc_setup(s, key, ctr, 0, (u32)n, (u32)(n >> 32));
	for (i = 0; i < 16; i++)
		x[i] = s[i];
	rc_rounds(x);
	for (i = 0; i < 16; i++)
		le32_store(out + 4 * i, x[i] + s[i]);
}

// HChaCha20: the rounds over (key, nonce[0..15]) without the final addition; words 0..3 and 12..15 as 32 bytes
static void ref_hchacha20(u8 out[32], const u8 key[32], const u8 nonce16[16])
{
	u32 x[16];
	int i;
	rc_setup(x, key, le32_load(nonce16), le32_load(nonce16 + 4), le32_load(nonce16 + 8), le32_load(nonce16 + 12));
	rc_rounds(x);
	for (i = 0; i < 4; i++) {
		le32_store(out + 4 * i, x[i]);
		le32_store(out + 16 + 4 * i, x[12 + i]);
	}
}

// Poly1305 (TweetNaCl crypto_onetimeauth, 17 limbs of 8 bits): state and one full 16-byte block (+ the 2^128 bit)
struct rpoly {
	u32 r[17];
	u32 h[17];
	u8 s[16];
};

static void rp_add(u32 h[17], const u32 c[17])
{
	u32 u = 0;
	int j;
	for (j = 0; j < 17; j++) {
		u += h[j] + c[j];
		h[j] = u & 255;
		u >>= 8;
	}
}

static void rp_init(struct rpoly *p, const u8 key[32])
{
	int j;
	for (j = 0; j < 17; j++) {
		p->r[j] = 0;
		p->h[j] = 0;
	}
	for (j = 0; j < 16; j++) {
		p->r[j] = key[j];
		p->s[j] = key[16 + j];
	}
	p->r[3] &= 15;
	p->r[4] &= 252;
	p->r[7] &= 15;
	p->r[8] &= 252;
	p->r[11] &= 15;
	p->r[12] &= 252;
	p->r[15] &= 15;
}

// h = (h + c) * r mod 2^130 - 5, c a 17-limb block (TweetNaCl's loop body)
static void rp_mul(struct rpoly *p, const u32 c[17])
{
	u32 x[17];
	u32 u;
	int i, j;
	rp_add(p->h, c);
	for (i = 0; i < 17; i++) {
		x[i] = 0;
		for (j = 0; j < 17; j++)
			x[i] += p->h[j] * ((j <= i) ? p->r[i - j] : 320 * p->r[i + 17 - j]);
	}
	for (i = 0; i < 17; i++)
		p->h[i] = x[i];
	u = 0;
	for (j = 0; j < 16; j++) {
		u += p->h[j];
		p->h[j] = u & 255;
		u >>= 8;
	}
	u += p->h[16];
	p->h[16] = u & 3;
	u = 5 * (u >> 2);
	for (j = 0; j < 16; j++) {
		u += p->h[j];
		p->h[j] = u & 255;
		u >>= 8;
	}
	u += p->h[16];
	p->h[16] = u;
}

// one full 16-byte block (with the 2^128 bit)
static void rp_block(struct rpoly *p, const u8 m[16])
{
	u32 c[17];
	int j;
	for (j = 0; j < 16; j++)
		c[j] = m[j];
	c[16] = 1;
	rp_mul(p, c);
}


// the message in[0..len) zero padded to a multiple of 16 (the AEAD's "pad16"), as full blocks
static void rp_padded(struct rpoly *p, const u8 *in, size_t len)
{
	u8 b[16];
	size_t pos = 0;
	while (len - pos >= 16) {
		rp_block(p, in + pos);
		pos += 16;
	}
	if (len - pos > 0) {
		bytes_set(b, 0, 16);
		bytes_copy(b, in + pos, len - pos);
		rp_block(p, b);
	}
}

static void rp_final(struct rpoly *p, u8 out[16])
{
	static const u32 minusp[17] = { 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 252 };
	u32 g[17], c[17], s;
	int j;
	for (j = 0; j < 17; j++)
		g[j] = p->h[j];
	rp_add(p->h, minusp);
	s = -(p->h[16] >> 7);
	for (j = 0; j < 17; j++)
		p->h[j] ^= s & (g[j] ^ p->h[j]);
	for (j = 0; j < 16; j++)
		c[j] = p->s[j];
	c[16] = 0;
	rp_add(p->h, c);
	for (j = 0; j < 16; j++)
		out[j] = (u8)p->h[j];
}

// Poly1305 (RFC 8439 2.5) of any message: full blocks, then a last partial block with 0x01 after it
static void ref_poly1305(u8 out[16], const u8 key[32], const u8 *m, size_t len)
{
	struct rpoly p;
	u32 c[17];
	size_t pos = 0, j;
	rp_init(&p, key);
	while (len - pos >= 16) {
		rp_block(&p, m + pos);
		pos += 16;
	}
	if (len - pos > 0) {
		for (j = 0; j < 17; j++)
			c[j] = 0;
		for (j = 0; j < len - pos; j++)
			c[j] = m[pos + j];
		c[len - pos] = 1;
		rp_mul(&p, c);
	}
	rp_final(&p, out);
}

// ChaCha20-Poly1305 (RFC 8439 2.8) with a 64-bit nonce (the kernel's API: 32 zero bits, then nonce LE)
static void ref_aead_tag(u8 tag[16], const u8 key[32], u64 nonce, const u8 *ad, size_t adlen, const u8 *ct, size_t ctlen)
{
	struct rpoly p;
	u8 blk[64];
	u8 lens[16];
	ref_chacha20_block(blk, key, 0, nonce);
	rp_init(&p, blk);
	rp_padded(&p, ad, adlen);
	rp_padded(&p, ct, ctlen);
	le64_store(lens, (u64)adlen);
	le64_store(lens + 8, (u64)ctlen);
	rp_block(&p, lens);
	rp_final(&p, tag);
}

// keystream XOR from block counter 1
static void ref_chacha20_xor(u8 *dst, const u8 *src, size_t len, const u8 key[32], u64 nonce)
{
	u8 blk[64];
	size_t pos = 0, i;
	u32 ctr = 1;
	while (pos < len) {
		ref_chacha20_block(blk, key, ctr, nonce);
		for (i = 0; i < 64 && pos + i < len; i++)
			dst[pos + i] = src[pos + i] ^ blk[i];
		pos += i;
		ctr++;
	}
}

// dst[0..len+16) = ciphertext || tag
static void ref_aead_encrypt(u8 *dst, const u8 *src, size_t len, const u8 *ad, size_t adlen, u64 nonce, const u8 key[32])
{
	ref_chacha20_xor(dst, src, len, key, nonce);
	ref_aead_tag(dst + len, key, nonce, ad, adlen, dst, len);
}

// 1 and dst[0..len-16) = plaintext if the tag verifies (len >= 16); else 0 and dst untouched
static int ref_aead_decrypt(u8 *dst, const u8 *src, size_t len, const u8 *ad, size_t adlen, u64 nonce, const u8 key[32])
{
	u8 tag[16];
	if (len < 16)
		return 0;
	ref_aead_tag(tag, key, nonce, ad, adlen, src, len - 16);
	if (!bytes_eq(tag, src + len - 16, 16))
		return 0;
	ref_chacha20_xor(dst, src, len - 16, key, nonce);
	return 1;
}

// XChaCha20-Poly1305: subkey = HChaCha20(key, nonce[0..15]), then the AEAD above with nonce LE64(nonce[16..23])
static u64 le64_load(const u8 *p)
{
	return (u64)le32_load(p) | ((u64)le32_load(p + 4) << 32);
}

static void ref_xaead_encrypt(u8 *dst, const u8 *src, size_t len, const u8 *ad, size_t adlen, const u8 nonce[24], const u8 key[32])
{
	u8 sub[32];
	ref_hchacha20(sub, key, nonce);
	ref_aead_encrypt(dst, src, len, ad, adlen, le64_load(nonce + 16), sub);
}

static int ref_xaead_decrypt(u8 *dst, const u8 *src, size_t len, const u8 *ad, size_t adlen, const u8 nonce[24], const u8 key[32])
{
	u8 sub[32];
	ref_hchacha20(sub, key, nonce);
	return ref_aead_decrypt(dst, src, len, ad, adlen, le64_load(nonce + 16), sub);
}

// X25519 (RFC 7748), TweetNaCl crypto_scalarmult (public domain: Bernstein, van Gastel, Janssen, Lange, Schwabe,
// Smetsers), 16 signed limbs of 16 bits.  Changes: `c << 16` of a possibly negative c is written c * 65536 (a
// left shift of a negative value is undefined in C); loops written out.
typedef s64 rgf[16];

static void rx_car(rgf o)
{
	int i;
	s64 c;
	for (i = 0; i < 16; i++) {
		o[i] += (s64)1 << 16;
		c = o[i] >> 16;
		if (i < 15)
			o[i + 1] += c - 1;
		else
			o[0] += 38 * (c - 1);
		o[i] -= c * 65536;
	}
}

static void rx_sel(rgf p, rgf q, int b)
{
	s64 t, c = ~((s64)b - 1);
	int i;
	for (i = 0; i < 16; i++) {
		t = c & (p[i] ^ q[i]);
		p[i] ^= t;
		q[i] ^= t;
	}
}

static void rx_pack(u8 o[32], const rgf n)
{
	int i, j, b;
	rgf m, t;
	for (i = 0; i < 16; i++)
		t[i] = n[i];
	rx_car(t);
	rx_car(t);
	rx_car(t);
	for (j = 0; j < 2; j++) {
		m[0] = t[0] - 0xffed;
		for (i = 1; i < 15; i++) {
			m[i] = t[i] - 0xffff - ((m[i - 1] >> 16) & 1);
			m[i - 1] &= 0xffff;
		}
		m[15] = t[15] - 0x7fff - ((m[14] >> 16) & 1);
		b = (int)((m[15] >> 16) & 1);
		m[14] &= 0xffff;
		rx_sel(t, m, 1 - b);
	}
	for (i = 0; i < 16; i++) {
		o[2 * i] = (u8)(t[i] & 0xff);
		o[2 * i + 1] = (u8)(t[i] >> 8);
	}
}

static void rx_unpack(rgf o, const u8 n[32])
{
	int i;
	for (i = 0; i < 16; i++)
		o[i] = n[2 * i] + ((s64)n[2 * i + 1] << 8);
	o[15] &= 0x7fff;
}

static void rx_add(rgf o, const rgf a, const rgf b)
{
	int i;
	for (i = 0; i < 16; i++)
		o[i] = a[i] + b[i];
}

static void rx_sub(rgf o, const rgf a, const rgf b)
{
	int i;
	for (i = 0; i < 16; i++)
		o[i] = a[i] - b[i];
}

static void rx_mul(rgf o, const rgf a, const rgf b)
{
	s64 t[31];
	int i, j;
	for (i = 0; i < 31; i++)
		t[i] = 0;
	for (i = 0; i < 16; i++)
		for (j = 0; j < 16; j++)
			t[i + j] += a[i] * b[j];
	for (i = 0; i < 15; i++)
		t[i] += 38 * t[i + 16];
	for (i = 0; i < 16; i++)
		o[i] = t[i];
	rx_car(o);
	rx_car(o);
}

static void rx_inv(rgf o, const rgf in)
{
	rgf c;
	int a;
	for (a = 0; a < 16; a++)
		c[a] = in[a];
	for (a = 253; a >= 0; a--) {
		rx_mul(c, c, c);
		if (a != 2 && a != 4)
			rx_mul(c, c, in);
	}
	for (a = 0; a < 16; a++)
		o[a] = c[a];
}

// q = X25519(n, p): the scalar is clamped, the top bit of the point ignored
static void ref_x25519(u8 q[32], const u8 n[32], const u8 p[32])
{
	static const rgf k121665 = { 0xDB41, 1 };
	u8 z[32];
	rgf x, a, b, c, d, e, f;
	int i;
	for (i = 0; i < 31; i++)
		z[i] = n[i];
	z[31] = (n[31] & 127) | 64;
	z[0] &= 248;
	rx_unpack(x, p);
	for (i = 0; i < 16; i++) {
		b[i] = x[i];
		d[i] = a[i] = c[i] = 0;
	}
	a[0] = d[0] = 1;
	for (i = 254; i >= 0; --i) {
		int r = (z[i >> 3] >> (i & 7)) & 1;
		rx_sel(a, b, r);
		rx_sel(c, d, r);
		rx_add(e, a, c);
		rx_sub(a, a, c);
		rx_add(c, b, d);
		rx_sub(b, b, d);
		rx_mul(d, e, e);
		rx_mul(f, a, a);
		rx_mul(a, c, a);
		rx_mul(c, b, e);
		rx_add(e, a, c);
		rx_sub(a, a, c);
		rx_mul(b, a, a);
		rx_sub(c, d, f);
		rx_mul(a, c, k121665);
		rx_add(a, a, d);
		rx_mul(c, c, a);
		rx_mul(a, d, f);
		rx_mul(d, b, x);
		rx_mul(b, e, e);
		rx_sel(a, b, r);
		rx_sel(c, d, r);
	}
	rx_inv(c, c);
	rx_mul(a, a, c);
	rx_pack(q, a);
}

// ---------------------------------------------------------------------------------------------------------------
// 2. the protocol model (over the kernel's primitive functions)
// ---------------------------------------------------------------------------------------------------------------

// HASH(a || b) = BLAKE2s-256 (the kernel's blake2s_init/update/final)
static void m_hash2(u8 out[32], const u8 *a, size_t alen, const u8 *b, size_t blen)
{
	struct blake2s_ctx ctx;
	blake2s_init(&ctx, 32);
	blake2s_update(&ctx, a, alen);
	blake2s_update(&ctx, b, blen);
	blake2s_final(&ctx, out);
}

// HMAC-BLAKE2s (RFC 2104, block 64) with a 32-byte key: H((K ^ opad) || H((K ^ ipad) || in))
static void m_hmac(u8 out[32], const u8 key[32], const u8 *in, size_t inlen)
{
	u8 k[64];
	u8 inner[32];
	int i;
	for (i = 0; i < 64; i++)
		k[i] = (u8)((i < 32 ? key[i] : 0) ^ 0x36);
	m_hash2(inner, k, 64, in, inlen);
	for (i = 0; i < 64; i++)
		k[i] = (u8)((i < 32 ? key[i] : 0) ^ 0x5c);
	m_hash2(out, k, 64, inner, 32);
}

// HKDF (RFC 5869) with HMAC-BLAKE2s, as WireGuard's KDF_n: T1 = HMAC(prk, 0x1), T_{i+1} = HMAC(prk, T_i || i+1)
static void m_kdf(u8 t1[32], u8 t2[32], u8 t3[32], const u8 ck[32], const u8 *in, size_t inlen)
{
	u8 prk[32];
	u8 buf[33];
	m_hmac(prk, ck, in, inlen);
	buf[0] = 1;
	m_hmac(t1, prk, buf, 1);
	bytes_copy(buf, t1, 32);
	buf[32] = 2;
	m_hmac(t2, prk, buf, 33);
	bytes_copy(buf, t2, 32);
	buf[32] = 3;
	m_hmac(t3, prk, buf, 33);
}

// DH: the kernel's curve25519_generic; the model's "DH failed" is the all-zero result
static int m_dh(u8 out[32], const u8 priv[32], const u8 pub[32])
{
	curve25519_generic(out, priv, pub);
	return !bytes_zero(out, 32);
}

static const u8 M_BASEPOINT[32] = { 9 };

static void m_clamp(u8 k[32])
{
	k[0] &= 248;
	k[31] = (u8)((k[31] & 127) | 64);
}

// The static identity after wg_noise_set_static_identity_private_key(raw): private = clamp(raw), public =
// X25519(raw, 9); usable ("has_identity") iff raw is not all zero and the public key is not all zero.
struct m_identity {
	u8 priv[32];
	u8 pub[32];
	int ok;
};

static void m_identity_of(struct m_identity *id, const u8 raw[32])
{
	int pub_ok;
	bytes_copy(id->priv, raw, 32);
	m_clamp(id->priv);
	pub_ok = m_dh(id->pub, raw, M_BASEPOINT);
	id->ok = !bytes_zero(raw, 32) && pub_ok;
}

// Initial chaining key and hash (whitepaper 5.4.2): Ci = HASH(CONSTRUCTION), Hi = HASH(Ci || IDENTIFIER),
// Hi = HASH(Hi || S_r^pub)
static const u8 M_CONSTRUCTION[37] = "Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s";
static const u8 M_IDENTIFIER[34] = "WireGuard v1 zx2c4 Jason@zx2c4.com";

struct m_state {
	u8 ck[32];
	u8 h[32];
};

static void m_start(struct m_state *s, const u8 responder_pub[32])
{
	u8 h0[32];
	m_hash2(s->ck, M_CONSTRUCTION, 37, M_CONSTRUCTION, 0);
	m_hash2(h0, s->ck, 32, M_IDENTIFIER, 34);
	m_hash2(s->h, h0, 32, responder_pub, 32);
}

static void m_mix_hash(struct m_state *s, const u8 *d, size_t n)
{
	u8 t[32];
	m_hash2(t, s->h, 32, d, n);
	bytes_copy(s->h, t, 32);
}

// C = KDF1(C, d)
static void m_mix_ck(struct m_state *s, const u8 *d, size_t n)
{
	u8 t1[32], t2[32], t3[32];
	m_kdf(t1, t2, t3, s->ck, d, n);
	bytes_copy(s->ck, t1, 32);
}

// (C, k) = KDF2(C, d)
static void m_mix_key(struct m_state *s, u8 key[32], const u8 *d, size_t n)
{
	u8 t1[32], t2[32], t3[32];
	m_kdf(t1, t2, t3, s->ck, d, n);
	bytes_copy(s->ck, t1, 32);
	bytes_copy(key, t2, 32);
}

// (C, tau, k) = KDF3(C, Q); H = HASH(H || tau)
static void m_mix_psk(struct m_state *s, u8 key[32], const u8 psk[32])
{
	u8 t1[32], t2[32], t3[32];
	m_kdf(t1, t2, t3, s->ck, psk, 32);
	bytes_copy(s->ck, t1, 32);
	bytes_copy(key, t3, 32);
	m_mix_hash(s, t2, 32);
}

// AEAD(k, 0, p, H), then H = HASH(H || c)
static void m_encrypt_and_hash(struct m_state *s, u8 *c, const u8 *p, size_t n, const u8 key[32])
{
	chacha20poly1305_encrypt(c, p, n, s->h, 32, 0, key);
	m_mix_hash(s, c, n + 16);
}

// the opposite: 1 and p, H updated if the tag verifies; 0 (H unchanged) otherwise
static int m_decrypt_and_hash(struct m_state *s, u8 *p, const u8 *c, size_t n, const u8 key[32])
{
	if (!chacha20poly1305_decrypt(p, c, n, s->h, 32, 0, key))
		return 0;
	m_mix_hash(s, c, n);
	return 1;
}

// TAI64N of the real clock: big-endian 2^62 + 10 + sec, then big-endian nanoseconds rounded down to a multiple of
// 2^24 (the largest power of two <= 10^9 / 50, INITIATIONS_PER_SECOND)
static void m_tai64n(u8 out[12], s64 sec, long nsec)
{
	u64 s = 0x400000000000000aULL + (u64)sec;
	u32 n = (u32)((unsigned long)nsec & ~((unsigned long)16777216 - 1));
	int i;
	for (i = 0; i < 8; i++)
		out[i] = (u8)(s >> (56 - 8 * i));
	for (i = 0; i < 4; i++)
		out[8 + i] = (u8)(n >> (24 - 8 * i));
}

// The handshake initiation (whitepaper 5.4.2), message fields, and the initiator's state after it.
struct m_initiation {
	u8 ephemeral[32];
	u8 enc_static[48];
	u8 enc_timestamp[28];
	u8 eph_priv[32];
	struct m_state st;
};

// Initiator with identity (spriv, spub), peer static rpub, precomputed DH(spriv, rpub) `ss` (all zero if it
// failed), ephemeral random bytes eraw (clamped here), timestamp ts.  Returns 1 iff every step succeeds:
// E_pub = X25519(E_priv, 9) not zero, DH(E_priv, S_r) not zero, ss not zero.
static int m_create_initiation(struct m_initiation *o, const u8 spub[32], const u8 rpub[32], const u8 ss[32],
			       const u8 eraw[32], const u8 ts[12])
{
	u8 key[32], dh[32];
	m_start(&o->st, rpub);
	bytes_copy(o->eph_priv, eraw, 32);
	m_clamp(o->eph_priv);
	if (!m_dh(o->ephemeral, o->eph_priv, M_BASEPOINT))
		return 0;
	m_mix_hash(&o->st, o->ephemeral, 32);
	m_mix_ck(&o->st, o->ephemeral, 32);
	if (!m_dh(dh, o->eph_priv, rpub))
		return 0;
	m_mix_key(&o->st, key, dh, 32);
	m_encrypt_and_hash(&o->st, o->enc_static, spub, 32, key);
	if (bytes_zero(ss, 32))
		return 0;
	m_mix_key(&o->st, key, ss, 32);
	m_encrypt_and_hash(&o->st, o->enc_timestamp, ts, 12, key);
	return 1;
}

// The responder's view of an initiation: from its identity (rid) and the message fields; on success the
// initiator's static key, timestamp and the state.  Returns 1 iff: DH(S_r, E_i) not zero, the static decrypts,
// [the caller: a peer has that key, its precomputed DH is not zero], the timestamp decrypts.  Stage 1 (up to the
// static) and stage 2 (from ss) are separate so that the caller does the peer lookup in between.
struct m_consumed_initiation {
	struct m_state st;
	u8 key[32];
	u8 spub[32];
	u8 ts[12];
};

static int m_consume_initiation_1(struct m_consumed_initiation *o, const struct m_identity *rid,
				  const u8 ephemeral[32], const u8 enc_static[48])
{
	u8 dh[32];
	m_start(&o->st, rid->pub);
	m_mix_hash(&o->st, ephemeral, 32);
	m_mix_ck(&o->st, ephemeral, 32);
	if (!m_dh(dh, rid->priv, ephemeral))
		return 0;
	m_mix_key(&o->st, o->key, dh, 32);
	return m_decrypt_and_hash(&o->st, o->spub, enc_static, 48, o->key);
}

static int m_consume_initiation_2(struct m_consumed_initiation *o, const u8 ss[32], const u8 enc_timestamp[28])
{
	if (bytes_zero(ss, 32))
		return 0;
	m_mix_key(&o->st, o->key, ss, 32);
	return m_decrypt_and_hash(&o->st, o->ts, enc_timestamp, 28, o->key);
}

// The handshake response (whitepaper 5.4.3) from the responder's state `st` (after consuming the initiation),
// initiator ephemeral ei, initiator static si, psk, responder ephemeral random bytes eraw.  Returns 1 iff
// E_r^pub, DH(E_r, E_i) and DH(E_r, S_i) are all non-zero.
struct m_response {
	u8 ephemeral[32];
	u8 enc_nothing[16];
	u8 eph_priv[32];
	struct m_state st;
};

static int m_create_response(struct m_response *o, const struct m_state *st, const u8 ei[32], const u8 si[32],
			     const u8 psk[32], const u8 eraw[32])
{
	u8 dh[32], key[32];
	bytes_copy(o->st.ck, st->ck, 32);
	bytes_copy(o->st.h, st->h, 32);
	bytes_copy(o->eph_priv, eraw, 32);
	m_clamp(o->eph_priv);
	if (!m_dh(o->ephemeral, o->eph_priv, M_BASEPOINT))
		return 0;
	m_mix_hash(&o->st, o->ephemeral, 32);
	m_mix_ck(&o->st, o->ephemeral, 32);
	if (!m_dh(dh, o->eph_priv, ei))
		return 0;
	m_mix_ck(&o->st, dh, 32);
	if (!m_dh(dh, o->eph_priv, si))
		return 0;
	m_mix_ck(&o->st, dh, 32);
	m_mix_psk(&o->st, key, psk);
	m_encrypt_and_hash(&o->st, o->enc_nothing, M_BASEPOINT, 0, key);
	return 1;
}

// The initiator's view of a response: from its state after the initiation (st), its ephemeral private key, its
// static private key, psk and the message fields.  Returns 1 iff DH(E_i, E_r), DH(S_i, E_r) are non-zero and the
// empty payload's tag verifies; *out is the state after.
static int m_consume_response(struct m_state *out, const struct m_state *st, const u8 eph_priv[32],
			      const u8 spriv[32], const u8 psk[32], const u8 ephemeral[32], const u8 enc_nothing[16])
{
	u8 dh[32], key[32], nothing[1];
	bytes_copy(out->ck, st->ck, 32);
	bytes_copy(out->h, st->h, 32);
	m_mix_hash(out, ephemeral, 32);
	m_mix_ck(out, ephemeral, 32);
	if (!m_dh(dh, eph_priv, ephemeral))
		return 0;
	m_mix_ck(out, dh, 32);
	if (!m_dh(dh, spriv, ephemeral))
		return 0;
	m_mix_ck(out, dh, 32);
	m_mix_psk(out, key, psk);
	return m_decrypt_and_hash(out, nothing, enc_nothing, 16, key);
}

// Transport keys (whitepaper 5.4.5): (T_send^i = T_recv^r, T_recv^i = T_send^r) = KDF2(C, empty)
static void m_transport(u8 first[32], u8 second[32], const u8 ck[32])
{
	u8 t3[32];
	m_kdf(first, second, t3, ck, M_BASEPOINT, 0);
}

// mac1 key and cookie key: HASH(LABEL || S_pub) with the 8-byte labels "mac1----" and "cookie--"
static const u8 M_LABEL_MAC1[8] = "mac1----";
static const u8 M_LABEL_COOKIE[8] = "cookie--";

static void m_label_key(u8 out[32], const u8 label[8], const u8 pub[32])
{
	m_hash2(out, label, 8, pub, 32);
}

// MAC(key, m) = keyed BLAKE2s-128 (the kernel's inline blake2s(), which is blake2s_init_key + update + final)
static void m_mac(u8 out[16], const u8 *key, size_t keylen, const u8 *msg, size_t len)
{
	blake2s(key, keylen, msg, len, out, 16);
}

// ---------------------------------------------------------------------------------------------------------------
// the device and peers as the kernel sets them up (device.c/peer.c order), on the shim's structs
// ---------------------------------------------------------------------------------------------------------------

// wg_noise_init: the constant initial hash and chaining key (once per run; harness globals are set in main)
static void setup_device(struct wg_device *wg, struct index_hashtable *itab, struct pubkey_hashtable *ptab,
			 const u8 raw_priv[32])
{
	// the device is kzalloc'd in the kernel: the fields the code reads before writing start at zero
	wg->dev = NULL;
	itab->head = NULL;
	ptab->head = NULL;
	wg->index_hashtable = itab;
	wg->peer_hashtable = ptab;
	wg->static_identity.has_identity = false;
	bytes_set(wg->static_identity.static_public, 0, 32);
	bytes_set(wg->static_identity.static_private, 0, 32);
	bytes_set(wg->cookie_checker.cookie_encryption_key, 0, 32);
	bytes_set(wg->cookie_checker.message_mac1_key, 0, 32);
	wg_noise_set_static_identity_private_key(&wg->static_identity, raw_priv);
	wg_cookie_checker_init(&wg->cookie_checker, wg);
	wg_cookie_checker_precompute_device_keys(&wg->cookie_checker);
}

// peer.c wg_peer_create, reduced: handshake, cookie, keypairs; the peer is linked into the public-key table
static void setup_peer(struct wg_peer *peer, struct wg_device *wg, const u8 pub[32], const u8 *psk, u64 id)
{
	peer->device = wg;
	peer->is_dead = false;
	peer->keypairs.current_keypair = NULL;
	peer->keypairs.previous_keypair = NULL;
	peer->keypairs.next_keypair = NULL;
	peer->last_sent_handshake.counter = 0;
	peer->refcount.refcount = 1;
	peer->internal_id = id;
	peer->handshake.entry.next = NULL;
	peer->handshake.entry.hashed = false;
	wg_noise_handshake_init(&peer->handshake, &wg->static_identity, pub, psk, peer);
	wg_cookie_init(&peer->latest_cookie);
	wg_cookie_checker_precompute_peer_keys(peer);
	peer->pubkey_next = wg->peer_hashtable->head;
	wg->peer_hashtable->head = peer;
}

// the precomputed static-static DH of a peer (wg_noise_precompute_static_static): X25519(priv, peer) or zero
static void m_precomputed(u8 out[32], const struct m_identity *id, const u8 peer_pub[32])
{
	if (!id->ok || !m_dh(out, id->priv, peer_pub))
		bytes_set(out, 0, 32);
}

// is `e` in the index table, exactly once?
static int table_has(const struct index_hashtable *t, const struct index_hashtable_entry *e)
{
	const struct index_hashtable_entry *it;
	int n = 0;
	for (it = t->head; it; it = it->next)
		if (it == e)
			n++;
	return n == 1 && e->hashed;
}

// is the index used by exactly one entry of the table?
static int table_index_unique(const struct index_hashtable *t, __le32 index)
{
	const struct index_hashtable_entry *it;
	int n = 0;
	for (it = t->head; it; it = it->next)
		if (it->index == index)
			n++;
	return n == 1;
}

static size_t table_len(const struct index_hashtable *t)
{
	const struct index_hashtable_entry *it;
	size_t n = 0;
	for (it = t->head; it; it = it->next)
		n++;
	return n;
}

// Snapshot of the mutable part of a handshake (every field but the lock), compared field by field (a byte copy of
// a struct holding pointers is undefined in CompCert's memory model).
struct hs_snap {
	struct wg_peer *peer;
	struct index_hashtable_entry *next;
	bool hashed;
	enum index_hashtable_type type;
	__le32 index;
	enum noise_handshake_state state;
	u64 last_initiation_consumption;
	struct noise_static_identity *static_identity;
	u8 ephemeral_private[32];
	u8 remote_static[32];
	u8 remote_ephemeral[32];
	u8 precomputed_static_static[32];
	u8 preshared_key[32];
	u8 hash[32];
	u8 chaining_key[32];
	u8 latest_timestamp[12];
	__le32 remote_index;
};

static void hs_take(struct hs_snap *s, const struct noise_handshake *h)
{
	s->peer = h->entry.peer;
	s->next = h->entry.next;
	s->hashed = h->entry.hashed;
	s->type = h->entry.type;
	s->index = h->entry.index;
	s->state = h->state;
	s->last_initiation_consumption = h->last_initiation_consumption;
	s->static_identity = h->static_identity;
	bytes_copy(s->ephemeral_private, h->ephemeral_private, 32);
	bytes_copy(s->remote_static, h->remote_static, 32);
	bytes_copy(s->remote_ephemeral, h->remote_ephemeral, 32);
	bytes_copy(s->precomputed_static_static, h->precomputed_static_static, 32);
	bytes_copy(s->preshared_key, h->preshared_key, 32);
	bytes_copy(s->hash, h->hash, 32);
	bytes_copy(s->chaining_key, h->chaining_key, 32);
	bytes_copy(s->latest_timestamp, h->latest_timestamp, 12);
	s->remote_index = h->remote_index;
}

static int hs_same(const struct hs_snap *s, const struct noise_handshake *h)
{
	return s->peer == h->entry.peer && s->next == h->entry.next && s->hashed == h->entry.hashed &&
	       s->type == h->entry.type && s->index == h->entry.index && s->state == h->state &&
	       s->last_initiation_consumption == h->last_initiation_consumption &&
	       s->static_identity == h->static_identity &&
	       bytes_eq(s->ephemeral_private, h->ephemeral_private, 32) &&
	       bytes_eq(s->remote_static, h->remote_static, 32) &&
	       bytes_eq(s->remote_ephemeral, h->remote_ephemeral, 32) &&
	       bytes_eq(s->precomputed_static_static, h->precomputed_static_static, 32) &&
	       bytes_eq(s->preshared_key, h->preshared_key, 32) && bytes_eq(s->hash, h->hash, 32) &&
	       bytes_eq(s->chaining_key, h->chaining_key, 32) &&
	       bytes_eq(s->latest_timestamp, h->latest_timestamp, 12) && s->remote_index == h->remote_index;
}

// the zeroed handshake of handshake_zero (after begin_session / clear): ephemeral, remote ephemeral, hash,
// chaining key and remote index zero, state ZEROED; everything else as in `s`
static int hs_zeroed_from(const struct hs_snap *s, const struct noise_handshake *h)
{
	return h->state == HANDSHAKE_ZEROED && h->remote_index == 0 && bytes_zero(h->ephemeral_private, 32) &&
	       bytes_zero(h->remote_ephemeral, 32) && bytes_zero(h->hash, 32) && bytes_zero(h->chaining_key, 32) &&
	       s->peer == h->entry.peer && s->type == h->entry.type &&
	       s->last_initiation_consumption == h->last_initiation_consumption &&
	       s->static_identity == h->static_identity &&
	       bytes_eq(s->remote_static, h->remote_static, 32) &&
	       bytes_eq(s->precomputed_static_static, h->precomputed_static_static, 32) &&
	       bytes_eq(s->preshared_key, h->preshared_key, 32) &&
	       bytes_eq(s->latest_timestamp, h->latest_timestamp, 12);
}

// Snapshot of a peer's cookie state
struct ck_snap {
	u64 birthdate;
	bool is_valid;
	u8 cookie[16];
	bool have_sent_mac1;
	u8 last_mac1_sent[16];
	u8 cookie_decryption_key[32];
	u8 message_mac1_key[32];
};

static void ck_take(struct ck_snap *s, const struct cookie *c)
{
	s->birthdate = c->birthdate;
	s->is_valid = c->is_valid;
	bytes_copy(s->cookie, c->cookie, 16);
	s->have_sent_mac1 = c->have_sent_mac1;
	bytes_copy(s->last_mac1_sent, c->last_mac1_sent, 16);
	bytes_copy(s->cookie_decryption_key, c->cookie_decryption_key, 32);
	bytes_copy(s->message_mac1_key, c->message_mac1_key, 32);
}

static int ck_same(const struct ck_snap *s, const struct cookie *c)
{
	return s->birthdate == c->birthdate && s->is_valid == c->is_valid && bytes_eq(s->cookie, c->cookie, 16) &&
	       s->have_sent_mac1 == c->have_sent_mac1 && bytes_eq(s->last_mac1_sent, c->last_mac1_sent, 16) &&
	       bytes_eq(s->cookie_decryption_key, c->cookie_decryption_key, 32) &&
	       bytes_eq(s->message_mac1_key, c->message_mac1_key, 32);
}

// Snapshot of the rest of a peer, i.e. every field of struct wg_peer (shim peer.h) except the
// handshake (hs_snap) and the reference count: the device, the dead flag, the three keypair slots, the time of the
// last sent handshake, the cookie state (ck_snap), the internal id and the public-key table link.  With hs_snap
// and the reference count it is the WHOLE peer (the locks are no-ops, S02).
struct pr_snap {
	struct wg_device *device;
	bool is_dead;
	struct noise_keypair *current_keypair;
	struct noise_keypair *previous_keypair;
	struct noise_keypair *next_keypair;
	s64 last_sent_handshake;
	struct ck_snap cookie;
	u64 internal_id;
	struct wg_peer *pubkey_next;
};

static void pr_take(struct pr_snap *s, const struct wg_peer *p)
{
	s->device = p->device;
	s->is_dead = p->is_dead;
	s->current_keypair = p->keypairs.current_keypair;
	s->previous_keypair = p->keypairs.previous_keypair;
	s->next_keypair = p->keypairs.next_keypair;
	s->last_sent_handshake = p->last_sent_handshake.counter;
	ck_take(&s->cookie, &p->latest_cookie);
	s->internal_id = p->internal_id;
	s->pubkey_next = p->pubkey_next;
}

// the rest of the peer but its cookie state is unchanged
static int pr_same_but_cookie(const struct pr_snap *s, const struct wg_peer *p)
{
	return s->device == p->device && s->is_dead == p->is_dead &&
	       s->current_keypair == p->keypairs.current_keypair &&
	       s->previous_keypair == p->keypairs.previous_keypair && s->next_keypair == p->keypairs.next_keypair &&
	       s->last_sent_handshake == p->last_sent_handshake.counter && s->internal_id == p->internal_id &&
	       s->pubkey_next == p->pubkey_next;
}

// the rest of the peer is unchanged
static int pr_same(const struct pr_snap *s, const struct wg_peer *p)
{
	return pr_same_but_cookie(s, p) && ck_same(&s->cookie, &p->latest_cookie);
}

// draw one of the five handshake states
static enum noise_handshake_state draw_hs_state(void)
{
	switch (nondet_u8() % 5) {
	case 0: return HANDSHAKE_ZEROED;
	case 1: return HANDSHAKE_CREATED_INITIATION;
	case 2: return HANDSHAKE_CONSUMED_INITIATION;
	case 3: return HANDSHAKE_CREATED_RESPONSE;
	default: break;
	}
	return HANDSHAKE_CONSUMED_RESPONSE;
}

// the expected static public key after wg_noise_set_static_identity_private_key: X25519(raw, 9), except that a
// raw key of all zeros leaves the (zeroed) field unwritten
static void m_static_public_field(u8 out[32], const struct m_identity *id, const u8 raw[32])
{
	if (bytes_zero(raw, 32))
		bytes_set(out, 0, 32);
	else
		bytes_copy(out, id->pub, 32);
}

// byte images of the messages (the structs have no padding: sizeof 148 / 92 / 64)
#define INIT_LEN 148
#define RESP_LEN 92
#define COOKIE_MSG_LEN 64

static void init_img(u8 img[INIT_LEN], const struct message_handshake_initiation *m)
{
	le32_store(img, m->header.type);
	le32_store(img + 4, m->sender_index);
	bytes_copy(img + 8, m->unencrypted_ephemeral, 32);
	bytes_copy(img + 40, m->encrypted_static, 48);
	bytes_copy(img + 88, m->encrypted_timestamp, 28);
	bytes_copy(img + 116, m->macs.mac1, 16);
	bytes_copy(img + 132, m->macs.mac2, 16);
}

static void resp_img(u8 img[RESP_LEN], const struct message_handshake_response *m)
{
	le32_store(img, m->header.type);
	le32_store(img + 4, m->sender_index);
	le32_store(img + 8, m->receiver_index);
	bytes_copy(img + 12, m->unencrypted_ephemeral, 32);
	bytes_copy(img + 44, m->encrypted_nothing, 16);
	bytes_copy(img + 60, m->macs.mac1, 16);
	bytes_copy(img + 76, m->macs.mac2, 16);
}

static void cookie_img(u8 img[COOKIE_MSG_LEN], const struct message_handshake_cookie *m)
{
	le32_store(img, m->header.type);
	le32_store(img + 4, m->receiver_index);
	bytes_copy(img + 8, m->nonce, 24);
	bytes_copy(img + 32, m->encrypted_cookie, 32);
}

static void fill_init(struct message_handshake_initiation *m)
{
	m->header.type = nondet_u32();
	m->sender_index = nondet_u32();
	nondet_bytes(m->unencrypted_ephemeral, 32);
	nondet_bytes(m->encrypted_static, 48);
	nondet_bytes(m->encrypted_timestamp, 28);
	nondet_bytes(m->macs.mac1, 16);
	nondet_bytes(m->macs.mac2, 16);
}

static void fill_resp(struct message_handshake_response *m)
{
	m->header.type = nondet_u32();
	m->sender_index = nondet_u32();
	m->receiver_index = nondet_u32();
	nondet_bytes(m->unencrypted_ephemeral, 32);
	nondet_bytes(m->encrypted_nothing, 16);
	nondet_bytes(m->macs.mac1, 16);
	nondet_bytes(m->macs.mac2, 16);
}

static void fill_cookie_msg(struct message_handshake_cookie *m)
{
	m->header.type = nondet_u32();
	m->receiver_index = nondet_u32();
	nondet_bytes(m->nonce, 24);
	nondet_bytes(m->encrypted_cookie, 32);
}

static void draw_real_clock(void)
{
	wg_shim_real_sec = (s64)draw_u64();
	wg_shim_real_nsec = (long)(nondet_u32() % 1000000000u);
}

// consume_initiation's replay and flood checks, as the model states them: accepted only if the timestamp is
// lexicographically (big endian) greater than the latest one, and the last consumption was at least 20 ms
// (NSEC_PER_SEC / INITIATIONS_PER_SECOND) before now, compared as signed 64-bit values
static int m_ts_newer(const u8 t[12], const u8 latest[12])
{
	int i;
	for (i = 0; i < 12; i++) {
		if (t[i] != latest[i])
			return t[i] > latest[i];
	}
	return 0;
}

static int m_not_flood(u64 last, u64 now)
{
	return !((s64)last + 20000000 > (s64)now);
}

// last_initiation_consumption after an accepted initiation: now if now is later (s64 difference), else unchanged
static u64 m_last_consumption(u64 last, u64 now)
{
	return (s64)(last - now) < 0 ? now : last;
}

// ANY mutable handshake state (the fields the handshake functions write): one of the five states, any ephemeral
// and remote ephemeral keys, hash, chaining key, latest timestamp, remote index, and a last consumption time on
// the boot clock
static void hs_randomize(struct noise_handshake *h)
{
	h->state = draw_hs_state();
	nondet_bytes(h->ephemeral_private, 32);
	nondet_bytes(h->remote_ephemeral, 32);
	nondet_bytes(h->hash, 32);
	nondet_bytes(h->chaining_key, 32);
	nondet_bytes(h->latest_timestamp, 12);
	h->remote_index = nondet_u32();
	h->last_initiation_consumption = draw_boottime();
}

// A peer's reference count before a call: 1, 2, INT_MAX - 1 = REFCOUNT_MAX (the largest below INT_MAX) or ANY count
// from 1 to INT_MAX - 1.  With the shim's refcount_t (quickproof_kref.h S04) a get on a count
// below INT_MAX never saturates, so a call that takes and drops peer references leaves the count as it found it and
// raises no refcount warning (shim_same).  A peer at INT_MAX references (2^31 - 1 holders) is excluded (L03):
// there the kernel's get saturates and leaks the peer; law keypairs covers saturation for the keypairs' counts.
#define M_REFCOUNT_MAX 0x7fffffffu
static unsigned int draw_peer_refs(void)
{
	switch (nondet_u8() % 4) {
	case 0:
		return 1 + (nondet_u32() % (M_REFCOUNT_MAX - 1));   // 1 .. INT_MAX - 1
	case 1:
		return M_REFCOUNT_MAX - 1;
	default:
		return 1 + (nondet_u8() & 1);
	}
}

// The harness's list of peers of a device, with a snapshot of each.  Peer references: draw_peer_refs (a peer in the
// device's tables is never at 0 references: peer.c removes it from both tables and clears it before its last
// reference is dropped).
struct hnode {
	struct wg_peer *p;
	struct hs_snap snap;
	unsigned int refs;
	struct pr_snap rest;   // the rest of the peer
	struct hnode *next;
};

static void hnodes_snap(struct hnode *l)
{
	for (; l; l = l->next) {
		hs_take(&l->snap, &l->p->handshake);
		l->refs = l->p->refcount.refcount;
		pr_take(&l->rest, l->p);
	}
}

// every peer but `except` is unchanged since the snapshot: its handshake, its reference count and
// the rest of it (pr_same: cookie state, keypair slots, last sent handshake, dead flag, ...), i.e. the whole peer
static int hnodes_same_except(const struct hnode *l, const struct wg_peer *except)
{
	for (; l; l = l->next)
		if (l->p != except && (!hs_same(&l->snap, &l->p->handshake) || l->p->refcount.refcount != l->refs ||
				       !pr_same(&l->rest, l->p)))
			return 0;
	return 1;
}

static void hnodes_free(struct hnode *l)
{
	struct hnode *n;
	while (l) {
		n = l->next;
		free(l->p);
		free(l);
		l = n;
	}
}

// Add a peer with public key `pub` (and any preshared key or none) to the device and the list, unless a peer
// with that key exists (the device keeps public keys unique: wg_peer_create is refused for a known key).
// Returns the node, or NULL (duplicate key or no memory).
static struct hnode *hnodes_add(struct hnode **l, struct wg_device *wg, const u8 pub[32], u64 id)
{
	struct hnode *n, *it;
	u8 psk[32];
	for (it = *l; it; it = it->next)
		if (bytes_eq(it->p->handshake.remote_static, pub, 32))
			return NULL;
	n = malloc(sizeof(*n));
	if (n == NULL)
		return NULL;
	n->p = malloc(sizeof(*n->p));
	if (n->p == NULL) {
		free(n);
		return NULL;
	}
	nondet_bytes(psk, 32);
	setup_peer(n->p, wg, pub, (nondet_u8() & 1) ? psk : NULL, id);
	n->p->refcount.refcount = draw_peer_refs();
	n->next = *l;
	*l = n;
	return n;
}

// ---------------------------------------------------------------------------------------------------------------
// Whole-state frame conditions.  A law states what a call writes; with these snapshots it also states
// that NOTHING ELSE changes: the whole of every peer (hnode: handshake, reference count, pr_snap), the device
// (dev_snap: identity, cookie checker, tables), every entry of the index table (kent and the peers' handshake
// entries) and the shim's allocation counters (shim_snap).
// ---------------------------------------------------------------------------------------------------------------

// ANY mutable state of a peer outside its handshake: the dead flag, the time of the last sent handshake and the
// cookie state (valid or not, birthdate, cookie, whether a mac1 was sent and which).  The keypair slots stay empty
// (no keypair objects here; law keypairs covers them) and the cookie keys stay the precomputed ones (configuration).
static void peer_randomize_rest(struct wg_peer *p)
{
	p->is_dead = nondet_u8() & 1;
	p->last_sent_handshake.counter = (s64)draw_u64();
	p->latest_cookie.is_valid = nondet_u8() & 1;
	p->latest_cookie.birthdate = draw_boottime();
	nondet_bytes(p->latest_cookie.cookie, 16);
	p->latest_cookie.have_sent_mac1 = nondet_u8() & 1;
	nondet_bytes(p->latest_cookie.last_mac1_sent, 16);
}

// any node of a non-empty list
static struct hnode *hnodes_pick(struct hnode *l)
{
	size_t k = nondet_size();
	while (k > 0 && l->next != NULL) {
		l = l->next;
		k--;
	}
	return l;
}

// Snapshot of a device: its identity, its cookie checker, its tables (the pointers and the public-key table's first
// peer; the index table's entries are checked one by one, kent / hnode)
struct dev_snap {
	struct net_device *dev;
	u8 static_public[32];
	u8 static_private[32];
	bool has_identity;
	u8 secret[32];
	u64 secret_birthdate;
	u8 cookie_encryption_key[32];
	u8 message_mac1_key[32];
	struct wg_device *checker_device;
	struct pubkey_hashtable *peer_hashtable;
	struct index_hashtable *index_hashtable;
	struct wg_peer *peers_head;
};

static void dev_take(struct dev_snap *s, const struct wg_device *wg)
{
	s->dev = wg->dev;
	bytes_copy(s->static_public, wg->static_identity.static_public, 32);
	bytes_copy(s->static_private, wg->static_identity.static_private, 32);
	s->has_identity = wg->static_identity.has_identity;
	bytes_copy(s->secret, wg->cookie_checker.secret, 32);
	s->secret_birthdate = wg->cookie_checker.secret_birthdate;
	bytes_copy(s->cookie_encryption_key, wg->cookie_checker.cookie_encryption_key, 32);
	bytes_copy(s->message_mac1_key, wg->cookie_checker.message_mac1_key, 32);
	s->checker_device = wg->cookie_checker.device;
	s->peer_hashtable = wg->peer_hashtable;
	s->index_hashtable = wg->index_hashtable;
	s->peers_head = wg->peer_hashtable->head;
}

// the device is as in the snapshot (a law that expects a change, e.g. the cookie secret's rotation, writes the
// expected value into the snapshot first)
static int dev_same(const struct dev_snap *s, const struct wg_device *wg)
{
	return s->dev == wg->dev && bytes_eq(s->static_public, wg->static_identity.static_public, 32) &&
	       bytes_eq(s->static_private, wg->static_identity.static_private, 32) &&
	       s->has_identity == wg->static_identity.has_identity &&
	       bytes_eq(s->secret, wg->cookie_checker.secret, 32) &&
	       s->secret_birthdate == wg->cookie_checker.secret_birthdate &&
	       bytes_eq(s->cookie_encryption_key, wg->cookie_checker.cookie_encryption_key, 32) &&
	       bytes_eq(s->message_mac1_key, wg->cookie_checker.message_mac1_key, 32) &&
	       s->checker_device == wg->cookie_checker.device && s->peer_hashtable == wg->peer_hashtable &&
	       s->index_hashtable == wg->index_hashtable && s->peers_head == wg->peer_hashtable->head;
}

// the shim's allocation and peer-release counters and its refcount_t warnings (quickproof_kernel.h S04: the kernel's
// refcount_warn_saturate, by type): a call that must not create (or destroy) state leaves the counters as they were,
// and no call of any law ever triggers a refcount_t warning (no increment from 0, no underflow, no saturation: the
// peers hold fewer than INT_MAX references, draw_peer_refs)
struct shim_snap {
	unsigned long allocs;
	unsigned long alloc_failures;
	unsigned long frees;
	unsigned long peer_released;
	unsigned long refcount_warn[5];
};

static void shim_take(struct shim_snap *s)
{
	int i;
	s->allocs = wg_shim_allocs;
	s->alloc_failures = wg_shim_alloc_failures;
	s->frees = wg_shim_frees;
	s->peer_released = wg_shim_peer_released;
	for (i = 0; i < 5; i++)
		s->refcount_warn[i] = wg_shim_refcount_warn[i];
}

// no refcount_t warning since the snapshot
static int shim_no_warning(const struct shim_snap *s)
{
	int i;
	for (i = 0; i < 5; i++)
		if (s->refcount_warn[i] != wg_shim_refcount_warn[i])
			return 0;
	return 1;
}

static int shim_same(const struct shim_snap *s)
{
	return s->allocs == wg_shim_allocs && s->alloc_failures == wg_shim_alloc_failures &&
	       s->frees == wg_shim_frees && s->peer_released == wg_shim_peer_released && shim_no_warning(s);
}

// Keypairs that a law adds besides the peers' handshakes: whole struct noise_keypair objects with ANY
// content (keys, validity, birthdates, sending counter, replay window, remote index, role, reference count below
// INT_MAX, internal id), each of ANY peer, in the index table; with kents_add(.., fill = 1) each may also sit in an
// empty keypair slot (current, previous or next) of its peer.  A snapshot of every field (kents_same: all of it;
// kents_same_but_next: all but the entry's list link).  For the laws whose calls never rotate keypairs (fill = 1):
// these objects are then the peers' current / previous / next keypairs, and the laws claim that the call leaves
// every byte of them as it was.
#define KENT_BT (COUNTER_BITS_TOTAL / BITS_PER_LONG)
struct kent {
	struct noise_keypair kp;
	struct wg_peer *peer0;
	struct index_hashtable_entry *next0;
	enum index_hashtable_type type0;
	__le32 index0;
	bool hashed0;
	u8 skey0[32];
	u8 rkey0[32];
	u64 sbirth0;
	u64 rbirth0;
	bool svalid0;
	bool rvalid0;
	s64 scnt0;
	u64 rcnt0;
	unsigned long bt0[KENT_BT];
	__le32 remote_index0;
	bool initiator0;
	unsigned int refs0;
	u64 id0;
	struct kent *next;
};

// ANY number of keypairs, each of ANY peer of `peers` (or of `p` if the list is empty; none if both are empty),
// inserted into the table; with fill, each one possibly in an empty slot of its peer
static struct kent *kents_add(struct index_hashtable *t, struct hnode *peers, struct wg_peer *p, int fill)
{
	struct kent *l = NULL, *k;
	size_t n = (peers != NULL || p != NULL) ? draw_steps() : 0, i, j;
	for (i = 0; i < n; i++) {
		struct wg_peer *owner;
		struct noise_keypair *kp;
		k = malloc(sizeof(*k));
		if (k == NULL)
			break;
		kp = &k->kp;
		owner = peers != NULL ? hnodes_pick(peers)->p : p;
		kp->entry.peer = owner;
		kp->entry.type = INDEX_HASHTABLE_KEYPAIR;
		kp->entry.next = NULL;
		kp->entry.hashed = false;
		wg_index_hashtable_insert(t, &kp->entry);
		nondet_bytes(kp->sending.key, 32);
		kp->sending.birthdate = draw_boottime();
		kp->sending.is_valid = nondet_u8() & 1;
		nondet_bytes(kp->receiving.key, 32);
		kp->receiving.birthdate = draw_boottime();
		kp->receiving.is_valid = nondet_u8() & 1;
		kp->sending_counter.counter = (s64)draw_u64();
		kp->receiving_counter.counter = draw_u64();
		for (j = 0; j < KENT_BT; j++)
			kp->receiving_counter.backtrack[j] = (unsigned long)draw_u64();
		kp->remote_index = nondet_u32();
		kp->i_am_the_initiator = nondet_u8() & 1;
		kp->refcount.refcount = draw_peer_refs();
		kp->internal_id = draw_u64();
		if (fill) {
			switch (nondet_u8() % 4) {
			case 0:
				if (owner->keypairs.current_keypair == NULL)
					owner->keypairs.current_keypair = kp;
				break;
			case 1:
				if (owner->keypairs.previous_keypair == NULL)
					owner->keypairs.previous_keypair = kp;
				break;
			case 2:
				if (owner->keypairs.next_keypair == NULL)
					owner->keypairs.next_keypair = kp;
				break;
			default:
				break;
			}
		}
		k->next = l;
		l = k;
	}
	return l;
}

static void kents_snap(struct kent *l)
{
	size_t j;
	for (; l; l = l->next) {
		const struct noise_keypair *kp = &l->kp;
		l->peer0 = kp->entry.peer;
		l->next0 = kp->entry.next;
		l->type0 = kp->entry.type;
		l->index0 = kp->entry.index;
		l->hashed0 = kp->entry.hashed;
		bytes_copy(l->skey0, kp->sending.key, 32);
		bytes_copy(l->rkey0, kp->receiving.key, 32);
		l->sbirth0 = kp->sending.birthdate;
		l->rbirth0 = kp->receiving.birthdate;
		l->svalid0 = kp->sending.is_valid;
		l->rvalid0 = kp->receiving.is_valid;
		l->scnt0 = kp->sending_counter.counter;
		l->rcnt0 = kp->receiving_counter.counter;
		for (j = 0; j < KENT_BT; j++)
			l->bt0[j] = kp->receiving_counter.backtrack[j];
		l->remote_index0 = kp->remote_index;
		l->initiator0 = kp->i_am_the_initiator;
		l->refs0 = kp->refcount.refcount;
		l->id0 = kp->internal_id;
	}
}

// every field of the keypair but its entry's list link is as in the snapshot
static int kent_same_but_next(const struct kent *l)
{
	const struct noise_keypair *kp = &l->kp;
	size_t j;
	if (kp->entry.peer != l->peer0 || kp->entry.type != l->type0 || kp->entry.index != l->index0 ||
	    kp->entry.hashed != l->hashed0 || !bytes_eq(kp->sending.key, l->skey0, 32) ||
	    !bytes_eq(kp->receiving.key, l->rkey0, 32) || kp->sending.birthdate != l->sbirth0 ||
	    kp->receiving.birthdate != l->rbirth0 || kp->sending.is_valid != l->svalid0 ||
	    kp->receiving.is_valid != l->rvalid0 || kp->sending_counter.counter != l->scnt0 ||
	    kp->receiving_counter.counter != l->rcnt0 || kp->remote_index != l->remote_index0 ||
	    kp->i_am_the_initiator != l->initiator0 || kp->refcount.refcount != l->refs0 || kp->internal_id != l->id0)
		return 0;
	for (j = 0; j < KENT_BT; j++)
		if (kp->receiving_counter.backtrack[j] != l->bt0[j])
			return 0;
	return 1;
}

// every keypair unchanged, its entry's list link included
static int kents_same(const struct kent *l)
{
	for (; l; l = l->next)
		if (!kent_same_but_next(l) || l->kp.entry.next != l->next0)
			return 0;
	return 1;
}

// every keypair unchanged but its entry's list link (an entry before it may have left the table), and in the table
// exactly once if it was hashed
static int kents_same_but_next(const struct kent *l, const struct index_hashtable *t)
{
	for (; l; l = l->next)
		if (!kent_same_but_next(l) || (l->hashed0 && !table_has(t, &l->kp.entry)))
			return 0;
	return 1;
}

static size_t kents_hashed(const struct kent *l)
{
	size_t n = 0;
	for (; l; l = l->next)
		if (l->kp.entry.hashed)
			n++;
	return n;
}

static void kents_free(struct kent *l)
{
	struct kent *n;
	while (l) {
		n = l->next;
		free(l);
		l = n;
	}
}

// hs_same but the entry's list link
static int hs_same_but_next(const struct hs_snap *s, const struct noise_handshake *h)
{
	return s->peer == h->entry.peer && s->hashed == h->entry.hashed &&
	       s->type == h->entry.type && s->index == h->entry.index && s->state == h->state &&
	       s->last_initiation_consumption == h->last_initiation_consumption &&
	       s->static_identity == h->static_identity &&
	       bytes_eq(s->ephemeral_private, h->ephemeral_private, 32) &&
	       bytes_eq(s->remote_static, h->remote_static, 32) &&
	       bytes_eq(s->remote_ephemeral, h->remote_ephemeral, 32) &&
	       bytes_eq(s->precomputed_static_static, h->precomputed_static_static, 32) &&
	       bytes_eq(s->preshared_key, h->preshared_key, 32) && bytes_eq(s->hash, h->hash, 32) &&
	       bytes_eq(s->chaining_key, h->chaining_key, 32) &&
	       bytes_eq(s->latest_timestamp, h->latest_timestamp, 12) && s->remote_index == h->remote_index;
}

// Snapshot of a socket buffer as cookie.c reads it
struct skb_snap {
	u8 *data;
	unsigned int len;
	__be16 protocol;
	u8 saddr4[4];
	u8 saddr6[16];
	u8 sport[2];
};

static void skb_take(struct skb_snap *s, const struct sk_buff *skb)
{
	s->data = skb->data;
	s->len = skb->len;
	s->protocol = skb->protocol;
	bytes_copy(s->saddr4, skb->ip4.saddr.s_addr, 4);
	bytes_copy(s->saddr6, skb->ip6.saddr.s6_addr, 16);
	bytes_copy(s->sport, skb->udp.source, 2);
}

static int skb_same(const struct skb_snap *s, const struct sk_buff *skb)
{
	return s->data == skb->data && s->len == skb->len && s->protocol == skb->protocol &&
	       bytes_eq(s->saddr4, skb->ip4.saddr.s_addr, 4) && bytes_eq(s->saddr6, skb->ip6.saddr.s6_addr, 16) &&
	       bytes_eq(s->sport, skb->udp.source, 2);
}

// a fresh replay window (keypair_create's kzalloc): counter 0 and an empty bitmap
static int replay_counter_fresh(const struct noise_replay_counter *c)
{
	size_t i;
	if (c->counter != 0)
		return 0;
	for (i = 0; i < COUNTER_BITS_TOTAL / BITS_PER_LONG; i++)
		if (c->backtrack[i] != 0)
			return 0;
	return 1;
}

#endif /* WG_HARNESS_COMMON_H */
