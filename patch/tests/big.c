// SPDX-License-Identifier: GPL-2.0
// patch/tests/big.c: the failing range of the series P22/P23 (DEVIATIONS.md: "lib/crypto: poly1305: Take a size_t
// length in poly1305_update()", "lib/crypto: chacha: Take a size_t length in chacha_crypt()"), natively, against
// the reference primitives of harness/common.h (ref_poly1305, ref_aead_*, ref_xaead_*).  Run by
// patch/tests/big.sh on the unmodified upstream code (where the 4 GiB cases FAIL) and on this repository's code (where every case must give the RFC 8439 result).  The single size_t
// poly1305_update calls beyond 2^32 run the series' UINT_MAX loop (poly1305_blocks gets 2^32 - 16 bytes, then the
// rest).  Also single poly1305_update calls of 2 GiB and more below 2^32 (one poly1305_blocks call in the series),
// which upstream's generic C gets right.  Each case
// runs in a child process, so that a crash of the unmodified code (the wrap writes 4 GiB over a 16-byte buffer) is
// reported and the next case still runs.  The calls pass size_t lengths: against upstream's unsigned int
// parameters they are converted, as for any caller with a size_t.
// Needs about 17 GiB of memory (case aead_msg) and about an hour.
#include "../../harness/common.h"
#include <crypto/poly1305.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <unistd.h>

uint8_t nondet_u8(void) { return 0; }
uint32_t nondet_u32(void) { return 0; }
size_t nondet_size(void) { return 0; }
void nondet_bytes(uint8_t *b, size_t n) { (void)b; (void)n; }

#define G4 ((size_t)1 << 32)

static void fill(u8 *p, size_t n, u64 seed)
{
	u64 s = seed * 0x9E3779B97F4A7C15ULL + 1;
	size_t i;
	for (i = 0; i < n; i++) {
		if ((i & 7) == 0) {
			s ^= s << 13;
			s ^= s >> 7;
			s ^= s << 17;
		}
		p[i] = (u8)(s >> (8 * (i & 7)));
	}
}

static u8 *alloc(size_t n)
{
	u8 *p = malloc(n);
	if (p == NULL) {
		printf("  no memory for %zu bytes\n", n);
		exit(3);
	}
	return p;
}

// Poly1305 of a 2^32 + 20-byte message: the reference once, then the kernel's streaming API with splits whose
// second chunk wraps buflen + nbytes in upstream (buflen 1 and 15), splits that do not (one chunk of 2^32 - 1
// from an empty buffer, then the rest; chunks of 2^32 - 16), and (series P22: a size_t chunk) the whole message
// in ONE call, and 1 byte then the whole rest (2^32 + 19 bytes) in one call.
static int case_poly1305(void)
{
	static const struct { size_t first; size_t second; } splits[] = {
		{ 1, 0xffffffffu }, { 15, 0xfffffff1u }, { 15, 0xffffffffu }, { 7, 0xfffffffau },
		{ 0, 0xffffffffu }, { 16, 0xfffffff0u }, { 0, G4 + 20 }, { 1, G4 + 19 },
	};
	const size_t n = G4 + 20;
	u8 *m = alloc(n), key[32], ref[16], tag[16];
	unsigned int i;
	int bad = 0;
	fill(m, n, 1);
	fill(key, 32, 2);
	ref_poly1305(ref, key, m, n);
	for (i = 0; i < sizeof(splits) / sizeof(splits[0]); i++) {
		pid_t pid = fork();
		if (pid == 0) {
			struct poly1305_desc_ctx d;
			size_t pos;
			poly1305_init(&d, key);
			poly1305_update(&d, m, splits[i].first);
			poly1305_update(&d, m + splits[i].first, splits[i].second);
			pos = splits[i].first + splits[i].second;
			poly1305_update(&d, m + pos, n - pos);
			poly1305_final(&d, tag);
			_exit(bytes_eq(tag, ref, 16) ? 0 : 1);
		}
		int st;
		waitpid(pid, &st, 0);
		printf("  poly1305 n = 2^32 + 20, chunks %zu, %zu, %zu: %s\n", splits[i].first, splits[i].second,
		       n - splits[i].first - splits[i].second,
		       WIFSIGNALED(st) ? "CRASHED" : WEXITSTATUS(st) == 0 ? "= RFC 8439 tag" : "WRONG TAG");
		bad |= !(WIFEXITED(st) && WEXITSTATUS(st) == 0);
	}
	free(m);
	return bad;
}

// Single poly1305_update calls of 2 GiB and more below 2^32 (in the series one poly1305_blocks call of up to
// 2^32 - 16 bytes): a 2^31 + 37-byte message
// after 0, 5 or 15 buffered bytes, and in exactly 2^31 bytes then the rest.  Upstream's generic C is correct here
// (no wrap, below 2^32); the series must be too.
static int case_poly1305_2g(void)
{
	static const struct { size_t first; size_t second; } splits[] = {
		{ 0, ((size_t)1 << 31) + 37 }, { 5, ((size_t)1 << 31) + 32 }, { 15, ((size_t)1 << 31) + 22 },
		{ 0, (size_t)1 << 31 },
	};
	const size_t n = ((size_t)1 << 31) + 37;
	u8 *m = alloc(n), key[32], ref[16], tag[16];
	unsigned int i;
	int bad = 0;
	fill(m, n, 7);
	fill(key, 32, 8);
	ref_poly1305(ref, key, m, n);
	for (i = 0; i < sizeof(splits) / sizeof(splits[0]); i++) {
		pid_t pid = fork();
		if (pid == 0) {
			struct poly1305_desc_ctx d;
			size_t pos;
			poly1305_init(&d, key);
			poly1305_update(&d, m, splits[i].first);
			poly1305_update(&d, m + splits[i].first, splits[i].second);
			pos = splits[i].first + splits[i].second;
			poly1305_update(&d, m + pos, n - pos);
			poly1305_final(&d, tag);
			_exit(bytes_eq(tag, ref, 16) ? 0 : 1);
		}
		int st;
		waitpid(pid, &st, 0);
		printf("  poly1305 n = 2^31 + 37, chunks %zu, %zu, %zu: %s\n", splits[i].first, splits[i].second,
		       n - splits[i].first - splits[i].second,
		       WIFSIGNALED(st) ? "CRASHED" : WEXITSTATUS(st) == 0 ? "= RFC 8439 tag" : "WRONG TAG");
		bad |= !(WIFEXITED(st) && WEXITSTATUS(st) == 0);
	}
	free(m);
	return bad;
}

// One AEAD case: kernel encrypt = reference encrypt (all n + 16 bytes), decrypt of it gives the message back,
// decrypt after one changed byte at `flip` (in the ciphertext, or in the associated data if flip_ad) is rejected
// and leaves the output buffer unchanged.
static int case_aead(const char *what, int x, size_t adlen, size_t n, size_t flip, int flip_ad)
{
	u8 key[32], xn[24];
	u64 nonce = 0x0123456789abcdefULL;
	u8 *ad = alloc(adlen), *pt = alloc(n), *ct = alloc(n + 16), *rct = alloc(n + 16), *dec = alloc(n);
	int enc_ok, dec_ok, tamper_rejected, untouched, ok;
	fill(key, 32, 3);
	fill(xn, 24, 4);
	fill(ad, adlen, 5);
	fill(pt, n, 6);
	if (x) {
		xchacha20poly1305_encrypt(ct, pt, n, ad, adlen, xn, key);
		ref_xaead_encrypt(rct, pt, n, ad, adlen, xn, key);
	} else {
		chacha20poly1305_encrypt(ct, pt, n, ad, adlen, nonce, key);
		ref_aead_encrypt(rct, pt, n, ad, adlen, nonce, key);
	}
	enc_ok = bytes_eq(ct, rct, n + 16);
	free(rct);
	ok = x ? xchacha20poly1305_decrypt(dec, ct, n + 16, ad, adlen, xn, key)
	       : chacha20poly1305_decrypt(dec, ct, n + 16, ad, adlen, nonce, key);
	dec_ok = ok && bytes_eq(dec, pt, n);
	if (flip_ad)
		ad[flip] ^= 0x80;
	else
		ct[flip] ^= 0x80;
	memset(dec, 0x5a, n);
	ok = x ? xchacha20poly1305_decrypt(dec, ct, n + 16, ad, adlen, xn, key)
	       : chacha20poly1305_decrypt(dec, ct, n + 16, ad, adlen, nonce, key);
	tamper_rejected = !ok;
	untouched = 1;
	{
		size_t i;
		for (i = 0; i < n; i++)
			if (dec[i] != 0x5a) {
				untouched = 0;
				break;
			}
	}
	printf("  %s: encrypt %s; decrypt %s; byte %zu of the %s changed: %s%s\n", what,
	       enc_ok ? "= RFC 8439" : "DIFFERS FROM RFC 8439", dec_ok ? "round trip ok" : "ROUND TRIP FAILS",
	       flip, flip_ad ? "associated data" : "ciphertext", tamper_rejected ? "rejected" : "ACCEPTED",
	       tamper_rejected ? (untouched ? ", output untouched" : ", OUTPUT WRITTEN") : "");
	free(ad); free(pt); free(ct); free(dec);
	return !(enc_ok && dec_ok && tamper_rejected && untouched);
}

static int in_child(int (*f)(void))
{
	pid_t pid = fork();
	int st;
	if (pid == 0)
		_exit(f());
	waitpid(pid, &st, 0);
	if (WIFSIGNALED(st))
		printf("  CRASHED (signal %d)\n", WTERMSIG(st));
	return !(WIFEXITED(st) && WEXITSTATUS(st) == 0);
}

static int aead_msg(void) { return case_aead("chacha20poly1305, ad 33 bytes, message 2^32 + 100 bytes", 0, 33, G4 + 100, ((size_t)1 << 31) + 5, 0); }
static int xaead_msg(void) { return case_aead("xchacha20poly1305, ad 0 bytes, message 2^32 + 64 bytes", 1, 0, G4 + 64, G4 + 10, 0); }
static int aead_ad(void) { return case_aead("chacha20poly1305, ad 2^32 + 7 bytes, message 50 bytes", 0, G4 + 7, 50, ((size_t)1 << 31) + 3, 1); }
static int xaead_ad(void) { return case_aead("xchacha20poly1305, ad 2^32 + 7 bytes, message 50 bytes", 1, G4 + 7, 50, G4 + 3, 1); }
static int aead_edge(void) { return case_aead("chacha20poly1305, ad 0, message 2^32 - 1 bytes (below the range: one chacha_crypt call, as upstream)", 0, 0, G4 - 1, 12345, 0); }
static int aead_edge2(void) { return case_aead("chacha20poly1305, ad 0, message 2^32 bytes (the first length chacha_crypt splits: 2^32 - 64 + 64)", 0, 0, G4, G4 - 3, 0); }

int main(int argc, char **argv)
{
	int bad = 0;
	const char *which = argc > 1 ? argv[1] : "all";
	setvbuf(stdout, NULL, _IONBF, 0);
	if (!strcmp(which, "all") || !strcmp(which, "poly1305")) {
		printf("P22 poly1305_update, 2^32 + 20 bytes:\n");
		bad |= in_child(case_poly1305);
		printf("P22 poly1305_update, single updates of 2 GiB and more:\n");
		bad |= in_child(case_poly1305_2g);
	}
	if (!strcmp(which, "all") || !strcmp(which, "aead")) {
		printf("P23 (and P22) AEAD:\n");
		bad |= in_child(aead_msg);
		bad |= in_child(xaead_msg);
		bad |= in_child(aead_ad);
		bad |= in_child(xaead_ad);
		bad |= in_child(aead_edge);
		bad |= in_child(aead_edge2);
	}
	printf("%s\n", bad ? "SOME CASES FAIL" : "all cases = RFC 8439");
	return bad;
}
