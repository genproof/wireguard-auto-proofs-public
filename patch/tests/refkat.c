// SPDX-License-Identifier: GPL-2.0
// patch/tests/refkat.c: the harness's reference primitives (harness/common.h, ref_*) on published test vectors.
// Native only; run by patch/tests/refkat.sh.  The laws compare the kernel's primitives with these references on
// any input; this anchors the references themselves to the standards.
#include "../../harness/common.h"
#include <stdio.h>

uint8_t nondet_u8(void) { return 0; }
uint32_t nondet_u32(void) { return 0; }
size_t nondet_size(void) { return 0; }
void nondet_bytes(uint8_t *b, size_t n) { (void)b; (void)n; }

static int hex(u8 *out, const char *h)
{
	int n = 0;
	for (; h[0] && h[1]; h += 2) {
		unsigned v;
		sscanf(h, "%2x", &v);
		out[n++] = (u8)v;
	}
	return n;
}

static int fails;
static void expect(const char *what, const u8 *got, const char *want_hex)
{
	u8 want[128];
	int n = hex(want, want_hex);
	int ok = bytes_eq(got, want, (size_t)n);
	printf("%-44s %s\n", what, ok ? "ok" : "MISMATCH");
	fails += !ok;
}

int main(void)
{
	u8 a[64], b[64], out[64], key[32];
	u32 x[16], s[16];
	int i;

	// RFC 7748 5.2, first X25519 vector
	hex(a, "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
	hex(b, "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c");
	ref_x25519(out, a, b);
	expect("X25519 (RFC 7748 5.2)", out, "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552");

	// RFC 7693 appendix B: BLAKE2s-256("abc")
	ref_blake2s(out, 32, key, 0, (const u8 *)"abc", 3);
	expect("BLAKE2s-256(\"abc\") (RFC 7693 B)", out, "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982");

	// RFC 8439 2.3.2: ChaCha20 block, key 00..1f, counter 1, nonce 000000090000004a00000000
	for (i = 0; i < 32; i++)
		key[i] = (u8)i;
	rc_setup(s, key, 1, 0x09000000u, 0x4a000000u, 0);
	for (i = 0; i < 16; i++)
		x[i] = s[i];
	rc_rounds(x);
	for (i = 0; i < 16; i++)
		le32_store(out + 4 * i, x[i] + s[i]);
	expect("ChaCha20 block (RFC 8439 2.3.2)", out,
	       "10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e");

	// RFC 8439 2.5.2: Poly1305 of "Cryptographic Forum Research Group"
	hex(key, "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b");
	ref_poly1305(out, key, (const u8 *)"Cryptographic Forum Research Group", 34);
	expect("Poly1305 (RFC 8439 2.5.2)", out, "a8061dc1305136c6c22b8baf0c0127a9");
	printf("%s\n", fails ? "FAILED" : "all vectors ok");
	return fails != 0;
}
