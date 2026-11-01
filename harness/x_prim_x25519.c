// SPDX-License-Identifier: GPL-2.0
// Law `prim_x25519`: the kernel's Curve25519 (lib/crypto/curve25519-fiat32.c, curve25519.c) is X25519 (RFC 7748,
// the TweetNaCl reference ref_x25519 of common.h).
//
// For ANY 32-byte scalar and ANY 32-byte point (non-canonical and low-order points included):
//  - curve25519_generic writes exactly the reference result;
//  - curve25519() writes the same and returns true iff it is not all zero;
//  - curve25519_generate_public() returns false without writing if the secret is all zero, else writes
//    X25519(secret, 9) (the reference) and returns true iff that is not all zero;
//  - inputs are not modified.
#include "common.h"

int main(void)
{
	u8 s[32], p[32], s0[32], p0[32], ref[32], base[32];
	u8 *out;
	bool r;
	int i;

	out = malloc(32);
	if (out == NULL)
		return 0;
	nondet_bytes(s, 32);
	nondet_bytes(p, 32);
	bytes_copy(s0, s, 32);
	bytes_copy(p0, p, 32);
	for (i = 0; i < 32; i++)
		base[i] = i == 0 ? 9 : 0;

	ref_x25519(ref, s, p);
	curve25519_generic(out, s, p);
	CHECK(bytes_eq(out, ref, 32));
	nondet_bytes(out, 32);
	r = curve25519(out, s, p);
	CHECK(bytes_eq(out, ref, 32) && r == !bytes_zero(ref, 32));

	nondet_bytes(out, 32);
	bytes_copy(ref, out, 32);
	r = curve25519_generate_public(out, s);
	if (bytes_zero(s, 32)) {
		CHECK(!r && bytes_eq(out, ref, 32));
	} else {
		ref_x25519(ref, s, base);
		CHECK(bytes_eq(out, ref, 32) && r == !bytes_zero(ref, 32));
	}
	CHECK(bytes_eq(s, s0, 32) && bytes_eq(p, p0, 32));
	free(out);
	return 0;
}
