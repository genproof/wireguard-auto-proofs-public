// SPDX-License-Identifier: GPL-2.0
// patch/shimtest/shimtest.c: differential test of the shim against upstream kernel code (DEVIATIONS.md S*).
// Native only, not verified.  Built twice by shimtest.sh:
//   -DUPSTREAM: the lookup tables of upstream drivers/net/wireguard/peerlookup.c (with the list primitives of
//               env/), upstream lib/crypto/utils.c (__crypto_xor) and memneq.c (__crypto_memneq), and the
//               kernel's byte-order helpers as gcc builtins;
//   default:    the same API over the shim (patch/wg_shim.c, patch/include).
// Both run the same pseudo-random operation sequences and print one output hash per section.
#include "quickproof_kernel.h"
#include <crypto/utils.h>
#include "shimtest.h"
#include <stdio.h>
#include <stdlib.h>

static uint64_t rs, rs2;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
uint8_t nondet_u8(void) { return (uint8_t)rnd64(); }
uint32_t nondet_u32(void) { return rnd64() % 4 == 0 ? (uint32_t)(rnd64() % 16) : (uint32_t)rnd64(); }
size_t nondet_size(void) { return rnd64() % 64; }
void nondet_bytes(uint8_t *b, size_t n) { for (size_t i = 0; i < n; i++) b[i] = (uint8_t)rnd64(); }
#ifdef UPSTREAM
u32 get_random_u32(void) { return nondet_u32(); }
void get_random_bytes(void *b, size_t n)   /* the table's siphash key: a separate stream */
{
	for (size_t i = 0; i < n; i++) {
		rs2 = rs2 * 6364136223846793005ULL + 1;
		((u8 *)b)[i] = (u8)(rs2 >> 56);
	}
}
#endif

static uint64_t th[4], tn[4];
static int sec;
static void t(u64 v) { th[sec] = (th[sec] ^ v) * 0x100000001b3ULL; tn[sec]++; }

static void tables(void)
{
	u8 keys[NPEER][32];
	int i, steps = 1 + rnd64() % 60;
	t_init();
	for (i = 0; i < NPEER; i++) {
		nondet_bytes(keys[i], 32);
		if (i > 0 && rnd64() % 6 == 0)
			memcpy(keys[i], keys[rnd64() % i], 32);   /* duplicate keys: the order of the lists decides */
		t_peer_key(i, keys[i]);
		t_peer_ref(i, (unsigned)(rnd64() % 8 == 0 ? 0 : 1 + rnd64() % 2));
		if (rnd64() % 4 != 0)
			t_padd(i);
	}
	for (i = 0; i < NENT; i++)
		t_entry(i, (int)(rnd64() % NPEER), rnd64() % 2 ? 1 : 2);
	for (i = 0; i < steps; i++) {
		int e = (int)(rnd64() % NENT), p;
		switch (rnd64() % 5) {
		case 0: t(t_insert(e)); break;
		case 1: {
			int n = (int)(rnd64() % NENT);
			if (n != e && !t_hashed(n))   /* the kernel replaces with a fresh (unhashed) keypair entry */
				t(t_replace(e, n));
			break;
		}
		case 2: t_remove(e); break;
		case 3: {
			u32 idx = rnd64() % 2 ? t_index((int)(rnd64() % NENT)) : nondet_u32();
			t((u64)(t_lookup(idx, 1 + (int)(rnd64() % 3), &p) + 1));
			t((u64)(p + 1));
			break;
		}
		default: {
			u8 k[32];
			if (rnd64() % 4)
				memcpy(k, keys[rnd64() % NPEER], 32);
			else
				nondet_bytes(k, 32);
			t((u64)(t_plookup(k) + 1));
			break;
		}
		}
		for (int j = 0; j < NENT; j++) {
			t(t_hashed(j));
			t(t_index(j));
			t((u64)(t_entry_peer(j) + 1));
		}
		for (int j = 0; j < NPEER; j++)
			t(t_peer_refs(j));
	}
}

static void utils(void)
{
	u8 a[80], b[80], d[80];
	size_t n = rnd64() % 80, off = rnd64() % 8;
	nondet_bytes(a, 80);
	memcpy(b, a, 80);
	if (rnd64() % 2)
		b[rnd64() % 80] ^= (u8)(1 + rnd64() % 255);
	t(crypto_memneq(a + off, b + off, n - (n > off ? off : n)));
	memset(d, 0, 80);
	crypto_xor_cpy(d + off, a + off, b + off, (unsigned)(n - (n > off ? off : n)));
	for (int i = 0; i < 80; i++)
		t(d[i]);
	crypto_xor(a + off, b, (unsigned)(n - (n > off ? off : n)));
	for (int i = 0; i < 80; i++)
		t(a[i]);
}

static void bytes_order(void)
{
	u8 buf[16];
	u64 v = rnd64();
	nondet_bytes(buf, 16);
#ifdef UPSTREAM
	/* the kernel's helpers on x86_64: unaligned native loads/stores, bswap for big endian */
	u32 x; u64 y;
	memcpy(&x, buf + 1, 4); t(x);
	x = (u32)v; memcpy(buf + 3, &x, 4); t(buf[3] | buf[4] << 8 | buf[5] << 16 | (u64)buf[6] << 24);
	y = v; memcpy(buf + 5, &y, 8); for (int i = 0; i < 8; i++) t(buf[5 + i]);
	x = __builtin_bswap32((u32)v); memcpy(buf, &x, 4); for (int i = 0; i < 4; i++) t(buf[i]);
	y = __builtin_bswap64(v); memcpy(buf + 4, &y, 8); for (int i = 0; i < 8; i++) t(buf[4 + i]);
	t(__builtin_bswap16((u16)v));
	t((v & 1) ? (((u32)v << (v % 32)) | ((u32)v >> ((32 - v % 32) % 32))) : ((u32)v >> (v % 32)) | ((u32)v << ((32 - v % 32) % 32)));
	{   /* rounddown_pow_of_two and ilog2 on the constants the code uses */
		unsigned long c = 1000000000UL / 50;
		t(1UL << (63 - __builtin_clzl(c)));
		t(63 - __builtin_clzl(64));
		unsigned long m[2] = { 0, 0 }; unsigned nr = (unsigned)(v % 128);
		int old = (m[nr / 64] >> (nr % 64)) & 1; m[nr / 64] |= 1UL << (nr % 64); t(old); t(m[0]); t(m[1]);
		old = (m[nr / 64] >> (nr % 64)) & 1; t(old);
	}
#else
	t(get_unaligned_le32(buf + 1));
	put_unaligned_le32((u32)v, buf + 3); t(buf[3] | buf[4] << 8 | buf[5] << 16 | (u64)buf[6] << 24);
	put_unaligned_le64(v, buf + 5); for (int i = 0; i < 8; i++) t(buf[5 + i]);
	put_unaligned_be32((u32)v, buf); for (int i = 0; i < 4; i++) t(buf[i]);
	put_unaligned_be64(v, buf + 4); for (int i = 0; i < 8; i++) t(buf[4 + i]);
	t(htons((u16)v));
	t((v & 1) ? rol32((u32)v, v % 32) : ror32((u32)v, v % 32));
	{
		t(rounddown_pow_of_two(1000000000UL / 50));
		t(ilog2(64));
		unsigned long m[2] = { 0, 0 }; unsigned nr = (unsigned)(v % 128);
		t(test_and_set_bit(nr, m)); t(m[0]); t(m[1]);
		t(test_and_set_bit(nr, m));
	}
#endif
}

int main(int argc, char **argv)
{
	long iters = argc > 1 ? atol(argv[1]) : 10000;
	rs = 0x9E3779B97F4A7C15ULL ^ ((argc > 2 ? strtoull(argv[2], NULL, 0) : 1) * 0x2545F4914F6CDD1DULL);
	rs2 = 42;
	for (long i = 0; i < iters; i++) {
		sec = (int)(rnd64() % 3);
		if (sec == 0) tables();
		else if (sec == 1) utils();
		else bytes_order();
	}
	printf("tables      %10llu values  %016llx\nutils       %10llu values  %016llx\nbyte order  %10llu values  %016llx\n",
	       (unsigned long long)tn[0], (unsigned long long)th[0], (unsigned long long)tn[1], (unsigned long long)th[1],
	       (unsigned long long)tn[2], (unsigned long long)th[2]);
	return 0;
}
