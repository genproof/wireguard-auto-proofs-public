// patch/tests/refcount_check.c: driver of refcount_check.sh (QUICKPROOF S04).  The shim's refcount_t operations
// against the kernel's text (k_*, compiled from include/linux/refcount.h and lib/refcount.c by the script).
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern unsigned long wg_shim_refcount_warn[5], kernel_warn[5];
bool wg_shim_refcount_inc_not_zero(unsigned int *r);
void wg_shim_refcount_inc(unsigned int *r);
bool wg_shim_refcount_dec_and_test(unsigned int *r);
bool k_inc_not_zero(unsigned int *v);
void k_inc(unsigned int *v);
bool k_dec_and_test(unsigned int *v);

// wg_shim.c's environment (not used by the refcount functions)
void nondet_bytes(uint8_t *b, size_t n) { memset(b, 0, n); }
uint32_t nondet_u32(void) { return 0; }

static uint64_t s = 88172645463325252ull;
static uint64_t rnd(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }
static unsigned long checks, bad;

// one operation on both, from the same count; 1 if they agree
static int one(int op, unsigned int *ks, unsigned int *ss)
{
	bool kb = false, sb = false;
	switch (op) {
	case 0: kb = k_inc_not_zero(ks); sb = wg_shim_refcount_inc_not_zero(ss); break;
	case 1: k_inc(ks); wg_shim_refcount_inc(ss); break;
	default: kb = k_dec_and_test(ks); sb = wg_shim_refcount_dec_and_test(ss); break;
	}
	checks++;
	return kb == sb && *ks == *ss && !memcmp(kernel_warn, wg_shim_refcount_warn, sizeof(kernel_warn));
}

int main(void)
{
	static const char *name[3] = { "inc_not_zero", "inc", "dec_and_test" };
	unsigned int starts[64];
	size_t n = 0, i;
	int op;
	unsigned long r;
	for (i = 0; i <= 3; i++)
		starts[n++] = (unsigned int)i;
	for (i = 0; i <= 6; i++)
		starts[n++] = 0x7fffffffu - 3 + (unsigned int)i;     // INT_MAX - 3 .. INT_MAX + 3 (INT_MIN + 2)
	for (i = 0; i <= 6; i++)
		starts[n++] = 0xc0000000u - 3 + (unsigned int)i;     // REFCOUNT_SATURATED +- 3
	for (i = 0; i <= 3; i++)
		starts[n++] = 0xffffffffu - (unsigned int)i;        // -1 .. -4
	for (i = 0; i < 16; i++)
		starts[n++] = (unsigned int)rnd();
	for (op = 0; op < 3; op++)
		for (i = 0; i < n; i++) {
			unsigned int ks = starts[i], ss = starts[i];
			if (!one(op, &ks, &ss)) {
				bad++;
				printf("DIFFER: %s from 0x%08x: kernel 0x%08x, shim 0x%08x\n", name[op], starts[i], ks, ss);
			}
		}
	// random sequences from edge and random starts
	for (r = 0; r < 1000000; r++) {
		unsigned int ks = rnd() % 2 ? starts[rnd() % n] : (unsigned int)rnd(), ss = ks;
		int k, len = 1 + (int)(rnd() % 8);
		for (k = 0; k < len; k++)
			if (!one((int)(rnd() % 3), &ks, &ss)) {
				bad++;
				break;
			}
	}
	printf("refcount_check: %lu operations, %lu differences; warnings by type (kernel = shim): %lu %lu %lu %lu %lu\n",
	       checks, bad, kernel_warn[0], kernel_warn[1], kernel_warn[2], kernel_warn[3], kernel_warn[4]);
	return bad != 0;
}
