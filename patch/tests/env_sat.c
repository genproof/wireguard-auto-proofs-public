// patch/tests/env_sat.c: a scripted environment that drives the UNCHANGED law `keypairs` past the saturation of a
// reference count (2^31 references), which env.c never reaches.  Used by keypairs_sat.sh instead of
// env.c.  The values are those of env.c (random, small sizes), except:
//   - nondet_size: the 1st call (other peers) 1, the 2nd (their keypair entries) 0, the 3rd (the number of
//     operations) 2^31 + SAT_TAIL; later calls 0 during the get phase;
//   - the get phase: from the first call of nondet_u8 after the SAT_START-th at which a keypair is live (the shim
//     has allocated more than it freed), for 3 * (2^31 + 64) calls, nondet_u8 returns 13
//     (operation 13 % 8 = 5: wg_noise_keypair_get; clock shift 13 with a zero draw; not NULL) and nondet_u32 0, so
//     that the harness gets 2^31 + 64 references to the first live keypair: its count saturates;
//   - afterwards: random again (puts of the saturated keypair, rotations, clears, ...), then the law's end (clear,
//     every kept reference put: the saturated keypair is leaked, everything else freed).
// It prints the shim's refcount_t warning counters when the get phase ends and every 2^28 calls.
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
extern uint64_t quickproof_rnd(void);
extern unsigned long wg_shim_refcount_warn[5];
#define rnd quickproof_rnd
#ifndef SAT_START
#define SAT_START 300
#endif
#ifndef SAT_TAIL
#define SAT_TAIL 6000
#endif
#ifndef SAT_GETS
#define SAT_GETS ((1ULL << 31) + 64)
#endif
#define GETS ((uint64_t)SAT_GETS)

extern unsigned long wg_shim_allocs, wg_shim_frees;
static uint64_t n_u8, n_size, start;
static int reported;

// the get phase begins at the first nondet_u8 call after SAT_START calls at which a keypair is live (the shim's
// allocations exceed its frees), and lasts 3 * GETS calls
static int in_get_phase(void)
{
	return start != 0 && n_u8 >= start && n_u8 < start + 3 * GETS;
}

uint8_t nondet_u8(void)
{
	n_u8++;
	if (start == 0 && n_u8 > SAT_START && wg_shim_allocs > wg_shim_frees) {
		start = n_u8;
		fprintf(stderr, "env_sat: get phase from call %llu\n", (unsigned long long)start);
	}
	if (in_get_phase()) {
		if ((n_u8 & ((1ULL << 28) - 1)) == 0)
			fprintf(stderr, "env_sat: %llu calls, warnings %lu %lu %lu %lu %lu\n", (unsigned long long)n_u8,
				wg_shim_refcount_warn[0], wg_shim_refcount_warn[1], wg_shim_refcount_warn[2],
				wg_shim_refcount_warn[3], wg_shim_refcount_warn[4]);
		return 13;
	}
	if (start != 0 && n_u8 >= start + 3 * GETS && !reported) {
		reported = 1;
		fprintf(stderr, "env_sat: get phase over: warnings ADD_NOT_ZERO_OVF %lu ADD_OVF %lu ADD_UAF %lu SUB_UAF %lu "
			"DEC_LEAK %lu\n", wg_shim_refcount_warn[0], wg_shim_refcount_warn[1], wg_shim_refcount_warn[2],
			wg_shim_refcount_warn[3], wg_shim_refcount_warn[4]);
	}
	return (uint8_t)rnd();
}

uint32_t nondet_u32(void)
{
	if (in_get_phase())
		return 0;
	switch (rnd() % 8) {
	case 0: return (uint32_t)(rnd() % 8);
	case 1: return 0;
	case 2: return 0xffffffffu - (uint32_t)(rnd() % 4);
	case 3: return 0x80000000u + (uint32_t)(rnd() % 4) - 2;
	default: return (uint32_t)rnd();
	}
}

size_t nondet_size(void)
{
	n_size++;
	if (n_size == 1)
		return 1;
	if (n_size == 2)
		return 0;
	if (n_size == 3)
		return (size_t)GETS + SAT_TAIL;
	if (in_get_phase())
		return 0;
	return rnd() % 4;
}

void nondet_bytes(uint8_t *buf, size_t n)
{
	const unsigned kind = rnd() % 20;
	for (size_t i = 0; i < n; ++i) {
		switch (kind) {
		case 0: buf[i] = 0; break;
		case 1: buf[i] = 0xff; break;
		case 2: buf[i] = rnd() % 4 == 0 ? 0 : (uint8_t)rnd(); break;
		default: buf[i] = (uint8_t)rnd(); break;
		}
	}
}
