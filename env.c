// Value distributions for native and interpreter runs of the harnesses.  They override the
// framework's generic nondet_* (quickproof/runtime/fuzz_driver.c).  The laws themselves have no size bound
// (N_MAX = SIZE_MAX): the small sizes and short operation sequences of test runs come from here.
//   bytes: mostly uniformly random (keys, nonces, messages), sometimes all zero or all 0xff (degenerate keys and
//          points, zero timestamps), sometimes random with a few zero bytes;
//   sizes: small (0..3, around the 16/32/64-byte block edges, up to 300); never large, since sizes are also
//          operation counts; under CompCert's interpreter smaller still (0..3 mostly);
//   u32:   random, small, 0, all ones, around 2^31; u8: random.
#include <stddef.h>
#include <stdint.h>
extern uint64_t quickproof_rnd(void);
#define rnd quickproof_rnd

uint8_t nondet_u8(void) { return (uint8_t) rnd(); }

uint32_t nondet_u32(void)
{
	switch (rnd() % 8) {
	case 0: return (uint32_t) (rnd() % 8);
	case 1: return 0;
	case 2: return 0xffffffffu - (uint32_t) (rnd() % 4);
	case 3: return 0x80000000u + (uint32_t) (rnd() % 4) - 2;
	default: return (uint32_t) rnd();
	}
}

size_t nondet_size(void)
{
#ifdef GP_CUSTOM_NONDET
	// CompCert's interpreter (tools/interp.sh defines GP_CUSTOM_NONDET): an X25519 takes about 13 s there, so
	// sizes and operation counts stay very small (0..3, and the 16/32/64-byte edges now and then)
	if (rnd() % 4 != 0)
		return rnd() % 4;
	return 16 * (1 + rnd() % 4) - 1 + rnd() % 3;
#endif
	switch (rnd() % 6) {
	case 0: return rnd() % 4;
	case 1: return 16 * (1 + rnd() % 5) - 1 + rnd() % 3;   // around 16, 32, 48, 64, 80
	case 2: return rnd() % 40;
	case 3: return 60 + rnd() % 10;
	default: return rnd() % 300;
	}
}

void nondet_bytes(uint8_t *buf, size_t n)
{
	const unsigned kind = rnd() % 20;
	for (size_t i = 0; i < n; ++i) {
		switch (kind) {
		case 0: buf[i] = 0; break;
		case 1: buf[i] = 0xff; break;
		case 2: buf[i] = rnd() % 4 == 0 ? 0 : (uint8_t) rnd(); break;
		default: buf[i] = (uint8_t) rnd(); break;
		}
	}
}
