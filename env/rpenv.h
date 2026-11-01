// Value distributions for the replay-window laws (rp_*): nonces cluster so that windows overlap, repeat and slide.
//   any_u64 = nondet_u32() << 32 | nondet_u32(): the high rp_env_half is mostly 0, sometimes 0xffffffff (then the low rp_env_half
//   lies around the limit 2^64 - 8130), rarely random; the low rp_env_half is mostly below 20000 (windows of 8128 overlap);
//   sizes (upto): mostly below 8200 or 20000, sometimes near the top; nondet_u8: about 1 in 160 ends a sequence.
#include <stddef.h>
#include <stdint.h>
extern uint64_t quickproof_rnd(void);
#define rnd quickproof_rnd
static int rp_env_half;              // 0: the next nondet_u32 is a high rp_env_half, 1: a low rp_env_half
static uint32_t rp_env_high;

uint8_t nondet_u8(void) { return rnd() % 160 == 0 ? 0 : (uint8_t) (1 + rnd() % 255); }

uint32_t nondet_u32(void)
{
	rp_env_half ^= 1;
	if (rp_env_half == 1) {
		uint64_t k = rnd() % 20;
		rp_env_high = k < 15 ? 0 : k < 19 ? 0xffffffffu : (uint32_t) rnd();
		return rp_env_high;
	}
	if (rp_env_high == 0xffffffffu)
		return 0xffffe03eu - 20000u + (uint32_t) (rnd() % 28130);   // around 2^64 - 8130
	return rnd() % 8 == 0 ? (uint32_t) rnd() : (uint32_t) (rnd() % 20000);
}

size_t nondet_size(void)
{
	switch (rnd() % 20) {
	case 0: case 1: return rnd() % 4;
	case 2: case 3: return SIZE_MAX - rnd() % 20000;
	case 4: return (size_t) rnd();
	case 5: case 6: case 7: case 8: case 9: return rnd() % 20000;
	default: return rnd() % 8200;           // offsets inside one window, spread out
	}
}

void nondet_bytes(uint8_t *buf, size_t n)
{
	for (size_t i = 0; i < n; ++i)
		buf[i] = (uint8_t) rnd();
}
