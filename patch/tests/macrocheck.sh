#!/usr/bin/env bash
# patch/tests/macrocheck.sh: shim row S25 (DEVIATIONS.md).  The series P22/P23 uses UINT_MAX, min() and
# round_down(); the shim (patch/include/quickproof_kernel.h) defines UINT_MAX with the kernel's own text and has min()
# (S20) and round_down() (S11) as plain macros.  Checks, with gcc:
#   1. the shim's UINT_MAX has the value AND the type of the kernel's definition, taken from the pinned upstream
#      (include/vdso/limits.h; renamed K_UINT_MAX);
#   2. the series' two expressions, as the shim expands them, give the kernel's values: round_down(UINT_MAX,
#      CHACHA_BLOCK_SIZE) = 2^32 - 64 (unsigned int), and round_down(min(nbytes, UINT_MAX), POLY1305_BLOCK_SIZE)
#      assigned to an unsigned int = the largest multiple of 16 not above min(nbytes, 2^32 - 1), for nbytes at
#      every boundary (0..64, around 2^31, 2^32 - 1, 2^32, 2^63, SIZE_MAX) and 10^6 random size_t values.  (The
#      kernel's min() of a size_t and the unsigned int constant UINT_MAX compares them as size_t and yields a
#      size_t, include/linux/minmax.h; its round_down() masks with (typeof(x))(y - 1), include/linux/math.h.)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
PROJ=$(cd "$HERE/../.." && pwd)
U=$("$PROJ/patch/upstream.sh")
COMMIT=$(cat "$U/.commit")
W=$(mktemp -d /tmp/wg-macro.XXXXXX); trap 'rm -rf "$W"' EXIT
grep -E '^#define[[:space:]]+UINT_MAX[[:space:]]' "$U/include/vdso/limits.h" \
  | sed -E 's/^#define[[:space:]]+UINT_MAX/#define K_UINT_MAX/' > "$W/klimits.h"
echo "kernel text at $COMMIT:"; sed 's/^/  /' "$W/klimits.h"
[ "$(wc -l < "$W/klimits.h")" -eq 1 ] || { echo "UINT_MAX not found in the pinned upstream"; exit 1; }
cat > "$W/t.c" <<'CEOF'
#include "quickproof_kernel.h"
#include "klimits.h"
#include <stdio.h>
#include <stdlib.h>
#define CHACHA_BLOCK_SIZE 64
#define POLY1305_BLOCK_SIZE 16
#define TYPE(x) _Generic((x), unsigned int: 1, int: 2, unsigned long: 3, long: 4, default: 0)
_Static_assert(UINT_MAX == K_UINT_MAX && TYPE(UINT_MAX) == TYPE(K_UINT_MAX) && TYPE(UINT_MAX) == 1, "UINT_MAX");
_Static_assert(UINT_MAX == 0xffffffffu, "value");
static unsigned long long rs = 88172645463325252ULL;
static size_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (size_t)rs; }
static int check(size_t nbytes)
{
	unsigned int got = round_down(min(nbytes, UINT_MAX), POLY1305_BLOCK_SIZE);   /* the series' text */
	size_t m = nbytes < (size_t)0xffffffff ? nbytes : (size_t)0xffffffff;
	unsigned int want = (unsigned int)(m - m % 16);
	if (got != want) { printf("MISMATCH nbytes=%zu: %u != %u\n", nbytes, got, want); return 1; }
	return 0;
}
int main(void)
{
	unsigned int l = round_down(UINT_MAX, CHACHA_BLOCK_SIZE);                      /* the series' text */
	int bad = 0;
	size_t i, n = 0;
	if (l != 0xffffffc0u || TYPE(round_down(UINT_MAX, CHACHA_BLOCK_SIZE)) != 1) { printf("chacha chunk %u\n", l); bad = 1; }
	for (i = 0; i <= 64; i++, n++) bad |= check(i);
	{ size_t b[] = { 0x7fffffffUL, 0x80000000UL, 0xffffffffUL, 0x100000000UL, 0x7fffffffffffffffUL, (size_t)-1 };
	  for (size_t j = 0; j < sizeof(b) / sizeof(b[0]); j++)
		for (long d = -40; d <= 40; d++, n++) bad |= check(b[j] + (size_t)d); }
	for (i = 0; i < 1000000; i++, n++) bad |= check(rnd() >> (rnd() % 64));
	printf("%s: chacha chunk %u; round_down(min(nbytes, UINT_MAX), 16) on %zu values\n", bad ? "FAILED" : "ok", l, n);
	return bad;
}
CEOF
gcc -O1 -Wall -Wno-unused-function -I"$W" -I"$PROJ/patch/include" "$W/t.c" -o "$W/t"
"$W/t"
