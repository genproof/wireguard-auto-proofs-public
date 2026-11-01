#!/usr/bin/env bash
# patch/diff.sh [ITERATIONS] [SEEDS] [--coverage]: the differential test of the patch (DEVIATIONS.md).
#
# Copies the unmodified upstream code and this repository's code (patch/tree.sh --orig, patch/tree.sh), builds
# patch/diff.c against each (all units of quickproof.conf with the same shim; gcc -O1, ASan+UBSan, aborting on the
# first report), runs both with the same seeds and compares their outputs, section by section (every output byte
# and return value).  Also checks that nothing in the handshake
# refers to the scatterlist functions the patch compiles out (P18).  With --coverage: a gcov build of the
# patched tree, reporting the execution count of every line marked QUICKPROOF (every hunk must be executed).
# The series P22/P23 (poly1305_update's loop giving poly1305_blocks at most round_down(min(nbytes, UINT_MAX), 16)
# bytes per call; chacha_crypt's loop of round_down(UINT_MAX, 64)-byte chunks while more than UINT_MAX bytes
# remain) is also built with small limits, so that the loops run several iterations on the driver's short inputs:
# "small1" (chacha_crypt: chunks of round_down(127, 64) = 64 bytes while more than 127 remain; poly1305_update: at
# most 16 bytes per poly1305_blocks call) and "small2" (192 bytes while more than 255 remain; at most 48 bytes);
# copies of the patched tree with smaller limits substituted for UINT_MAX in the series' lines.  Their
# outputs must equal upstream's too.  Sanity (seed 1 only, must DIFFER): "badchacha" rounds the chacha chunk
# to 32 bytes (96: not a multiple of the ChaCha block), "badpoly" rounds the Poly1305 chunk to 8 bytes.
set -euo pipefail
PROJ=$(cd "$(dirname "$0")/.." && pwd)
ITERS=${1:-20000}; SEEDS=${2:-5}; COV=${3:-}
W=$(mktemp -d /tmp/wg-diff.XXXXXX)
[ -z "${KEEP:-}" ] && trap 'rm -rf "$W"' EXIT; echo "work dir: $W"
"$PROJ/patch/tree.sh" "$W/orig" --orig >/dev/null
"$PROJ/patch/tree.sh" "$W/patched" >/dev/null
UNITS_LIST="drivers/net/wireguard/noise.c drivers/net/wireguard/cookie.c patch/counter_validate.c lib/crypto/blake2s.c
 lib/crypto/chacha.c lib/crypto/chacha-block-generic.c lib/crypto/poly1305.c lib/crypto/poly1305-donna32.c
 lib/crypto/chacha20poly1305.c lib/crypto/curve25519.c lib/crypto/curve25519-fiat32.c patch/wg_shim.c quickproof/libc/libc.c"
build() {   # build TREE OUT EXTRA-FLAGS...
  local t=$1 out=$2; shift 2
  local fl=(-O1 -g -w "$@" -Ipatch/include -Idrivers/net/wireguard -Iinclude -Iquickproof/include -Iharness
            -isystem "$(gcc -print-file-name=include)" -DCONFIG_CRYPTO_LIB_POLY1305_RSIZE=1)
  mkdir -p "$out"
  local objs=()
  for u in $UNITS_LIST; do
    (cd "$t" && gcc "${fl[@]}" -c "$u" -o "$out/$(basename "$u" .c).o"); objs+=("$out/$(basename "$u" .c).o")
  done
  (cd "$t" && gcc "${fl[@]}" -c "$PROJ/patch/diff.c" -o "$out/diff.o")
  gcc "$@" "${objs[@]}" "$out/diff.o" -o "$out/diff"
}
SAN=(-fsanitize=address,undefined -fno-sanitize-recover=all)
build "$W/orig" "$W/b_orig" "${SAN[@]}"
build "$W/patched" "$W/b_patched" "${SAN[@]}"
variant() {   # variant NAME CHACHA_LIMIT CHACHA_ROUND POLY_LIMIT POLY_ROUND: the patched tree with smaller limits
  cp -r "$W/patched" "$W/$1"
  python3 - "$W/$1" "$2" "$3" "$4" "$5" <<'PYEOF' || { echo "series lines not found"; exit 1; }
import sys
t, cl, cr, pl, pr = sys.argv[1:]
def sub(p, old, new):
    s = open(p).read()
    if s.count(old) != 1:
        sys.exit('variant: %r not found once in %s' % (old, p))
    open(p, 'w').write(s.replace(old, new))
c = t + '/lib/crypto/chacha.c'
sub(c, '\twhile (bytes > UINT_MAX) {\n', '\twhile (bytes > %s) {\n' % cl)
sub(c, 'round_down(UINT_MAX, CHACHA_BLOCK_SIZE);', 'round_down(%s, %s);' % (cl, cr))
sub(t + '/lib/crypto/poly1305.c', 'round_down(min(nbytes, UINT_MAX),\n\t\t\t\t\t\t\t   POLY1305_BLOCK_SIZE);',
    'round_down(min(nbytes, %s),\n\t\t\t\t\t\t\t   %s);' % (pl, pr))
PYEOF
  build "$W/$1" "$W/b_$1" "${SAN[@]}"
}
VARIANTS="small1 small2"
variant small1 127U CHACHA_BLOCK_SIZE 16 POLY1305_BLOCK_SIZE
variant small2 255U CHACHA_BLOCK_SIZE 50 POLY1305_BLOCK_SIZE
variant badchacha 100U 32 UINT_MAX POLY1305_BLOCK_SIZE
variant badpoly UINT_MAX CHACHA_BLOCK_SIZE 50 8
# P18: the scatterlist functions are not referenced by the handshake code (upstream objects)
if nm "$W/b_orig/noise.o" "$W/b_orig/cookie.o" | grep -q sg_inplace; then echo "P18: handshake refers to the sg functions"; exit 1; fi
fail=0
for s in $(seq 1 "$SEEDS"); do
  a=$(ASAN_OPTIONS=detect_leaks=0 "$W/b_orig/diff" "$ITERS" "$s")
  b=$(ASAN_OPTIONS=detect_leaks=0 "$W/b_patched/diff" "$ITERS" "$s")
  if [ "$a" == "$b" ]; then echo "seed $s: $ITERS iterations, outputs identical"; else echo "seed $s: DIFFERENT"; diff <(echo "$a") <(echo "$b") || true; fail=1; fi
  for c in $VARIANTS; do
    b2=$(ASAN_OPTIONS=detect_leaks=0 "$W/b_$c/diff" "$ITERS" "$s")
    if [ "$a" == "$b2" ]; then echo "seed $s: $c build, outputs identical"; else echo "seed $s: $c DIFFERENT"; diff <(echo "$a") <(echo "$b2") || true; fail=1; fi
  done
  if [ "$s" == 1 ]; then   # sanity: a wrong chunking must be seen
    for c in badchacha badpoly; do
      b2=$(ASAN_OPTIONS=detect_leaks=0 "$W/b_$c/diff" "$ITERS" "$s" 2>&1 || true)
      if [ "$a" == "$b2" ]; then echo "seed $s: SANITY FAILED: $c build gives identical outputs"; fail=1
      else echo "seed $s: sanity $c build differs (as it must): $(diff <(echo "$a") <(echo "$b2") | grep -c '^>') of $(echo "$a" | wc -l) lines"; fi
    done
  fi
done
echo "$b"
if [ "$COV" == "--coverage" ]; then
  build "$W/patched" "$W/b_cov" --coverage -O0
  (cd "$W/patched" && "$W/b_cov/diff" "$ITERS" 1 >/dev/null)
  echo "== execution counts of the QUICKPROOF lines (patched tree, $ITERS iterations, seed 1)"
  for u in drivers/net/wireguard/noise.c drivers/net/wireguard/cookie.c patch/counter_validate.c lib/crypto/blake2s.c \
           lib/crypto/chacha-block-generic.c lib/crypto/chacha20poly1305.c lib/crypto/poly1305.c lib/crypto/curve25519-fiat32.c; do
    (cd "$W/patched" && gcov -o "$W/b_cov/$(basename "$u" .c).o" "$u" >/dev/null 2>&1 || true)
  done
  (cd "$W/patched" && gcov -o "$W/b_cov/poly1305.o" include/crypto/internal/poly1305.h >/dev/null 2>&1 || true)
  for g in "$W"/patched/*.gcov; do
    awk -v f="$(basename "$g" .gcov)" '
      /QUICKPROOF P[0-9][0-9]/ { match($0, /P[0-9][0-9]/); id = substr($0, RSTART, 3); pend = 3 }
      pend > 0 && $1 ~ /^[0-9]+\*?:$/ { sub(":", "", $1); if (!(id in seen) || $1 + 0 > cnt[id]) cnt[id] = $1 + 0; seen[id] = 1; pend-- }
      pend > 0 && $1 ~ /#####/ { if (!(id in seen)) { cnt[id] = 0; seen[id] = 1 } pend-- }
      END { for (k in cnt) printf "%s %-28s executed %d\n", k, f, cnt[k] }' "$g"
  done | sort -u
  # the series P22/P23 carries no QUICKPROOF markers (verbatim text): the execution counts of its lines, in the
  # patched tree and in the small1 build (where its loops iterate)
  build "$W/small1" "$W/b_cov_small1" --coverage -O0
  (cd "$W/small1" && "$W/b_cov_small1/diff" "$ITERS" 1 >/dev/null)
  for t in patched small1; do
    b=b_cov; [ $t == small1 ] && b=b_cov_small1
    for u in lib/crypto/chacha.c lib/crypto/poly1305.c; do
      (cd "$W/$t" && gcov -o "$W/$b/$(basename "$u" .c).o" "$u" >/dev/null 2>&1 || true)
    done
    echo "== execution counts of the series' lines ($t tree, $ITERS iterations, seed 1)"
    grep -h -E 'while \(bytes > |chacha_crypt_arch\(state, dst, src, (l|bytes), nrounds\)|if \(nbytes >= POLY1305_BLOCK_SIZE - desc->buflen\)|while \(nbytes >= POLY1305_BLOCK_SIZE\)|poly1305_blocks\(&desc->state, src, bulk_len, 1\)|nbytes -= bulk_len' \
      "$W/$t/chacha.c.gcov" "$W/$t/poly1305.c.gcov" | sed 's/^ *//'
  done
fi
exit $fail
