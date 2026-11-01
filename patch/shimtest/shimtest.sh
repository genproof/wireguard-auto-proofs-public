#!/usr/bin/env bash
# patch/shimtest/shimtest.sh [ITERATIONS] [SEEDS]: differential test of the shim against upstream kernel code
# (DEVIATIONS.md): the index and public-key tables (upstream drivers/net/wireguard/peerlookup.c), crypto_memneq /
# crypto_xor(_cpy) (upstream lib/crypto/memneq.c, utils.c and include/crypto/utils.h, x86_64 configuration), and
# the byte-order / bit helpers (the kernel's x86_64 semantics).  The upstream files are those of the pinned commit
# (patch/upstream.sh).  Native, ASan+UBSan; both builds must print identical outputs.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
R=$(cd "$HERE/../.." && pwd)
ITERS=${1:-20000}; SEEDS=${2:-5}
U=$("$R/patch/upstream.sh")
W=$(mktemp -d /tmp/wg-shimtest.XXXXXX); trap 'rm -rf "$W"' EXIT
"$R/patch/tree.sh" "$W/tree" >/dev/null
T=$W/tree
mkdir -p "$W/up/include/crypto"
cp "$U/drivers/net/wireguard/peerlookup.c" "$U/drivers/net/wireguard/peerlookup.h" "$U/lib/crypto/utils.c" \
   "$U/lib/crypto/memneq.c" "$W/up/"
cp "$U/include/crypto/utils.h" "$W/up/include/crypto/utils.h"
SAN=(-O1 -g -w -fsanitize=address,undefined -fno-sanitize-recover=all)
GI=$(gcc -print-file-name=include)
UP=(-DUPSTREAM -DCONFIG_HAVE_EFFICIENT_UNALIGNED_ACCESS=1 -DCONFIG_64BIT=1 -include "$HERE/env/upstream_extra.h"
    -I"$W/up" -I"$W/up/include" -I"$HERE/env" -I"$HERE" -I"$T/patch/include" -I"$T/drivers/net/wireguard" -I"$T/include"
    -I"$T/quickproof/include" -isystem "$GI")
gcc "${SAN[@]}" "${UP[@]}" "$HERE/shimtest.c" "$HERE/adapter_upstream.c" "$W/up/utils.c" "$W/up/memneq.c" -o "$W/upstream"
SH=(-I"$HERE" -I"$T/patch/include" -I"$T/drivers/net/wireguard" -I"$T/include" -I"$T/quickproof/include" -isystem "$GI")
gcc "${SAN[@]}" "${SH[@]}" "$HERE/shimtest.c" "$HERE/adapter_shim.c" "$T/patch/wg_shim.c" -o "$W/shim"
fail=0
for s in $(seq 1 "$SEEDS"); do
  a=$(ASAN_OPTIONS=detect_leaks=0 "$W/upstream" "$ITERS" "$s")
  b=$(ASAN_OPTIONS=detect_leaks=0 "$W/shim" "$ITERS" "$s")
  if [ "$a" == "$b" ]; then echo "seed $s: $ITERS iterations, outputs identical"; else echo "seed $s: DIFFERENT"; diff <(echo "$a") <(echo "$b") || true; fail=1; fi
done
echo "$b"
exit $fail
