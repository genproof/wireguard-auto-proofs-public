#!/usr/bin/env bash
# patch/tree.sh OUT [--orig]: the C side of this repository, copied to OUT for the native tests: the code under
# test, the shim and the extracted kernel code (patch/), the harnesses, env.c, quickproof.conf, and the framework's
# include/, libc/ and runtime/.  With --orig the code under test is the unmodified upstream text
# (patch/upstream.sh) instead of this repository's patched files, and patch/counter_validate.c is its version before
# patch/wgpatch.py (patch/upstream/counter_validate.c); everything else is the same.
set -euo pipefail
R=$(cd "$(dirname "$0")/.." && pwd)
OUT=${1:?usage: patch/tree.sh OUT [--orig]}; ORIG=${2:-}
CODE=(
  drivers/net/wireguard/noise.c drivers/net/wireguard/noise.h drivers/net/wireguard/cookie.c
  drivers/net/wireguard/cookie.h drivers/net/wireguard/messages.h drivers/net/wireguard/receive.c
  lib/crypto/blake2s.c include/crypto/blake2s.h
  lib/crypto/chacha.c lib/crypto/chacha-block-generic.c include/crypto/chacha.h
  lib/crypto/poly1305.c lib/crypto/poly1305-donna32.c include/crypto/poly1305.h include/crypto/internal/poly1305.h
  lib/crypto/chacha20poly1305.c include/crypto/chacha20poly1305.h
  lib/crypto/curve25519.c lib/crypto/curve25519-fiat32.c include/crypto/curve25519.h
)
SRC=$R
if [ "$ORIG" = --orig ]; then SRC=$("$R/patch/upstream.sh"); fi
rm -rf "$OUT"; mkdir -p "$OUT/quickproof"
cp -r "$R/patch" "$R/harness" "$R/env.c" "$R/quickproof.conf" "$OUT/"
cp -r "$R/quickproof/include" "$R/quickproof/libc" "$R/quickproof/runtime" "$OUT/quickproof/"
for f in "${CODE[@]}"; do
  mkdir -p "$OUT/$(dirname "$f")"
  cp "$SRC/$f" "$OUT/$f"
done
if [ "$ORIG" = --orig ]; then cp "$R/patch/upstream/counter_validate.c" "$OUT/patch/counter_validate.c"; fi
echo "$OUT"
