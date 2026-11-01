#!/usr/bin/env bash
# patch/tests/refkat.sh: the reference primitives of harness/common.h on published test vectors (native).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
R=$(cd "$HERE/../.." && pwd)
W=$(mktemp -d /tmp/wg-refkat.XXXXXX); trap 'rm -rf "$W"' EXIT
"$R/patch/tree.sh" "$W/tree" >/dev/null
cd "$W/tree"
gcc -O1 -g -w -fsanitize=address,undefined -fno-sanitize-recover=all -Ipatch/include -Idrivers/net/wireguard -Iinclude \
  -Iquickproof/include -isystem "$(gcc -print-file-name=include)" -DCONFIG_CRYPTO_LIB_POLY1305_RSIZE=1 "$HERE/refkat.c" \
  drivers/net/wireguard/noise.c drivers/net/wireguard/cookie.c lib/crypto/blake2s.c lib/crypto/chacha.c \
  lib/crypto/chacha-block-generic.c lib/crypto/poly1305.c lib/crypto/poly1305-donna32.c lib/crypto/chacha20poly1305.c \
  lib/crypto/curve25519.c lib/crypto/curve25519-fiat32.c patch/wg_shim.c -o "$W/refkat"
"$W/refkat"
