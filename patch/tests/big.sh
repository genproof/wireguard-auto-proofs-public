#!/usr/bin/env bash
# patch/tests/big.sh [orig|patched|both] [poly1305|aead|all]: the failing range of the series P22/P23
# (DEVIATIONS.md): messages, associated data and poly1305_update chunks of about 2^32 bytes, and single
# poly1305_update calls of 2 GiB and more, against the reference primitives of harness/common.h, natively (gcc -O2,
# no sanitizers: 4 GiB buffers; each case in a child process).  On the unmodified upstream code the 4 GiB cases
# fail; on this repository's code every case must give the RFC 8439 result.  Needs about 17 GiB of memory.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
R=$(cd "$HERE/../.." && pwd)
WHICH=${1:-both}; CASES=${2:-all}
W=$(mktemp -d /tmp/wg-big.XXXXXX); trap 'rm -rf "$W"' EXIT
run() {   # run orig|patched
  local v=$1 flag=""
  [ "$v" == orig ] && flag=--orig
  "$R/patch/tree.sh" "$W/$v" $flag >/dev/null
  (cd "$W/$v" && gcc -O2 -g -w -Ipatch/include -Idrivers/net/wireguard -Iinclude -Iquickproof/include \
    -isystem "$(gcc -print-file-name=include)" -DCONFIG_CRYPTO_LIB_POLY1305_RSIZE=1 "$HERE/big.c" \
    lib/crypto/blake2s.c lib/crypto/chacha.c lib/crypto/chacha-block-generic.c lib/crypto/poly1305.c \
    lib/crypto/poly1305-donna32.c lib/crypto/chacha20poly1305.c patch/wg_shim.c drivers/net/wireguard/noise.c \
    drivers/net/wireguard/cookie.c lib/crypto/curve25519.c lib/crypto/curve25519-fiat32.c -o "$W/big_$v")
  echo "== $v"
  "$W/big_$v" "$CASES" || true
}
case $WHICH in
  orig) run orig ;;
  patched) run patched ;;
  *) run orig; run patched ;;
esac
