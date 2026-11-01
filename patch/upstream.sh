#!/usr/bin/env bash
# patch/upstream.sh: prints the directory of the unmodified Linux files at the pinned commit that this repository
# and its tests use: the upstream versions of the code under test, and the kernel files the tests compare the shim
# with.  They are read from $LINUX when it is set (a local clone of Linux that has the commit; nothing is fetched),
# otherwise from a shallow, blobless fetch of the commit from GitHub into build/linux (made on first use; only the
# listed files are downloaded).  The files are written to build/upstream/ once.
set -euo pipefail
cd "$(dirname "$0")/.."
COMMIT=551c722f40809618230001baccf219193e22fc5a
FILES=(
  # the code under test (as the repository has them, before patch/wgpatch.py)
  drivers/net/wireguard/noise.c drivers/net/wireguard/noise.h drivers/net/wireguard/cookie.c
  drivers/net/wireguard/cookie.h drivers/net/wireguard/messages.h drivers/net/wireguard/receive.c
  lib/crypto/blake2s.c include/crypto/blake2s.h
  lib/crypto/chacha.c lib/crypto/chacha-block-generic.c include/crypto/chacha.h
  lib/crypto/poly1305.c lib/crypto/poly1305-donna32.c include/crypto/poly1305.h include/crypto/internal/poly1305.h
  lib/crypto/chacha20poly1305.c include/crypto/chacha20poly1305.h
  lib/crypto/curve25519.c lib/crypto/curve25519-fiat32.c include/crypto/curve25519.h
  # what the tests compare the shim with (patch/shimtest/, patch/tests/refcount_check.sh, macrocheck.sh)
  drivers/net/wireguard/peerlookup.c drivers/net/wireguard/peerlookup.h
  include/crypto/utils.h lib/crypto/utils.c lib/crypto/memneq.c
  include/linux/refcount.h lib/refcount.c include/vdso/limits.h
)
D=build/upstream
if [ "$(cat $D/.commit 2>/dev/null || true)" != $COMMIT ]; then
  if [ -n "${LINUX:-}" ]; then
    R=$LINUX
  else
    R=build/linux
    if ! git -C $R cat-file -e "$COMMIT^{commit}" 2>/dev/null; then
      rm -rf $R; git init -q $R
      git -C $R remote add origin https://github.com/torvalds/linux.git
      git -C $R fetch -q --depth 1 --filter=blob:none origin $COMMIT >&2
    fi
  fi
  rm -rf $D; mkdir -p $D
  for f in "${FILES[@]}"; do
    mkdir -p "$D/$(dirname "$f")"
    git -C "$R" show "$COMMIT:$f" > "$D/$f"
  done
  echo $COMMIT > $D/.commit
fi
echo "$PWD/$D"
