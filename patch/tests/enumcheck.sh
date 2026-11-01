#!/usr/bin/env bash
# patch/tests/enumcheck.sh (DEVIATIONS.md C04): enumeration constants above INT_MAX, gcc vs CompCert.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
R=$(cd "$HERE/../.." && pwd)
W=$(mktemp -d /tmp/wg-enum.XXXXXX); trap 'rm -rf "$W"' EXIT
"$R/patch/tree.sh" "$W/tree" >/dev/null
cd "$W/tree"
FL=(-Ipatch/include -Idrivers/net/wireguard -Iinclude -Iquickproof/include)
gcc -w "${FL[@]}" -isystem "$(gcc -print-file-name=include)" "$HERE/enumcheck.c" -o "$W/g"
"$W/g" > "$W/gcc.txt"
eval "$(opam env --switch="${QP_OPAM_SWITCH:-liblzma}" --set-switch)"
ccomp -interp -quiet "${FL[@]}" "$HERE/enumcheck.c" 2>/dev/null > "$W/ccomp.txt"
if diff "$W/gcc.txt" "$W/ccomp.txt"; then echo "gcc and CompCert agree:"; cat "$W/gcc.txt"; else echo "DIFFERENT"; exit 1; fi
