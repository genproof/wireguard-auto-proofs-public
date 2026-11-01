#!/usr/bin/env bash
# patch/tests/keypairs_sat.sh [TREE] [BUILD] [SEEDS] [FIRST]: the unchanged law `keypairs` past the saturation of a
# reference count (2^31 + 64 gets of one keypair; env_sat.c), natively: library units and harness at -O2 without
# sanitizers for time (the harness with -fno-delete-null-pointer-checks, so a failed CHECK still ends the run), the
# framework's fuzz driver, one child process per seed, a timeout of 4 hours per seed.
set -euo pipefail
T=$(realpath "${1:-.}"); B=$(realpath -m "${2:-$T/build/sat}"); SEEDS=${3:-2}; FIRST=${4:-1}
cd "$T"
INC=(); DEFS=(); UNITS=()
GP=$(realpath quickproof)
source quickproof.conf
mkdir -p "$B"
LIBS=()
i=0
for u in "${UNITS[@]}"; do
  src=${u%%=*}; out=${u#*=}
  case $out in src/harness/*) continue;; esac
  case $(realpath "$src") in "$GP"/*) continue;; esac
  gcc -O2 -g -w "${DEFS[@]}" "${INC[@]}" -c "$src" -o "$B/lib$i.o"
  LIBS+=("$B/lib$i.o"); i=$((i+1))
done
gcc -O2 -g -w "${DEFS[@]}" "${INC[@]}" -c quickproof/runtime/fuzz_driver.c -o "$B/drv.o"
gcc -O2 -g -w ${SAT_DEFS:-} -c patch/tests/env_sat.c -o "$B/env_sat.o"
gcc -O2 -g -w -fno-delete-null-pointer-checks -Iquickproof/include -Iharness -Dmain=harness_main "${DEFS[@]}" "${INC[@]}" \
    -c harness/keypairs.c -o "$B/h_keypairs.o"
gcc "$B/h_keypairs.o" "${LIBS[@]}" "$B/drv.o" "$B/env_sat.o" -o "$B/keypairs_sat"
"$B/keypairs_sat" "$SEEDS" "$FIRST" 0 14400
