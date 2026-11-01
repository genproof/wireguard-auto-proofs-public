#!/usr/bin/env bash
# patch/check.sh: the code under test is the upstream code with patch/wgpatch.py applied, and nothing else.  Copies
# the unmodified upstream files (patch/tree.sh --orig), runs patch/wgpatch.py there (the two patches of
# patch/series/ verbatim, then the rewrites P01-P21 of DEVIATIONS.md, and the checks of the extracted texts), and
# compares every file of the code under test with this repository's.
set -euo pipefail
R=$(cd "$(dirname "$0")/.." && pwd)
W=$(mktemp -d); trap 'rm -rf "$W"' EXIT
"$R/patch/tree.sh" "$W/t" --orig > /dev/null
(cd "$W/t" && python3 patch/wgpatch.py)
n=0; bad=0
for f in $(cd "$W/t" && find drivers lib include -type f | sort) patch/counter_validate.c; do
  n=$((n + 1))
  if ! cmp -s "$W/t/$f" "$R/$f"; then echo "DIFFERENT: $f"; bad=1; fi
done
if [ $bad = 0 ]; then echo "patch/check.sh: the $n files of the code under test are upstream + patch/wgpatch.py, byte for byte"; fi
exit $bad
