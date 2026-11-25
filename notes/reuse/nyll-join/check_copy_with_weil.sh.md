# `check_copy_with_weil.sh`

This page holds the script `check_copy_with_weil.sh` as it is, in the code block below. To use it, save the content of the block under that name.

```sh
#!/usr/bin/env bash
# Import the seven roots of the copy `Nyll/` together with the whole of weil-conjectures
# in one Lean file, without Lake, and report whether Lean accepts the import.
#
# Usage: check_copy_with_weil.sh ROOT [WEIL_LIB]
#   ROOT      the Lake workspace that holds `Nyll/` and its compiled outputs in
#             `.lake/build/lib/lean` (the packages in `.lake/packages/*` are added too)
#   WEIL_LIB  the compiled weil-conjectures (default /srv/ll-nyll/weil-lib)
#
# The seven roots are the modules of the copy that no other module of the copy imports.
# The script recomputes them from the import lines, so that it stays right if the copy grows.
# Exit status 0 when the import is accepted; Lean's messages are printed otherwise.
set -euo pipefail
ROOT=$(cd "${1:?usage: check_copy_with_weil.sh ROOT [WEIL_LIB]}" && pwd)
WEIL=${2:-/srv/ll-nyll/weil-lib}
WORK=$(mktemp -d "${TMPDIR:-/tmp}/copyweil.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

# All modules of the copy, and all modules of the copy that some module of the copy imports.
( cd "$ROOT" && find Nyll -name '*.lean' | sed 's|\.lean$||; s|/|.|g' | sort ) > "$WORK/all"
( cd "$ROOT" && grep -rhoE '^(public )?import Nyll\.[A-Za-z0-9_.]+' Nyll --include=*.lean \
    | sed -E 's/^(public )?import //' | sort -u ) > "$WORK/imported"
comm -23 "$WORK/all" "$WORK/imported" > "$WORK/roots"
echo "roots of the copy: $(wc -l < "$WORK/roots")"
sed 's/^/  /' "$WORK/roots"

{
  sed 's/^/import /' "$WORK/roots"
  echo "import WeilConjectures"
} > "$WORK/CopyWithWeil.lean"

LP="$ROOT/.lake/build/lib/lean:$WEIL"
for d in "$ROOT"/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
start=$(date +%s)
if env LEAN_PATH="$LP" lean "$WORK/CopyWithWeil.lean"; then
  echo "ACCEPTED: the copy's roots and WeilConjectures import together ($(( $(date +%s) - start )) s)"
else
  echo "REFUSED ($(( $(date +%s) - start )) s)"
  exit 1
fi
```
