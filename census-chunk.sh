#!/usr/bin/env bash
# One shard of the wide census: both passes per file from a list slice into
# the shared RES dir. Usage: census-chunk.sh <list-file> <res-dir>
set -uo pipefail
LIST="$1"; RES="$2"
rev=$(git -C /home/b7r6/src/straylight/continuity rev-parse --short HEAD)
TC=$(cat ~/src/vendor/mathlib4/lean-toolchain)
EXE="$HOME/.cache/lean4fmt-census/$rev-${TC//[:\/]/_}/.lake/build/bin/lean4fmt"
ML=~/src/vendor/mathlib4
cd "$ML"
CORE="$(elan run "$TC" lean --print-libdir)"
LP="$ML/.lake/build/lib/lean"
for p in "$ML"/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
export LEAN_PATH="$LP:$CORE" EXE TC RES

runone() {
  f="$1"; slug="${f//\//_}"
  timeout 180 elan run "$TC" "$EXE" --stats --lake off "$f" > "$RES/$slug.out" 2>/dev/null
  timeout 180 elan run "$TC" "$EXE" --log-level debug --lake off "$f" \
    > /dev/null 2> "$RES/$slug.err"
}
export -f runone
xargs -P 2 -I{} bash -c 'runone {}' < "$LIST"
echo "chunk done: $(wc -l < "$LIST") files"
