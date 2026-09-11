#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
#                                                  // LEAN4FMT // CORE FUZZ
# ─────────────────────────────────────────────────────────────────────────────
#
#   The zero-passthrough guard on the SHIPPING exe: for every file in
#   fuzz/core-set.txt × seeds 1..3, assert format(perturbed) ==
#   format(original). Perturbations are parse-preserving trivia mutations
#   (perturb.py, with the content pins); a seed whose mutation breaks the
#   parse is filtered (the exe reports a parse warning and ships identity —
#   not a divergence).
#
#   The corpus is this repository's own source tree: the formatter fuzzes
#   itself. Env: LEAN4FMT_EXE overrides the exe (default: ./result/bin, then
#   .lake/build/bin).
#
#   Usage:  fuzz/fuzz-core.sh          # from anywhere
#   Exits nonzero if divergences exceed the pinned baseline in
#   fuzz/core-baseline.txt (missing baseline = 0).
# ─────────────────────────────────────────────────────────────────────────────
set -uo pipefail
repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo"
exe="${LEAN4FMT_EXE:-}"
if [ -z "$exe" ]; then
  for candidate in result/bin/lean4fmt .lake/build/bin/lean4fmt; do
    [ -x "$candidate" ] && { exe="$candidate"; break; }
  done
fi
[ -n "$exe" ] && [ -x "$exe" ] || { echo "build lean4fmt first (nix build / lake build)"; exit 2; }

list="fuzz/core-set.txt"
baseline=$(cat fuzz/core-baseline.txt 2>/dev/null || echo 0)
div=0 runs=0 filtered=0
tmp="$(mktemp -u).lean"
while IFS= read -r f; do
  [ -f "$f" ] || { echo "missing: $f" >&2; continue; }
  orig="$("$exe" --lake off "$f" 2>/dev/null)"
  for seed in 1 2 3; do
    python3 fuzz/perturb.py "$f" "$seed" > "$tmp" 2>/dev/null || continue
    err="$("$exe" --lake off "$tmp" 2>&1 >/dev/null)"
    if echo "$err" | grep -q 'warning \[parse\]'; then filtered=$((filtered+1)); continue; fi
    pert="$("$exe" --lake off "$tmp" 2>/dev/null)"
    runs=$((runs+1))
    if [ "$orig" != "$pert" ]; then div=$((div+1)); echo "DIVERGE seed=$seed $f"; fi
  done
done < "$list"
rm -f "$tmp"
echo "// core-fuzz: $runs runs, $filtered filtered, divergences=$div (baseline $baseline)"
[ "$div" -le "$baseline" ] || exit 1
