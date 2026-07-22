#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
#                                              // LEAN4FMT // MATHLIB CENSUS
# ─────────────────────────────────────────────────────────────────────────────
#
#   The campaign instrument (CAMPAIGN.md): coverage + ceiling + gate outcomes
#   + the byte-weighted opt-out queue over a stratified mathlib sample.
#   Read-only on mathlib.
#
#     src/lean4fmt/mathlib-census.sh [N-per-dir]     # default 2 (~55 files)
#
#   Env: MATHLIB=checkout (default ~/src/vendor/mathlib4). The exe is built
#   from THIS tree under MATHLIB'S pinned toolchain via elan (olean formats
#   are version-locked; both build AND run must go through `elan run` or
#   findSysroot picks a mismatched core). Build cached per (git-rev,
#   toolchain) under ~/.cache/lean4fmt-census.
#
#   Two passes per file — --stats suppresses both the debug trail and gate
#   warnings (by design: stats is the attempted-emit accounting), so gate
#   outcomes and the opt-out trail come from a DEFAULT-mode pass with
#   --log-level debug, stdout discarded. The aggregator (mathlib-census.py)
#   zeroes gate-rejected files' active bytes: they ship identity.
# ─────────────────────────────────────────────────────────────────────────────
set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ML="${MATHLIB:-$HOME/src/vendor/mathlib4}"
PER="${1:-2}"
[ -d "$ML/Mathlib" ] || { echo "no mathlib checkout at $ML (set MATHLIB=)" >&2; exit 2; }

TC="$(cat "$ML/lean-toolchain")"
rev="$(git -C "$here" rev-parse --short HEAD 2>/dev/null || echo dev)"
cache="${XDG_CACHE_HOME:-$HOME/.cache}/lean4fmt-census/$rev-${TC//[:\/]/_}"
EXE="$cache/.lake/build/bin/lean4fmt"

if [ ! -x "$EXE" ]; then
  echo "// census: building lean4fmt@$rev under $TC (cached: $cache)"
  rm -rf "$cache"; mkdir -p "$cache"
  rsync -a --exclude='.lake' --exclude='fuzz' "$here/" "$cache/"
  echo "$TC" > "$cache/lean-toolchain"
  (cd "$cache" && elan run "$TC" lake build 2>&1 | tail -2) || exit 2
fi

cd "$ML"
CORE="$(elan run "$TC" lean --print-libdir)"
LP="$ML/.lake/build/lib/lean"
for p in "$ML"/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
export LEAN_PATH="$LP:$CORE" EXE TC

RES="$(mktemp -d)"; export RES
echo "// census: results in $RES"

files=()
for d in Mathlib/*/; do
  while IFS= read -r f; do files+=("$f"); done \
    < <(find "$d" -maxdepth 1 -name '*.lean' | sort | head -"$PER")
done
echo "// census: ${#files[@]} files, 2 passes each"

runone() {
  f="$1"; slug="${f//\//_}"
  timeout 180 elan run "$TC" "$EXE" --stats --lake off "$f" \
    > "$RES/$slug.out" 2>/dev/null
  timeout 180 elan run "$TC" "$EXE" --log-level debug --lake off "$f" \
    > /dev/null 2> "$RES/$slug.err"
}
export -f runone
printf '%s\n' "${files[@]}" | xargs -P 2 -I{} bash -c 'runone {}'

python3 "$here/mathlib-census.py" "$RES"
echo "// census: raw results kept in $RES"
