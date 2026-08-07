#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
#                                              // LEAN4FMT // MATHLIB CENSUS
# ─────────────────────────────────────────────────────────────────────────────
#
#   The campaign instrument (CAMPAIGN.md): coverage + ceiling + gate outcomes
#   + the byte-weighted opt-out queue over a stratified mathlib sample.
#   Read-only on mathlib.
#
#     src/lean4fmt/mathlib-census.sh [N-per-dir|all|@file-list] [clearances]
#                                                    # default 2 (~55 files)
#
#   Env: MATHLIB=checkout (default ~/src/vendor/mathlib4). The exe is built
#   from THIS tree under MATHLIB'S pinned toolchain via elan (olean formats
#   are version-locked; both build AND run must go through `elan run` or
#   findSysroot picks a mismatched core). Build cached per (git-rev,
#   toolchain) under ~/.cache/lean4fmt-census.
#
#   MATHLIB_CENSUS_JOBS controls file-level parallelism. `all` defaults to half
#   the available CPUs (capped at 16); samples default to 2. Set
#   MATHLIB_CENSUS_RES to a stable directory to resume an interrupted run.
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
CLEARANCES=""
if [ "$#" -ge 2 ]; then CLEARANCES="$(realpath "$2")"; fi
LIST_PATH=""
if [[ "$PER" == @* ]]; then LIST_PATH="$(realpath "${PER#@}")"; fi

TC="$(cat "$ML/lean-toolchain")"
rev="$(git -C "$here" rev-parse --short HEAD 2>/dev/null || echo dev)"
tree_hash="$({ find "$here" -type f -not -path '*/.lake/*' -not -path '*/.lean4fmt/*' \
  -not -path '*/fuzz/*' -print0 |
  sort -z | xargs -0 sha256sum; } | sha256sum | cut -c1-12)"
cache="${XDG_CACHE_HOME:-$HOME/.cache}/lean4fmt-census/$rev-$tree_hash-${TC//[:\/]/_}"
EXE="$cache/.lake/build/bin/lean4fmt"

if [ ! -x "$EXE" ]; then
  echo "// census: building lean4fmt@$rev under $TC (cached: $cache)"
  rm -rf "$cache"; mkdir -p "$cache"
  rsync -a --exclude='.lake' --exclude='fuzz' "$here/" "$cache/"
  echo "$TC" > "$cache/lean-toolchain"
  (cd "$cache" && elan run "$TC" lake build 2>&1 | tail -2) || exit 2
fi

RES="${MATHLIB_CENSUS_RES:-$(mktemp -d)}"; mkdir -p "$RES"; RES="$(realpath "$RES")"; export RES
manifest="revision=$rev tree=$tree_hash toolchain=$TC mode=$PER"
if [ -f "$RES/manifest" ] && [ "$(cat "$RES/manifest")" != "$manifest" ]; then
  echo "census result manifest mismatch: $RES" >&2
  echo "  have: $(cat "$RES/manifest")" >&2
  echo "  want: $manifest" >&2
  exit 2
fi
printf '%s\n' "$manifest" > "$RES/manifest"
cd "$ML"
CORE="$(elan run "$TC" lean --print-libdir)"
LP="$ML/.lake/build/lib/lean"
for p in "$ML"/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
export LEAN_PATH="$LP:$CORE" EXE TC

echo "// census: results in $RES"

files=()
if [ -n "$LIST_PATH" ]; then
  while IFS= read -r f; do
    if [ -n "$f" ]; then files+=("$f"); fi
  done < "$LIST_PATH"
  cpu_count="$(nproc 2>/dev/null || echo 2)"
  default_jobs=$((cpu_count / 2))
  if [ "$default_jobs" -lt 2 ]; then default_jobs=2; fi
  if [ "$default_jobs" -gt 16 ]; then default_jobs=16; fi
elif [ "$PER" = all ]; then
  while IFS= read -r f; do files+=("$f"); done < <(find Mathlib -name '*.lean' | sort)
  cpu_count="$(nproc 2>/dev/null || echo 2)"
  default_jobs=$((cpu_count / 2))
  if [ "$default_jobs" -lt 2 ]; then default_jobs=2; fi
  if [ "$default_jobs" -gt 16 ]; then default_jobs=16; fi
else
  for d in Mathlib/*/; do
    while IFS= read -r f; do files+=("$f"); done \
      < <(find "$d" -maxdepth 1 -name '*.lean' | sort | head -"$PER")
  done
  default_jobs=2
fi
JOBS="${MATHLIB_CENSUS_JOBS:-$default_jobs}"
echo "// census: ${#files[@]} files, 2 passes each, jobs=$JOBS"

runone() {
  f="$1"; slug="${f//\//_}"
  if [ -f "$RES/$slug.done" ]; then return 0; fi
  stats_tmp="$RES/$slug.out.tmp.$$"
  debug_tmp="$RES/$slug.err.tmp.$$"
  if timeout 180 elan run "$TC" "$EXE" --style mathlib --stats --lake off "$f" \
      > "$stats_tmp" 2>/dev/null \
      && timeout 180 elan run "$TC" "$EXE" --style mathlib --log-level debug --lake off "$f" \
        > /dev/null 2> "$debug_tmp"; then
    mv "$stats_tmp" "$RES/$slug.out"
    mv "$debug_tmp" "$RES/$slug.err"
    touch "$RES/$slug.done"
  else
    rm -f "$stats_tmp" "$debug_tmp"
    echo "$f" >> "$RES/failures"
    return 1
  fi
}
export -f runone
run_status=0
printf '%s\n' "${files[@]}" | xargs -P "$JOBS" -I{} bash -c 'runone "$1"' _ {} || run_status=$?

status="$run_status"
if [ -n "$CLEARANCES" ]; then
  python3 "$here/mathlib-census.py" "$RES" "$CLEARANCES" || status=$?
else
  python3 "$here/mathlib-census.py" "$RES" || status=$?
fi
echo "// census: raw results kept in $RES"
exit "$status"
