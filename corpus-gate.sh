#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
#                                                    // LEAN4FMT // CORPUS GATE
# ─────────────────────────────────────────────────────────────────────────────
#
#   Reproducible correctness gate for the shipping lean4fmt exe over the
#   continuity corpus (all */Continuity/*.lean). Tests the invariant that matters
#   most: IDEMPOTENCE of the shipping tool — format(format x) == format(x),
#   byte-for-byte. The runtime safety gate (Frontend §4.2) already guarantees
#   reparse + token-preservation + fixed-point per file; this exercises it end to
#   end on real inputs and fails loudly on any drift.
#
#   Method: copy the corpus to a scratch tree, `--write` it twice, and diff the
#   two passes. A non-empty diff is a non-idempotence bug. Imports resolve by
#   module name against the in-tree package build dirs (no symlink farm needed).
#
#   Usage:  src/lean4fmt/corpus-gate.sh            # from repo root
#   Assumes the continuity packages and lean4fmt are already built (make core
#   lean4fmt). Exits nonzero on any non-idempotent file or formatter error.
# ─────────────────────────────────────────────────────────────────────────────
set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

exe="src/lean4fmt/.lake/build/bin/lean4fmt"
[ -x "$exe" ] || { echo "build first: make lean4fmt" >&2; exit 2; }

# LEAN_PATH: lean4fmt lib + every in-tree package build lib + lean core.
fmt_lib="$repo_root/src/lean4fmt/.lake/build/lib/lean"
pkg_libs="$(find "$repo_root/src" -type d -path '*/.lake/build/lib/lean' | tr '\n' ':')"
core_lib="$(lean --print-libdir)"
export LEAN_PATH="$fmt_lib:$pkg_libs$core_lib"

mapfile -t files < <(find src -path '*/Continuity/*' -name '*.lean' \
  -not -path '*/vendor/*' -not -path '*/.lake/*' | sort)
# CORPUS_LIMIT=N restricts to the first N files (quick smoke / CI subset).
if [ "${CORPUS_LIMIT:-0}" -gt 0 ] 2>/dev/null; then
  files=("${files[@]:0:$CORPUS_LIMIT}")
fi
echo "// lean4fmt // corpus-gate: ${#files[@]} files"

scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
for f in "${files[@]}"; do
  mkdir -p "$scratch/$(dirname "$f")"
  cp "$f" "$scratch/$f"
done

# Pass 1: format in place (against the original tree's LEAN_PATH for imports).
pass() { for f in "${files[@]}"; do "$exe" --write "$scratch/$f" >/dev/null 2>&1 || echo "$f"; done; }

echo "// pass 1 (format) ..."
p1_errors="$(pass)"
snapshot="$(mktemp -d)"; trap 'rm -rf "$scratch" "$snapshot"' EXIT
for f in "${files[@]}"; do mkdir -p "$snapshot/$(dirname "$f")"; cp "$scratch/$f" "$snapshot/$f"; done

echo "// pass 2 (re-format) ..."
p2_errors="$(pass)"

# Idempotence: pass-1 vs pass-2 must be byte-identical.
nonidem=0
for f in "${files[@]}"; do
  if ! diff -q "$snapshot/$f" "$scratch/$f" >/dev/null 2>&1; then
    nonidem=$((nonidem+1)); echo "NON-IDEMPOTENT: $f"
  fi
done

errs="$(printf '%s\n%s\n' "$p1_errors" "$p2_errors" | grep -c .)"
echo "// corpus-gate: files=${#files[@]} non-idempotent=$nonidem errors=$errs"
[ "$nonidem" -eq 0 ] && [ "$errs" -eq 0 ] && { echo "// corpus-gate: PASS"; exit 0; }
echo "// corpus-gate: FAIL" >&2; exit 1
