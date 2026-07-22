# The mathlib4 coverage campaign

Goal-ladder rung 3: **roundtrip mathlib4** — every portable code byte actively
formatted, zero gate fallbacks, idempotent, in mathlib-canonical form. This
document is the standing plan; the scoreboard updates per round.

The number that matters is **shipped-of-portable**: active bytes over
portable code bytes, where *shipped* zeroes gate-rejected files (they emit
identity — `--stats` alone counts the attempted emit and flatters) and
*portable* excludes content-by-policy bytes (module docstrings, headers,
quotation commands — permanently verbatim by design).

## The instrument

```sh
src/lean4fmt/mathlib-census.sh [N-per-dir]    # MATHLIB= to point elsewhere
```

Builds this tree under mathlib's pinned toolchain (elan, cached per rev),
runs a stratified sample two passes per file (`--stats` for byte attribution;
default mode + `--log-level debug` for gate outcomes and the opt-out trail —
stats mode suppresses both, by design), and aggregates: coverage, ceiling,
gate-reject classes, and the porting queue ranked by bytes with bail reasons.

## Scoreboard

| date | sample | attempted | shipped | portable ceiling | **shipped-of-portable** | rejects |
|------|--------|-----------|---------|------------------|-------------------------|---------|
| 2026-07-22 | 55 (2/dir) | 72.3% | 63.1% | 90.1% of code | **70.1%** | 6: 3 fixed-point, 2 tokens, 1 comments |
| 2026-07-23 | 55 (2/dir) | 72.2% | 72.2% | 90.1% of code | **80.1%** | **0** (Phase 1 closed) |
| 2026-07-23 | 55 (2/dir) | 74.9% | 74.9% | 90.1% of code | **83.2%** | 0 (defwhere round: by-field glue + sigDoc broken heads + flatten-first decision) |
| 2026-07-23 | 55 (2/dir) | 75.7% | 75.7% | 90.1% of code | **84.1%** | 0 (own-line opaque field values; defwhere-shape 26.0KB → 0.8KB total arc) |
| 2026-07-23 | 55 (2/dir) | 77.1% | 77.1% | 90.1% of code | **85.7%** | 0 (instance class closed: broken heads + own-line fields + Porting-note seams; 11.6KB → 0.7KB) |

Phase 1 closed in three rounds (nine mechanisms; see the round commits):
the mid-line verbatim drift law (chain/arm/let sites), the align effective
column, string-aware wrBlock, gate frontend alignment, cdot bullet anchor,
five content-guard zones. Bonus: the fallback counter exposed and purged SIX
silent HOME-corpus fallbacks (home now 401 files / 0 fallbacks / 0 drift,
85.3% active-of-portable). Shipped == attempted for the first time.

First instrumented reading (2026-07-22): the whole-declaration payload is
SHAPE-handlers, not comments — `defwhere-shape` 26.0KB + `instance-shape`
11.6KB + `structure-shape` 4.4KB vs `modifiers-comment` 1.3KB. Phase 2
therefore starts at `defWhereDoc?` and `instanceDoc?`. Next by bytes:
`declValSimple` spans (14.2KB `val-multiline`), typeSpec 7.9KB, then the
tactic tail (induction ×2 = 5.3KB, have 5.2KB, cdot 4.9KB, suffices 4.6KB).

## The phases

**Phase 0 — instruments** ✅ byte-weighted trail with bail reasons; walk
interception pops its stale entry; `--stats` ceiling accounting; this harness.

**Phase 1 — zero the whole-file losses.** Drill every gate reject with the
established kit (TOKDIFF/SPINEDIFF probes, writeFile-on-reject, reparse the
dump). Known targets: fixed-point ×4 (`Control/Applicative`, `Tactic/Abel`,
`Util/AddRelatedDecl`, `Data/List/Basic` — suspect: the reverted
simpa-`using` mechanism), tokens ×2 (`ArchimedeanDensely` — fillList-wrap
last-tactic drop — and `MeasureTheory/PiSystem`), comments ×1
(`Lean/ContextInfo`). Column-shaped root causes land as classes in
`Emit/WsSensitivity.lean`. *Exit: sample rejects = 0, home slice 0/100 holds.*

**Phase 2 — the declaration payload.** The whole-`Command.declaration`
verbatims are where the bytes are; the trail's `why=` tags bucket them into
classes (modifiers-comment, eqns-unformattable, unported-value-multiline,
…). Port or relax per class, poison-chain bisection for stragglers.
*Exit: whole-decl verbatims < 10 on the sample, remainder named-permanent.*

**Phase 3 — mathlib-native ports.**
- *Bracketed binops*: `isBinOp` routes `→ₗ[R]`/`→ₐ[R]`/`≃ₐ[R]`/`≫`/`≅` but
  the chain code expects 3-slot `[lhs, op, rhs]` and bails on the 5-slot
  bracket shape — generalize the chain, the family goes active at once.
- *`variable`* (trivial), *calc* term+tactic (taxonomy check first — step
  columns may be parser-read), the tactic tail
  (`suffices`/`have`/`rwSeq`/`simp_rw`/`obtain`/`haveI`) via the token-line /
  head-block recipes. *Exit: queue top-10 ported or policy-permanent.*

**Phase 4 — residue burn-down.** `declValSimple`/`typeSpec`/`letIdDecl`/
`doLetArrow` at mathlib density; extend the perturbation fuzzer to the
mathlib sample. *Exit: portable residue < 2% of code bytes.*

**Phase 5 — scale and lock.** Full-tree sweep (union import + pooled format;
mathlib is the co-importable shape), full gate at rejects=0, pin the mathlib
preset and run the conformance wash (roundtrip = mathlib-canonical form, not
imposed house style), lock this census as a standing gate.

## Standing rules (every round)

Home gate 234/234 · slice 0/100 · comment-diff on every formatter-applied
diff · core fuzz 0/120 · new column hazards → `WsSensitivity.lean` · new
kinds → the `Syntax/Kinds.lean` registry · toolchain pinned per round via
the census cache · never batch processHeader across files.
