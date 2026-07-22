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
| 2026-07-23 | 55 (2/dir) | 77.2% | 77.2% | 90.1% of code | **85.8%** | 0 (Phase 2 closed: shape payload 42KB → 5.3KB; structure defaults fix-forward after a caught -3.1 regression) |
| 2026-07-23 | 55 (2/dir) | 78.0% | 78.0% | 90.1% of code | **86.7%** | 0 (Phase 3: variable port + bracketed-binop family w/ per-link parent-op threading) |
| 2026-07-23 | 55 (2/dir) | 78.0% | 78.0% | 90.1% of code | **86.7%** | 0 (suffices position-split + tacticHave over-guard drop; run's stopping point — residue queue in the memory/next-round notes) |
| 2026-07-23 | **249 (10/dir)** | 74.0% | 71.8% | 88.2% of code | **81.4%** | 5: 3 tokens, 1 fixed-point, 1 comments (the wide baseline — 55-sample was ~5pt flattering; drill list: Fixed, CosetCover, Determinant, Induced, Algebraize) |
| 2026-07-23 | **249 (10/dir)** | 74.3% | 74.3% | 88.2% of code | **84.2%** | **0 — GATE 1 CLOSED** (seven mechanisms: anonymous-ident injection, byTactic' descent, head-ws law, simpa naive-join, paren master-class, doMatch block-blindness, + round-1 pair) |
| 2026-07-23 | 249 (10/dir) | 75.0% | 75.0% | 88.2% of code | **85.1%** | 0 (comma-less structInst vertical form + leftEdgeText? brace glue at 3 seams; sepByIndent colGe law) |
| 2026-07-23 | 249 (10/dir) | 76.2% | 76.2% | 88.2% of code | **86.4%** | 0 (obtain port + isBinOp namespace-blind — the scoped-operator sleeper: ≫/⟶ families + every chain containing one) |
| 2026-07-24 | 249 (10/dir) | 74.4% | 74.4% | 88.2% of code | 84.4 REGRESSION | 0 (induction shadow-handler: wrong arm shape sent every arm verbatim — census caught it; always grep for an existing handler) |
| 2026-07-24 | 249 (10/dir) | 77.1% | 76.1% | 88.2% of code | 86.3 | 1 tree (semicolon-let; + per-arm induction seams, calc port w/ tokenJoinFlat? decision + step-column law) |
| 2026-07-24 | 249 (10/dir) | 77.1% | 77.1% | 88.2% of code | **87.4%** | 0 (paren-by glue + calc head-ws guard; Divisors cleared) |
| 2026-07-24 | 249 (10/dir) | 77.3% | 77.3% | 88.2% of code | **87.7%** | 0 (the fun round: glueFun in straylight, trailing-lambda + match-body glue, vertical relaxation; 58 home files re-canonicalized, fuzz 5→4) |
| 2026-07-24 | 249 (10/dir) | 77.6% | 77.6% | 88.1% of code | **88.0%** | 0 (broken-head port + anon-have fix after a caught -1.1; cdot bullet comments; listFill house knob) |
| 2026-07-24 | 249 (10/dir) | 78.3% | 78.3% | 88.1% of code | **88.8%** | 0 (simp_rw family + induction arm comment seams; Ackermann 54.7→80.3) |
| 2026-07-24 | 249 (10/dir) | 78.6% | 78.6% | 88.1% of code | **89.2%** | 0 (rw multi-line rules walk) |
| 2026-07-24 | 249 (10/dir) | 78.7% | 78.7% | 88.1% of code | **89.3%** | 0 (tacticHave blanket comment bail dropped — the over-guard class) |
| 2026-07-24 | 249 (10/dir) | 78.7% | 78.3% | 88.1% of code | 88.8 | 1 fixed-point (instance round: broken-type heads take := values, empty where; CechNerve = the decision law at the instance type branch) |
| 2026-07-24 | 249 (10/dir) | 78.7% | 78.7% | 88.1% of code | **89.3%** | 0 (CechNerve cleared: instance type branch width-derived) |
| 2026-07-24 | 249 (10/dir) | 78.8% | 78.8% | 88.1% of code | **89.4%** | 0 (inductive ctor multi-line types walk; unified width criterion after a gate-caught pass-disagreement on home Http1) |
| 2026-07-24 | 249 (10/dir) | 78.9% | 78.9% | 88.1% of code | **89.5%** | 0 (obtain broken-type head) |
| 2026-07-24 | 249 (10/dir) | 78.9% | 77.2% | 88.1% of code | 87.6 | 2 tree (binder-comma family v1: respacing `∫ t in a..b,` flipped the longest-match notation — NEW LAW) |
| 2026-07-24 | 249 (10/dir) | 78.9% | 78.9% | 88.1% of code | **89.5%** | 0 (binder-comma heads source-exact; both rejects cleared) |
| 2026-07-24 | 249 (10/dir) | 79.0% | 79.0% | 88.1% of code | **89.6%** | 0 (with-source vertical structInst + brace-glue startsWith) |
| 2026-07-24 | 249 (10/dir) | 79.0% | 79.0% | 88.1% of code | **89.6%** | 0 (elab command port — ApplyAt 100.0 of portable; the meta cluster) |

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


## The four gates (set 2026-07-23, from the wide-249 baseline at 81.4)

All numbers are wide-census (10/dir, 249 files), shipped-of-portable, and
every gate additionally requires: home 401 / 0 fallbacks / 0 drift, fuzz at
baseline, comment-diff clean on every formatter-applied diff.

**GATE 1 — zero at width (≥ 83).** The five rejects drilled to zero:
`FieldTheory/Fixed`, `GroupTheory/CosetCover`, `LinearAlgebra/Determinant`
(tokens), `RepresentationTheory/Induced` (fixed-point), `Tactic/Algebraize`
(comments). Exit: wide rejects = 0, ≥ 83.

**GATE 2 — the term-value cluster (≥ 90).** The 208KB mountain:
`declValSimple` / `letIdDecl` / `fun` / `structInst` / `typeSpec` span
classes ported on the established recipes (own-line seam, by-tail glue,
flatten-first, position-split). Exit: cluster residue < 60KB, ≥ 90,
rejects 0.

**GATE 3 — the named tail (≥ 95).** calc (32KB, term+tactic), obtain
(32KB), have/suffices residue, induction, cdot, the over-guard sweep.
Exit: no single portable kind > 10KB in the wide queue, ≥ 95, rejects 0.

**GATE 4 — ceiling honest, tree locked (≥ 98 of the refined ceiling).**
Grind the 142-kind tail; reclassify measured correctly-verbatim-forever
kinds INTO the ceiling (per-kind, documented — never silently); full-tree
sweep (8,245 files) with rejects = 0; this census becomes a standing gate.
Exit: ≥ 98 of the reclassified ceiling at full width.

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
