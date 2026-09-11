# The mathlib4 coverage campaign

This is the laboratory notebook for the Mathlib coverage campaign. It preserves
the hypotheses, regressions, instrument corrections, gate decisions, and final
ledger in chronological form. Read it as primary evidence, not as the current
architecture or a polished success narrative.

The campaign objective was to approach active formatting of every portable code
byte while retaining zero unclassified gate failures, idempotence, and
Mathlib-canonical output.

The number that matters is **shipped-of-portable**: active bytes over
portable code bytes, where *shipped* zeroes gate-rejected files (they emit
identity — `--stats` alone counts the attempted emit and flatters) and
*portable* excludes content-by-policy bytes (module docstrings, headers,
quotation commands — permanently verbatim by design).

## The instrument

```sh
./mathlib-census.sh [N-per-dir|all|@file-list] [clearances]
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
| 2026-07-22 | 249 (10/dir) | 80.2% | 80.2% | 88.1% of code | **91.0%** | **0 — GATE 2 CLOSED** (the null-wrapper unlock: the letIdDecl broken-type path never saw the optional slot's null wrapper, so EVERY multi-line-typed have/let bailed structurally — one fix, tacticHave 68K→27K, letIdDecl 62K→19K) |
| 2026-07-22 | 249 (10/dir) | 80.7% | 80.7% | 88.1% of code | **91.7%** | 0 (by joins ownsSeams — do's proof twin; fun-block glue at the binding seam; vertical structInst per-seam comment precision. The commented by-proof value class throughout) |
| 2026-07-22 | 249 (10/dir) | 81.1% | 81.1% | 88.0% of code | **92.1%** | 0 (quantifier heads wrap via headPieces? fillSep + BigOperators.bigsum/bigprod routed through the extended binder-comma branch; letIdDecl 19K→13K, tacticHave 21K→12K) |
| 2026-07-22 | 249 (10/dir) | 81.1% | 80.7% | 88.0% of code | 91.7 | 1 comments (structure Porting-note zone + eqns-form where-fields; the no-prefix zone double-emitted — ElementaryMaps) |
| 2026-07-22 | 249 (10/dir) | 81.1% | 81.1% | 88.0% of code | **92.1%** | 0 (zone only behind a docstring/modifier prefix; reject cleared same-round) |
| 2026-07-22 | 249 (10/dir) | 81.6% | 81.6% | 88.0% of code | **92.7%** | 0 (wide vertical-structInst fields break in-group + calc bare first step; the `{ base with` traverse-instance shape and the mathlib calc head form) |
| 2026-07-23 | 249 (10/dir) | 81.6% | 81.6% | 88.0% of code | **92.7%** (+0.07) | 0 (gate-3 round 1: alternative-pattern stacks via the shared arm loop + chain layout-level hasMidlineReanchor; Abel 75.6→81.2) |
| 2026-07-23 | 249 (10/dir) | 82.0% | 82.0% | 88.0% of code | **93.2%** | 0 (gate-3 round 2: Term.show port + simpa `using`-tail walk via pruneUsing? + exact/apply/refine layout hazard; paren general-content relaxation attempted and reverted — the half-verbatim mangle class) |
| 2026-07-23 | 249 (10/dir) | 82.3% | 82.3% | 88.0% of code | **93.6%** | 0 (gate-3 round 3: replace/letI/haveI join the have family + doMatch arm-leading seams + altPatternStack? extracted shared) |
| 2026-07-23 | 249 (10/dir) | 82.6% | 82.6% | 88.0% of code | **93.8%** | 0 (gate-3 round 4: alias port + doPatDecl/doLetArrow value glue — ten home files re-canonicalized) |
| 2026-07-23 | 249 (10/dir) | 82.8% | 80.2% | 88.0% of code | 91.1 REGRESSION | 5 (round 5 elabTail unwrap + chain glue: 3 fixed-point from a SOURCE-newline-derived glue decision, 1 tokens elab body parse floor, 1 comments elab prefix zone) |
| 2026-07-23 | 249 (10/dir) | 81.3% | 80.8% | 88.0% of code | 91.8 REGRESSION | 1 (round 6: naive-substring hasLineComment over `@[to_additive /-- -/]` attr text sent 13 files verbatim; OmegaLimit calc-glue tokens) |
| 2026-07-23 | 249 (10/dir) | 82.6% | 82.6% | 88.0% of code | **93.9%** | 0 (round 7: trivia-COUNT hazards + tailGlueSafe; all five rejects cleared — the newline-blind law, the elab parse-floor law) |

**INSTRUMENT CORRECTION (2026-07-23, round 9):** mathlib-census.py counted
only tagged `gate rejected output (…)` lines — the reparse-fail class has no
tag, and THREE files (Configuration, Applicative, Fold) had been silently
rejecting since before the campaign close. Every number above is ~1pt
flattered (the 92.7 close = **91.2 honest**). The aggregator now counts
reparse-fails; rows below are honest. Honest recompute of this run's rounds:
r2 91.7 · r3 92.1 · r4 92.4 · r7 92.8 · r8 93.4.

| 2026-07-23 | 249 (10/dir) | 83.1% | 82.2% | 88.0% of code | 93.4 honest | 2 HIDDEN (round 8: instance eqns-fields unlock — matchAltsOf needs the matchAlts CHILD of structInstFieldEqns; chain general layout restored with calc-tail fence) |
| 2026-07-23 | 249 (10/dir) | 83.2% | 83.2% | 88.0% of code | **94.6%** | **0 — both hidden rejects cleared** (round 9: chainOwnLine for structInst field let-values, eqns-arm fallback rides the .eqns +2-hardline placement (mirror-drift-proof), calc chain tails at line-start seams) |
| 2026-07-23 | 249 (10/dir) | 83.5% | 83.5% | 88.0% of code | **94.9%** (94.86) | 0 (round 10: Term.letI/haveI join the let/have chain arm — the local-instance ladders) |
| 2026-07-23 | 249 (10/dir) | 83.5% | 83.5% | 88.0% of code | **94.9%** (94.93) | 0 (round 11: doLetElse port — the a[8] slot is the do-block CONTINUATION; width-derived one-liner) |
| 2026-08-02 | **249 (10/dir)** | 83.6% | 83.6% | 88.1% of code | **94.9%** | 0 (fresh post-snake baseline on mathlib4 `308db4b`, Lean `v4.32.0-rc1`) |
| 2026-08-02 | 249 (10/dir) | 83.6% | 83.6% | 88.1% of code | **94.9%** | 0 (comment-bearing `doLetElse` continuations: +721 active bytes; the continuation seam already owns their trivia) |
| 2026-08-02 | 249 (10/dir) | 83.7% | 83.7% | 88.1% of code | **95.0%** | 0 (multiline `show` types compose with the structural term emitter: +1,129 active bytes; `show-type-shape` 1,480B → 0) |
| 2026-08-02 | **249 (10/dir)** | **84.1%** | **84.1%** | 88.0% of code | **95.6% — GATE 3 CLOSED** | **0** (set-builder + anonymous bindings; direct `doIf` arrow values; owned declaration-value seams; active modifier wrappers around opaque structure/`where` children; executable per-kind clearances) |

### 2026-08-02 effort/coverage probe

Two narrow rounds measured the late-curve slope on the legible snake tree.
The baseline carried 2,006,433 active bytes. The `doLetElse` round moved that
to 2,007,154 (+721): its apparent 5.6KB queue prize was nested double-counting,
and activating the outer continuation exposed 3.8KB of inner `doLetArrow`
residue. The `show` round moved active bytes to 2,008,283 (+1,129) without a
home-tree wash; it also reduced nested `paren` and `fun` residue. Both rounds
kept 249/249 parsed, zero gate rejects, formatter fixed point, comment multiset,
and Lean recompilation on the affected mathlib files.

Gate 3 is now closed at its stricter executable fixed point: 95.5 minimum
shipped-of-portable, zero rejects, and exact non-increase clearances for the
five former blockers. Their measured residues are `declaration` 3,521B,
`letIdDecl` 6,261B, `declValSimple` 1,310B, `doLetArrow` 5,640B, and
`tacticHave` 4,313B. Queue bytes remain dependency-weighted upper bounds, not
additive coverage estimates.

## GATE-3 RUN PAUSED at 94.93 (2026-07-23)

Stop rule: rounds 10→11→11b gained +0.26/+0.00/+0.08 — two consecutive
rounds under the 0.15 floor. 0.07 from the gate, zero rejects, zero
per-file drops, home 402/0/0 self-enforcing throughout. The HONEST arc of
this run (post-instrument-fix): 91.2 → 94.93 (+3.7). Residue queue at
ef70f49 (non-policy): declValSimple ~15K (diffuse inner-kind bails, avg
~210B/site), declaration ~14K (structure/defwhere-shape drills),
letIdDecl ~14K + tacticHave ~12K (the Dioph set-builder types — a setOf
port is the unlock), typeSpec 8K, syntax 7.8K (G4 policy candidate),
paren 7.3K, simpa 5.2K, cdot 5K, macro 4.9K, mutual 4.3K (x2),
typeAscription 3.5K, compNotation 3.2K. Any one of the top three pools
half-cleared closes the gate.

## CAMPAIGN CLOSED (2026-07-22, at 92.7)

Closed by priority re-ranking, not exhaustion: the formatter is now a
daily-drivable mathlib-grade tool — 92.7 shipped-of-portable on the
wide-249 census, zero gate rejects, home tree 402/0/0 self-enforcing,
and the failure mode is provably "unformatted", never "damaged". Gates
3–4 (95 / 98-of-refined) are PARKED with the ranked residue queue
recorded above and in the memory notes; the census harness is in-tree
(mathlib-census.sh + census-chunk.sh + mathlib-census.py +
comment_check.py) and reruns in ~15 min whenever the climb resumes.
What this campaign leaves behind for the next program: a formatter that
roundtrips proof code safely, the WsSensitivity law set, and the
instrument.

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

## The closing plan (set 2026-07-22 at 89.6; supersedes the phase list)

Phases 0–3 closed inside Gates 1–2 (the round commits and scoreboard carry
the history). What remains is a ranked burn-down. Measured at 086258c:
**gap to 90.0 = 8.7K active bytes; gap to 95.0 = 114.7K** (portable pool
2.12MB). Every round is the same monotone loop:

1. Pick top-of-queue targets, **≤ 3 ports per census round**.
2. Sample real sites from the latest census `.err` trail (grep the opt-out
   kind, read the mathlib lines) — never port from an imagined shape.
3. Port on the established laws: flat-vs-broken decisions width/parse-derived
   only; unknown notation heads source-exact; inner machinery over blanket
   bails; precise hazards over guards.
4. Home battery: `scripts/lean4fmt.sh --check src` 401/0/0 · fuzz-core ≤ 4 ·
   comment_check on every formatter diff · converge.
5. Census; aggregate with `mathlib-census.py`; **any drop → per-file mover
   diff before anything else**; outcome greps must cover all variants
   ('gate rejected', 'falling back').
6. Scoreboard row, commit (`git commit -F -` heredoc), push.

**Gate 2 close (89.6 → ≥ 90.0, 1–2 rounds).** The queue's top two pools are
residual shapes of ported classes: `tacticHave__` 68K, `letIdDecl` 61K
(nested opt-outs double-count; still the biggest live pools by far).
R1: classify the top 2 tacticHave shapes from sites and port — a third of
the pool overshoots the gate. R2 if needed: letIdDecl shapes. No ceiling
reclassification inside G2 — the 90 is absolute; quotation-only bodies stay
in the denominator until G4. *Exit: ≥ 90.0, rejects 0, home clean.*

**Gate 3 (90 → ≥ 95, ~6–8 rounds).** Ranked queue at 086258c:
- R3 — finish the tacticHave / letIdDecl pools (comment-bearing + interior
  forms).
- R4 — `declaration` whole-verbatims (27.5K) + `declValSimple` (21.7K):
  bucket by why= tags; port-or-name-permanent per bucket.
- R5 — `paren` interiors (16.3K), `structInst` residue (13.0K), `typeSpec`
  (12.6K).
- R6 — the do-cluster: `letDecl` (8.6K), `doMatch` (7.6K), `doLetArrow`
  (7.0K).
- R7 — the tactic tail: `calcTactic` residue (8.3K), `simpa` +
  `simpaUsingBang` (12.3K), `replace` (6.8K), `exact` (6.0K), `show`
  (5.6K), `cdot` residue (6.1K).
- R8 — chain residue: `«term_<|_»` (7.4K), `«term_=_»` (4.4K), remaining
  5-slot shapes.
- R9 — cross-cutting sweeps: enumerate every remaining blanket
  `interiorHasLineComment` / `hasMultilineReanchor` bail and replace with
  precise hazards (the over-guard pattern, proven ×3); block-comment
  blindness sweep.
*Exit: ≥ 95.0, no portable kind > 10K in the queue, rejects 0, home clean.*

**Gate 4 (ceiling honest, tree locked, ≥ 98 of refined ceiling).**
- R10 — per-kind ceiling reclassification, documented, never silent:
  `elab`/`elabTail`/`syntax`/`macro`/`alias` quotation-only bodies (~34K
  pool; criterion: measured no-portable-spelling — the 13 worst files, the
  Tactic/Util meta cluster at 1–25%, are THIS, not port targets).
- R11 — full-tree sweep, 8,245 files, chunked over the census cache;
  rejects must be 0; drill any straggler with the standard kit.
- R12 — mathlib conformance wash: roundtrip = mathlib-canonical form, not
  imposed house style; pin the mathlib preset.
- R13 — lock: the census becomes a standing gate (make target), scoreboard
  frozen.
*Exit: ≥ 98 of the refined ceiling at full width, full tree rejects 0.*

## Standing rules (every round)

Home gate 234/234 · slice 0/100 · comment-diff on every formatter-applied
diff · core fuzz 0/120 · new column hazards → `WsSensitivity.lean` · new
kinds → the `Syntax/Kinds.lean` registry · toolchain pinned per round via
the census cache · never batch processHeader across files.

## Gate 4 full-tree ledger (2026-08-02)

The standing instrument now accepts `all` and resumable `@file-list` runs,
uses content-addressed formatter builds, records atomically completed files,
and rejects missing stats. `mathlib-full-gate` pins the full-tree clearance.
R12 also corrected the instrument itself: both passes now run `--style mathlib`.

The first 8,245-file census parsed every file with zero missing stats and found
241 safety-gate rejects under the old style invocation. Replaying that exact
frontier with the mathlib style and the binder default-order fix reduced it to
192. The current monotone clearances reduce the same frozen frontier to zero:
multiline container children cannot be relocated, adjacency-sensitive
applications stay opaque, and declarations preserve interior comments plus
the modifier seams that own ordinary block comments. Shift notation,
parenthesized projection, nested `calc`, padded parentheses, and multiline
anonymous constructors now have explicit conservative owners.

Current frozen-frontier result:
`.lean4fmt/mathlib-rejects-zero-candidate` — 192 parsed, zero missing stats,
zero rejects, 55.9% attempted and shipped code-active, and 90.8% portable
ceiling. Layout-sensitive `ℓ^p` notation, type-level `letI`, zero-column
structure literals, semantic whitespace in token payloads, termination
suffixes, and constructor-valued instances now have explicit owners.

The fresh `.lean4fmt/mathlib-full-zero-confirmation` discovery pass completed
all 8,245 files with zero missing stats: 67.2% attempted, 66.4% shipped, 89.3%
portable ceiling, and 47 rejects (16 reparse, 24 fixed-point, 6 token, 1 tree).
The full 47-file discovery frontier is now green:
`.lean4fmt/mathlib-full-frontier-zero` parsed all 47 with zero missing stats and
zero rejects, at 73.0% attempted/shipped active and 90.0% portable ceiling.
The new owner laws cover nested structure fields, inline `have` values,
multiline signature/binder continuations, function/`let` values,
layout-sensitive `where` fields, same-line attributes, and constructor/tuple
patterns whose whitespace changes macro shape.

Gate 4 is closed. The fresh
`.lean4fmt/mathlib-full-confirmation-aa6b151` production pass parsed all 8,245
files with zero missing stats and zero gate rejects: 70.7% attempted/shipped
code-active, 87.4% portable ceiling, and 80.9% shipped-of-portable. Both
required monotone clearances—the frozen frontier and an independent fresh
full-tree run—are zero.

## Post-Gate-4 accounting correction and frontier curve (2026-08-03)

The Gate 4 safety result remains valid, but its coverage percentages were
inflated: `source_exact` logged an opt-out and then returned `.textRaw`, whose
bytes the stats algebra classifies as active. It now returns `.verbatim` at
base indent zero, preserving identical output while charging the fallback to
the verbatim column. The old 70.7% / 80.9% figures above are retained as the
historical ledger, not as current coverage claims.

On the identical stratified 249-file cohort, honest accounting reports 53.9%
code-active and 60.6% shipped-of-portable, with 249/249 files green. Removing
the blanket `multiline-signature` fallback raises those to 56.7% and 63.8%
with 249/249 green. Widening to 708 files found one fixed-point drift: a nested
`forall` signature gained one binder indent per pass. Replacing the blanket
guard with the precise `signature-nested-forall` hazard closes 708/708 at
57.4% code-active and 64.5% shipped-of-portable.

Measured frontier cost for this slice: one accounting correction, one blanket
guard deletion, and one named 46,015-byte hazard recover 59,785 active bytes
in the paired 249-file cohort while introducing and clearing one new
syntax-family failure in 708 files. A fresh full-tree run is required before
extrapolating these cohort percentages to all of mathlib.

The next independent clearance removed `binder-continuation`. It remained on
the favorable slope: 249/249 closed at 57.6% code-active and 64.8%
shipped-of-portable; the widened gate closed 708/708 with zero rejects at
58.3% and 65.7%. No replacement hazard was required.

Opening the blanket `paren-projection` fallback raised the paired cohort to
60.8% / 68.4%. The first 708-file run exposed two fixed-point projection
chains. A layout-derived `multiline` predicate was rejected because it changed
routing between passes; token-stable chain predicates preserve only the two
unowned seams. The final widened gate closes 708/708 at 61.8% code-active and
69.6% shipped-of-portable.

Removing `function-have-value` remained independently green: 249/249 reached
62.1% code-active and 69.9% shipped-of-portable; 708/708 reached 63.0% and
70.9%. This ends the cheap declaration-owner run. The next measured pools are
cross-cutting hazards (`decl-line-comment` and `application-adjacency`) and
should begin with shape bucketing rather than another blanket deletion.

Scouting found one final broad declaration heuristic before that boundary:
`constructor-pattern` matched any declaration containing `fun ⟨` and any
comma anywhere. Removing it closes 249/249 at 63.4% / 71.4% and 708/708 at
64.4% code-active / 72.5% shipped-of-portable, with zero replacement hazards.

The first architectural clearance removes the declaration-wide
`decl-line-comment` fallback. Existing local owners already covered modifier,
equation-arm, `where`-field, do-statement, and value-leading seams. Two missing
laws were added: binder-leading comments force the seam-materializing
`onePerLine` signature layout, and a pattern-or-else branch reappends its
same-line trailing comment before the scoped continuation. The final widened
gate closes 708/708 at 66.8% code-active and 75.4% shipped-of-portable; the
348 KB `decl-line-comment` pool is gone from the queue.

The adjacency clearance replaces the whole-application bailout with a seam
vector. Each seam is the complete trivia gap (previous token trailing plus
next argument leading): empty gaps remain unbreakably glued; nonempty gaps are
breakable application lines. One structural exception remains for applications
containing shorthand structure fields, whose field grammar is indentation
sensitive. The final gate closes 249/249 at 71.3% / 80.6% and 708/708 at 71.0%
code-active / 80.3% shipped-of-portable. `application-adjacency` is gone; the
precise `application-struct-shorthand` residue is 16,485 bytes.

Typed instance chains no longer require declaration-wide opacity. Removing
`type-haveI` closes 249/249 at 72.7% / 82.2% and 708/708 at 72.9%
code-active / 82.6% shipped-of-portable, with no replacement hazard.

Inline and vertically nested structure values no longer require blanket
declaration opacity. The one exposed counterexample was a comma-less structure
literal whose fields are aligned by source column: moving the declaration seam
reanchored its still-opaque child and changed the field grammar. A precise
parent/child `decl-struct-value-reindent` owner preserves only that composition
boundary. The final gates close 249/249 at 72.9% code-active / 82.5%
shipped-of-portable and 708/708 at 73.2% / 82.8%, with zero rejects.

Same-line declaration attributes are owned by the existing modifier/declaration
composition and need no declaration-wide exception. Removing
`same-line-attribute` closes 249/249 at 73.9% code-active / 83.6%
shipped-of-portable and 708/708 at 74.0% / 83.8%, with zero rejects and no
replacement hazard.

Equation-style declarations whose arms end in tactic bodies are already owned
by the equation-arm and tactic-body composition. Removing
`equation-tactic-body` closes 249/249 at 74.4% code-active / 84.2%
shipped-of-portable and 708/708 at 74.4% / 84.2%, with zero rejects and no
replacement hazard.

Termination suffixes are likewise owned by the declaration value/suffix
composition. Removing `termination-suffix` closes 249/249 at 74.6%
code-active / 84.4% shipped-of-portable and 708/708 at 74.4% / 84.3%, with
zero rejects and no replacement hazard.

Function-valued instance declarations require no instance-wide suffix bailout.
Removing `instance-function-suffix` closes 249/249 at 74.7% code-active /
84.5% shipped-of-portable and 708/708 at 74.7% / 84.5%, with zero rejects and
no replacement hazard.

Constructor-valued instances also require no declaration-wide layout bailout.
Removing `instance-constructor-layout` is coverage-neutral—the active residue
already belongs to smaller constructor and structure owners—and closes both
249/249 and 708/708 at 74.7% code-active / 84.5% shipped-of-portable, with zero
rejects.

Old-style `:=` declarations whose structure literal begins at column zero now
enter the ordinary structure/value routes. Their syntax boundary is explicit;
canonical indentation no longer needs a declaration-wide fence. This removes
`zero-column-structure`: the focused witness closes at 85.1% code-active /
92.2% shipped-of-portable, 249/249 at 80.8% / 91.6%, widened 566/566 at 80.6%
/ 91.3%, and home at 84.1% / 89.0%, with zero rejects.

Function values containing destructuring `let` terms are owned by the existing
function/let composition. Removing `function-let-value` closes 249/249 at
74.8% code-active / 84.6% shipped-of-portable and 708/708 at 74.8% / 84.7%,
with zero rejects and no replacement hazard.

Inline `have` declaration values need no declaration-wide bailout. Removing
`inline-have-value` is coverage-neutral—the smaller have/tactic owners already
account for every sampled occurrence—and closes 249/249 at 74.8% / 84.6% and
708/708 at 74.8% / 84.7%, with zero rejects.

The source-spelling-specific `multiline-binder-type` declaration guard is also
unnecessary: binder layout already owns the seam. Removing it closes 249/249 at
74.8% code-active / 84.7% shipped-of-portable and 708/708 at 74.8% / 84.7%,
with zero rejects and no replacement hazard.

Where-fields whose values begin with `let` are owned by the existing
where-field/value composition. Removing `where-let-field` closes both 249/249
and 708/708 at 74.8% code-active / 84.7% shipped-of-portable, with zero rejects
and no replacement hazard.

The declaration-wide `padded-anonymous-ctor` heuristic is dead policy: the
remaining constructor residue is charged to the smaller `trailing-comma` owner.
Removing it is coverage-neutral and closes both 249/249 and 708/708 at 74.8%
code-active / 84.7% shipped-of-portable, with zero rejects.

Padded negations need no declaration-wide spelling guard. Removing
`padded-negation` closes 249/249 at 75.0% code-active / 84.9%
shipped-of-portable and 708/708 at 74.9% / 84.8%, with zero rejects and no
replacement hazard.

Fill-layout signatures with multiline type documents are owned by the binder
and type layout composition. Removing `fill-multiline-type` closes 249/249 and
708/708 at 75.1% code-active / 85.0% shipped-of-portable, with zero rejects and
no replacement hazard.

Value suffixes containing multiline docstrings now compose locally: the suffix
comment token rides a column-stable raw doc while the declaration and value stay
active. The widened probe exposed one token-payload counterexample
(`Tactic/DefEqAbuse`), which this local law clears. Final gates close 249/249 at
75.1% / 85.0% and 708/708 at 75.1% / 85.1%, with zero rejects; the remaining
`val-suffix-docstring` charge is only the semantic comment token itself.

The first `defwhere-body` subclearance adds the missing shorthand-field grammar
case (`... where app`): a field with no definition or equations is its head.
Both 249/249 and 708/708 remain zero-reject at 75.1% / 85.1%; the wide residue
falls from 6,299 to 6,107 bytes. G3 remains open for the next unsupported field
shape.

Authored trailing commas in collection literals and anonymous constructors are
now explicit list-body tokens and survive both flat and broken layouts. The old
`trailing-comma` pool was an instrumentation conflation: all 23,558 wide bytes
were actually constructors containing multiline opaque children, now named
`anonymous-ctor-multiline-piece`. The clearance is coverage-neutral and closes
249/249 and 708/708 at 75.1% / 85.1%, with zero rejects.

Structure bodies now own empty `where` blocks, explicit constructor declarations,
instance fields, and parenthesized explicit fields. The type-declaration fallback
also distinguishes `inductive-body` from `structure-body`, making the next
grammar frontier explicit instead of conflating it with structures. The final
gates close 249/249 at 75.2% code-active / 85.1% shipped-of-portable and the
widened 566/566 cohort at 75.2% / 85.0%, with zero rejects; the home corpus closes
234/234 with zero errors and zero fixed-point drift.

Equation-defined instances now reuse the declaration equation-arm algebra, so
their patterns and bodies remain active under the same alignment and comment
laws as `def` equations. The old `instance-shape` bucket is empty on both
cohorts; unsupported large structural instance values are now isolated as
`instance-where-body`. Final gates close 249/249 and widened 566/566 at 75.2%
code-active / 85.2% and 85.1% shipped-of-portable respectively, while the home
corpus remains 234/234 with zero errors and zero fixed-point drift.

Type declarations no longer carry declaration-wide or field-wide line-comment
vetoes. Constructor section comments, field Porting-note runs, and comments in
walked default proofs compose at their existing local seams; token-aware child
emitters retain authority to reject genuinely unsafe interiors. Removing the
coarse `type-decl-comment` gate closes 249/249 at 75.4% / 85.4% and widened
566/566 at 75.3% / 85.2%, with zero rejects. The home corpus rises sharply to
80.9% code-active / 85.6% shipped-of-portable and remains 234/234 green.

Block comments no longer trigger a declaration-wide lexical veto. Comments in
terms and tactic bodies are retained by the subtree walkers that own those
seams, while unsafe children continue to fall back locally. Removing
`decl-block-comment` closes 249/249 at 75.8% code-active / 85.8%
shipped-of-portable and widened 566/566 at 75.7% / 85.7%, with zero rejects; the
home corpus remains 234/234 green at 80.9% / 85.6%.

`... in` command wrappers now own only their prefix and the seam before the
walked child command; line and block comments inside that child remain under
the child's local emitters. Removing the wrapper-wide `command-in-layout` veto
closes 249/249 at 76.7% code-active / 86.9% shipped-of-portable and widened
566/566 at 76.7% / 86.8%, with zero rejects. Home remains 234/234 green at
81.0% / 85.7%.

Structure-instance values are now rendered by the existing column-relative
vertical field document instead of fenced at both the declaration seam and the
term root. The first parent-only attempt correctly failed the 249 gate on
`Order/BooleanSubalgebra`; removing the stale child veto made that witness
97.8% active and restored reparse. The joint clearance removes both
`decl-struct-value-reindent` and `struct-value-reindent`, closing 249/249 at
78.9% code-active / 89.5% shipped-of-portable and widened 566/566 at 78.7% /
89.1%, with zero rejects. Home rises to 81.8% / 86.6%, 234/234 green.

Nested `∀` continuations in declaration signatures now rely on the structural
signature/type documents rather than a source-newline fence. Binder and body
indentation is derived from the enclosing document on every pass, so the old
indent-growth hazard no longer exists. Removing `signature-nested-forall`
closes 249/249 at 79.6% code-active / 90.3% shipped-of-portable and widened
566/566 at 79.3% / 89.9%, with zero rejects; home remains 234/234 green at
81.8% / 86.6%.

The coarse `semantic-token-whitespace` pool is now split without changing
policy into `adaptation-note-whitespace`, `message-interpolation-whitespace`,
and `syntax-antiquotation-whitespace`. Direct structure-shorthand application
arguments now use the ordinary application seam law. The first widened run
caught HTML quotation syntax whose nested subtree merely resembles a shorthand
field; those custom-syntax interiors remain precisely fenced as
`nested-application-struct-shorthand`. Final gates close 249/249 at 80.3%
code-active / 91.2% shipped-of-portable and widened 566/566 at 79.9% / 90.5%,
with zero rejects; home remains 234/234 green at 81.8% / 86.6%.

Comma-list documents now accept multiline opaque children when the child has
no midline re-anchor: the broken list gives every child an owned line-start
seam. This shared law activates recursive anonymous constructors and multiline
collection elements while retaining the actual column hazard. Removing
`anonymous-ctor-multiline-piece` closes 249/249 at 80.3% code-active / 91.1%
shipped-of-portable and widened 566/566 at 79.9% / 90.6%, with zero rejects;
home remains 234/234 green at 81.9% / 86.6%.

The shared `where` body loop now delegates comments inside field values to the
value walker, preserves block-comment-bearing fields locally, and owns explicit
semicolon separators as terminators followed by a fresh field seam. Definitions
with a fully supported body but an unsafe header are now honestly charged as
`defwhere-signature`. Instance fields using `:= private name` preserve that
single-line field grammar atom whole—the focused token gate caught that
`private` belongs to the field-definition node, not the value child. Final gates
remove both `defwhere-body` and `instance-where-body`: 249/249 closes at 80.5%
code-active / 91.3% shipped-of-portable, widened 566/566 at 80.3% / 91.0%, and
home rises to 83.6% / 88.4%, 234/234 green.

Parenthesized terms now use a real bracket document: flat output remains `(x)`,
while a multiline interior breaks below `(` at an owned +2 seam and closes on
its own line. The universal midline-reanchor check subsumes the former special
cases for `by` and `do`; calc and projection-specific parser fences remain.
Removing `paren-multiline-piece` closes 249/249 at 80.3% code-active / 91.1%
shipped-of-portable and widened 566/566 at 80.0% / 90.6%, with zero rejects;
home remains 234/234 green at 81.9% / 86.6%.

Nested structure literals now recurse through the same column-relative
structure-field documents as top-level values. The declaration-wide spelling
heuristic for `{ toFun := ... }` and `{ obj ... }` was therefore redundant and
prevented safe recursive composition. Removing `nested-structure-fields`
closes 249/249 at 80.1% code-active / 90.9% shipped-of-portable and widened
566/566 at 79.9% / 90.5%, with zero rejects; home remains 234/234 green at
81.8% / 86.6%.

Nested application shorthand is now classified by its immediate parser seam.
Ordinary `choice` arguments such as `{s}` and `{i, j, k}` compose through the
application document; shorthand-shaped descendants of custom syntax such as a
`do` argument remain opaque because the outer macro may own significant
whitespace. The focused witnesses close 3/3, the 249 gate closes at 80.5%
code-active / 91.4% shipped-of-portable, and the widened 566 gate closes at
80.3% / 91.0%, all with zero rejects; home remains 234/234 green at 83.6% /
88.4%.

Comments nested inside a simple declaration value are now delegated to the
value walker. The enclosing `:=` form owns the line-start seam and may compose
an opaque multiline child unless that child actually re-anchors midline; a
comment-bearing value with a `where` suffix advances to the narrower
`val-suffix-multiline` frontier. This removes `val-comment`: the focused gate is
7/7 green, 249/249 closes at 80.5% code-active / 91.4%
shipped-of-portable, widened 566/566 at 80.3% / 91.0%, and home rises to 83.9%
/ 88.8%, with zero rejects throughout.

Binary chains now distinguish comments owned recursively by their operands from
comments attached to the operator-to-operand seam. Operand comments compose
through the existing walkers; the focused comment/token gate proved that a
right-operand leading comment still needs an explicit placement law, now named
`chain-seam-comment`. Removing coarse `chain-comment` closes the focused set
5/5, 249/249 at 80.6% code-active / 91.4% shipped-of-portable, widened 566/566
at 80.4% / 91.1%, and home at 84.0% / 88.9%, with zero rejects.

The former `modifiers-comment` pool is uniformly a modifier suffix-seam
hazard: an attribute or visibility token carries a same-line trailing comment
before the declaration keyword. It is now named `modifier-seam-comment`, the
missing algebraic operation being a suffix-bearing modifier piece rather than
generic comment support. The six-file classification gate, 249/249, widened
566/566, and home 234/234 all close with zero rejects; aggregate coverage holds
at 80.6% / 91.4%, 80.4% / 91.1%, and 84.0% / 88.9%, respectively.

Unsupported structures now report the layer that declined composition rather
than the declaration-wide `structure-body`: head, deriving clause, `where`
seam, empty body, fieldless form, or fields. The widened residue is 3,055 bytes
of `structure-fields` and 936 bytes of `structure-head`; the nine focused
witnesses, 249, 566, and home gates are all green with zero rejects. Coverage
holds at 80.6% / 91.4%, 80.4% / 91.1%, and 84.0% / 88.9%.

Unsupported inductives now distinguish head/layout failures from constructor
item failures. The widened residue is 921 bytes of `inductive-constructors`
and 294 bytes of `inductive-head`; declaration-wide `inductive-body` is gone.
The two focused witnesses, 249, 566, and home gates all close with zero
rejects, holding aggregate coverage at 80.6% / 91.4%, 80.4% / 91.1%, and
84.0% / 88.9%.

Structure field containers now compose multiline types with either inline or
multiline defaults. When an individual field grammar remains unsupported, the
field rides as an opaque line-start item while the structure head, neighboring
fields, comment seams, and alignment stay active. This removes
`structure-fields`: the nine focused witnesses close at 85.9% code-active /
93.8% shipped-of-portable, 249/249 at 80.6% / 91.4%, widened 566/566 at 80.4%
/ 91.1%, and home rises to 84.1% / 89.0%, with zero rejects.

Inductive constructor containers now apply the same line-start composition law
as structure fields: an unsupported constructor remains an opaque body item,
while the inductive head, sibling constructors, deriving clause, and comment
seams remain active. This removes `inductive-constructors`: the focused gate is
2/2 green at 78.8% code-active / 92.9% shipped-of-portable; 249/249, widened
566/566, and home remain green at 80.6% / 91.4%, 80.4% / 91.1%, and 84.1% /
89.0%, with zero rejects.

Binary operators now own a RHS-leading comment seam. The operator remains with
the left operand; the full-line comment run and right operand are nested at the
continuation indent, preserving every comment character without surrendering
the surrounding chain. This removes `chain-seam-comment`: the five focused
witnesses close at 60.2% code-active / 66.2% shipped-of-portable; 249/249,
widened 566/566, and home remain green at 80.7% / 91.5%, 80.4% / 91.2%, and
84.1% / 89.0%, with zero rejects.

Simple declaration values now compose a multiline opaque value with an owned
suffix separator. The `:=` form owns the value's line-start seam and each
suffix owns its own leading seam, so neither layer needs to absorb the other.
This removes `val-suffix-multiline`: the two focused witnesses are green;
249/249 closes at 80.7% / 91.5%, widened 566/566 rises to 80.5% / 91.2%, and
home remains 84.1% / 89.0%, with zero rejects.

Multiline docstring suffixes were already emitted as owned raw token content
behind a proved leading separator; a stale explicit opt-out charge mislabeled
that ownership as `val-suffix-docstring`. Removing the charge makes the
coverage algebra honest. The six focused files, 249/249, widened 566/566, and
home gates are green with zero rejects; aggregate coverage holds at 80.7% /
91.5%, 80.5% / 91.2%, and 84.1% / 89.0%.

Equation declarations now degrade per arm. When the shared active arm parser
declines a pattern, each alternative remains an opaque line-start item behind
its owned separator while the declaration signature and sibling arms remain
active. This removes declaration-wide `eqns-arm`; the two focused witnesses,
249/249, widened 566/566, and home gates all close with zero rejects at 80.7% /
91.5%, 80.5% / 91.2%, and 84.1% / 89.0% aggregate coverage.

`do match` alternatives now admit full-line block comments in their leading
seams. The shared separator algebra already preserves and re-anchors those
comments; the old parser-level veto was redundant. Removing
`doMatch-arm-block-comment` closes both focused witnesses, 249/249, widened
566/566, and home with zero rejects; 249 shipped-of-portable rises to 91.6%
and the aggregate remains 80.5% / 91.2% widened and 84.1% / 89.0% at home.

Definitions now own post-value suffix slots as line-start items. Standalone
`deriving` clauses compose after the formatted signature and value through
their syntax-derived leading separators; multiline unknown suffixes remain
opaque individually. This removes `defn-extra-slot`: focused, 249, widened
566, and home gates are green with zero rejects; widened shipped-of-portable
rises to 91.3% while 249 holds 91.6% and home holds 89.0%.

The spelling-specific `paren-projection-chain` fence is gone. Parenthesized
terms now own multiline interiors and projections/applications preserve their
syntax-derived seams, so the old `).antisymm <|` and measurable-equivalence
special cases compose through the ordinary documents. The ten focused
witnesses close at 83.2% code-active / 94.4% shipped-of-portable; 249/249,
widened 566/566, and home are green with zero rejects at 80.7% / 91.6%, 80.5%
/ 91.3%, and 84.1% / 89.0%.

Structure heads now flatten multiline binders, result types, and `extends`
clauses through token-preserving joins before entering the head document. This
removes `structure-head`: the five focused witnesses close at 90.1%
code-active / 94.1% shipped-of-portable, 249/249 at 80.7% / 91.6%, widened
566/566 at 80.6% / 91.3%, and home at 84.1% / 89.0%, with zero rejects.

Headless inductives now flatten multiline `deriving` syntax through the same
token-preserving join used by other portable head pieces. This removes
`inductive-head`: the focused witness rises to 82.7% code-active / 96.9%
shipped-of-portable, 249/249 closes at 80.8% / 91.6%, widened 566/566 at 80.6%
/ 91.3%, and home at 84.1% / 89.0%, with zero rejects.

Declaration modifiers now have a suffix-bearing attribute piece. An attribute
such as `@[simp] -- rationale` owns its inline comment and the forced newline
before the declaration keyword, so the declaration body remains active without
losing comment content. This removes `modifier-seam-comment`: the six focused
witnesses rise to 87.7% code-active / 93.0% shipped-of-portable, 249/249 rises
to 80.7% / 91.5%, widened 566/566 to 80.4% / 91.2%, and home remains 84.1% /
89.0%, with zero rejects.

Top-level `def … where` declarations now compose an independently active
field body after a multiline opaque signature fragment. Because the signature
retains its original top-level anchor, owning the body cannot drift the opaque
return type. This removes `defwhere-signature`: the focused witness closes at
83.1% code-active / 93.5% shipped-of-portable, 249/249 at 80.8% / 91.6%,
widened 566/566 at 80.6% / 91.3%, and home at 84.1% / 89.0%, with zero
rejects.

Multiline opaque structure-field values now break after `field :=` onto an
explicit line-start seam. The opaque value keeps its source-column anchor while
the field, enclosing structure, and declaration remain active. This removes
`val-multiline` from its focused witness, which closes at 89.2% code-active /
93.9% shipped-of-portable; 249/249, widened 566/566, and home remain green at
80.8% / 91.6%, 80.6% / 91.3%, and 84.1% / 89.0%, with zero rejects.

The declaration-wide padded-parenthesis substring fence is gone. Its live
witnesses were string payloads such as `"( "`, not parenthesized syntax, and
the syntax walkers already own actual parens. This removes `padded-paren`: the
focused witness closes at 93.1% code-active / 98.1% shipped-of-portable,
249/249 rises to 80.8% / 91.7%, widened 566/566 holds 80.6% / 91.3%, and home
holds 84.1% / 89.0%, with zero rejects.

## Final named-residue ladder (set 2026-08-07 at 80.7 / 91.4 widened)

The widened queue now has nine named bailout families. Burn them in dependency
order: compositional children before their enclosing lexical guards. Every gate
must pass focused witnesses, 249, widened 566, and home with zero token,
parse, or fixed-point rejects before commit and push. A failed conjecture is
discarded; it does not count as a clearance.

1. **G42 — `equation-arm-piece` (1,744 bytes / 9 arms).** Instrument the shared
   arm loop, name the exact rejection stage, and move opacity to the smallest
   pattern or body piece. Exit: residue materially reduced, no new arm-wide
   bailout.
2. **G43 — `structure-field-piece` (550 / 2).** Preserve only the unsupported
   field interior at its line-start seam. Exit: no whole structure-field piece
   when its head and sibling fields are portable.
3. **G44 — `inductive-constructor-piece` (564 / 2).** Apply the same piecewise
   law to constructors. Exit: unsupported constructor tails do not make the
   constructor head or neighboring constructors opaque.
4. **G45 — `defwhere-calc` (977 / 1).** Anchor the calc-bearing field/value,
   retaining the active signature and other `where` fields. Exit: declaration-
   wide reason removed.
5. **G46 — `unspaced-tuple-pattern` (410 / 1).** Replace the source substring
   fence with syntax-derived tuple-pattern ownership. Exit: spacing-sensitive
   token spelling preserved at the smallest owner.
6. **G47 — `nested-application-struct-shorthand` (14,975 / 190).** Localize
   shorthand adjacency to the owning application/field rather than its ancestor
   stack. Exit: dominant byte pool collapses without changing macro expansion.
7. **G48 — `adaptation-note-whitespace` (10,283 / 9).** Classify the command
   structurally and preserve only its whitespace-semantic payload. Exit: parent
   declarations and tactic sequences remain active.
8. **G49 — `message-interpolation-whitespace` (23,949 / 18).** Preserve each
   interpolation owner, not every containing declaration. Exit: message token
   stream unchanged and declaration-wide reason removed.
9. **G50 — `syntax-antiquotation-whitespace` (101,281 / 113).** Apply the same
   smallest-complete-owner law to quotation/antiquotation nodes. Exit: quotation
   bytes stay exact while enclosing commands compose actively.
10. **G51 — exposed-residue fixed point.** Rerun widened and home queues after
    G42–G50; enumerate and gate every newly visible named reason until the named
    queue is empty or a class is explicitly proved ceiling-only.
11. **G52 — full-tree lock.** Run all mathlib files, zero rejects; document every
    ceiling-only class with a syntax/policy argument; freeze the census as a
    standing production gate.

G52 closes over all 8,245 Mathlib files: zero missing statistics and zero
unclassified safety-gate rejects. The production lock ships 81.8% of all code
bytes and 91.9% of the portable surface. Its remaining 113 failed candidates
are named by exact path in the identity-clearance ledger; each returns the
original source and counts as zero shipped-active bytes. The clearance files
compose by set union (associative, commutative, and idempotent), are consulted
only after semantic validation fails, and cannot authorize a changed result.
`mathlib-full-gate.sh` pins coverage at 91.8%, rejects at zero, missing stats at
zero, and identity clearances at 113, making every regression or new exception
loud while allowing the exception set to shrink monotonically.

G42 closes by degrading an unsupported multiline pattern at its own arm seam
instead of collapsing the complete equation set. The eight portable siblings
in `WhatsNew` remain active; the focused residue falls from 1,744 to 944 bytes
and coverage rises from 63.8% / 69.9% to 72.1% / 79.0%. The 249, widened 566,
and home gates close at 80.8% / 91.7%, 80.7% / 91.4%, and 84.1% / 89.0%, with
zero rejects.

G43 closes by admitting implicit structure binders through the flat token law
and splitting a documented unsupported field into an active doc prefix plus an
opaque tail at the field seam. Focused `structure-field-piece` falls from 550
to 156 bytes and closes at 83.1% / 95.4%; 249, widened 566, and home close at
80.8% / 91.7%, 80.7% / 91.5%, and 84.1% / 89.0%, with zero rejects.

G44 applies the same prefix/tail law to documented inductive constructors: the
docstring remains active and only the unsupported dependent-arrow signature is
opaque at the constructor seam. Focused residue falls from 564 to 241 bytes and
closes at 80.3% / 96.4%; 249, widened 566, and home close at 80.8% / 91.7%,
80.7% / 91.5%, and 84.1% / 89.0%, with zero rejects.

G45 removes the obsolete `defwhere-calc` declaration fence. The field/value
walker already owns calc-bearing structure fields at a stable seam, so the
ordinary `def … where` composition converges unchanged. The focused witness
closes at 73.0% / 81.3%; 249, widened 566, and home close at 80.8% / 91.7%,
80.7% / 91.5%, and 84.1% / 89.0%, with zero rejects.

G46 removes the declaration-wide `,_ )`-style source substring fence. Its live
witness mixed an ordinary tuple pattern with quoted tactic syntax; both are
already owned by their syntax walkers and preserve their token stream. The
focused declaration reason disappears at 61.6% / 68.2%; 249, widened 566, and
home close at 80.8% / 91.7%, 80.7% / 91.5%, and 84.1% / 89.0%, with zero
rejects.

G47 localizes nested structure-shorthand opacity to the nearest application
owner. JSX-bearing applications retain their proven wider owner: the tree gate
caught the unsafe narrow form on `ClickSuggestions`. Widened residue falls from
14,975 to 2,176 bytes; 249, widened 566, and home rise to 81.0% / 91.9%, 80.9%
/ 91.7%, and 84.2% / 89.1%, with zero rejects.

G48 removes the blanket adaptation-note declaration fence. Five ordinary
tactic placements compose through the existing unknown-tactic fallback; only
an adaptation note nested inside an anonymous constructor retains whole-form
source-exact ownership, as required by the token gate. Residue falls from
10,283 to 383 bytes; 249, widened 566, and home rise to 81.1% / 92.1%, 81.0%
/ 91.8%, and 84.2% / 89.1%, with zero rejects.

G49 limits message-interpolation source-exact ownership to declarations that
contain a backslash-newline message literal. Ordinary `m!"..."` nodes now
compose through their surrounding command; the fixed-point gate proved the
continued-line exception on `Choose`. Residue falls from 23,949 to 6,133 bytes;
249, widened 566, and home rise to 81.3% / 92.3%, 81.2% / 92.0%, and 84.2% /
89.1%, with zero rejects.

G50 removes the declaration-wide syntax-antiquotation fence. The quotation pin
already preserves every antiquotation payload, and all 40 focused files pass
without an exception. The 101,281-byte named residue disappears; 249, widened
566, and home jump to 83.1% / 94.3%, 82.7% / 93.8%, and 87.7% / 92.8%, with
zero rejects. The census cache hash now excludes generated `.lean4fmt` results,
so repeated trust gates reuse the exact source/toolchain build.

G51 closes the exposed named frontier. The widened queue contains only six
explicit smallest-owner classes:

- 6,133 bytes of declarations containing backslash-newline `m!` literals;
  moving ownership inward made `Choose` non-idempotent, so source-exact
  declaration ownership is required by the literal's indentation semantics.
- 4,501 bytes of individual equation arms whose patterns are multiline opaque
  syntax; siblings remain active and the arm seam is the smallest stable owner.
- 2,176 bytes in the single JSX-bearing `ClickSuggestions` application; a
  narrower application owner changes the parsed tree.
- 383 bytes for an adaptation note inside an anonymous constructor; removing
  declaration ownership changes the token stream.
- 241 bytes of dependent-arrow constructor tails and 156 bytes of structure
  field tails; doc prefixes and sibling items remain active.

These classes are the refined ceiling, not unexamined blanket bails. G50's
widened and home runs are the G51 fixed point: six named piece classes, zero
rejects, 82.7% / 93.8% widened and 87.7% / 92.8% home.

Equation declarations now compose multiline opaque suffixes at their owned
line-start seam. A `where` tail containing a docstring no longer forces its
equation arms and signature opaque. This removes `eqns-unformattable`: the
focused witness closes at 68.8% code-active / 81.5% shipped-of-portable;
249/249, widened 566/566, and home remain green at 80.8% / 91.7%, 80.6% /
91.3%, and 84.1% / 89.0%, with zero rejects.

Empty line-comment detection now classifies source lines whose trimmed content
is exactly `--`, rather than matching the `--\n` suffix inside every multiline
docstring opener. This removes the false `empty-line-comment` fence: the
focused witness closes at 30.8% code-active / 40.2% shipped-of-portable,
249/249 at 80.8% / 91.7%, widened 566/566 rises to 80.6% / 91.4%, and home
holds 84.1% / 89.0%, with zero rejects.

Adjacency-sensitive `⟦…⟧` notation now preserves its smallest complete
application owner plus the notation node itself, rather than every enclosing
term. The extra owner is required by category-theory shift macros; the focused
token gate caught the too-small first cut. This removes `shift-notation`: all
seven witnesses close at 85.6% code-active / 98.0% shipped-of-portable,
249/249 at 80.8% / 91.7%, widened 566/566 rises to 80.7% / 91.4%, and home
holds 84.1% / 89.0%, with zero rejects.
