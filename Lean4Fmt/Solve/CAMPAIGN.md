# The layout-solver campaign

Goal: promote the constraint solver (`Lean4Fmt/Solve/Layout.lean`) from a
verified isolated core to **the house layout engine** — the shipping formatter
selects the most-preferred declaration shape that satisfies the width
constraint, per declaration, optimally (not greedy).

The floor never moves: degrade-to-identity means every gate's failure mode is
"unformatted", never "damaged". Standing checks each gate — home 401/0/0,
core fuzz ≤ baseline, comment-multiset clean, wide-249 census rejects 0,
idempotence (`format ∘ format = format`, the involution the whole thing rides
on). Commit + push per gate.

## The five monotone gates

**G-L1 — the nested core holds (tractability + optimality).** The core works
on flat sigs; nesting (def ⊃ match ⊃ calc ⊃ …) is the real test. Compose
choice-trees through nesting; prove the DP optimum EQUALS brute-force-over-all-
layouts (correctness) while the Pareto frontier stays ≪ 2^depth (tractability).
*Exit: solve == bruteForce on the nested battery, frontier bounded, greedy-beat
holds — all #guard-locked. Pure core, no live-formatter risk.*

**G-L2 — Syntax → LDoc bridge for `def`, offline.** `ofDef?` builds the real
choice-tree from a `def`'s binders/type/body; a renderer emits the solved
layout. Run OFFLINE over every `def` in the anchor + a corpus slice, checked
for token-preservation + idempotence via the existing gate machinery — WITHOUT
touching the Emit path. *Exit: K/K real defs round-trip clean (parse-back, token
multiset == source, format∘format stable).*

**G-L3 — live on the `def` path, gate-clean.** Route `def` through the solver in
Emit (knob-gated, on for the house preset). *Exit: home 401/0/0, fuzz ≤ base,
wide-249 rejects 0, coverage ≥ prior; adaptivity live (short inline, long hang).
The shipping formatter now solves its defs.*

> **PREREQUISITE — settle the byte-identical target first.** The house-style
> pin is only half-applied: the `visibilityOwnLine` knob ships (26db864) but
> `fmt.lean` still selects the OLD style (no visibilityOwnLine, bodyOwnLine
> true) and the repo has NOT been reformatted. So "byte-identical to current"
> is ambiguous. Resolve before G-L3: either (a) apply the pin — update
> `fmt.lean` to visibilityOwnLine + bodyOwnLine=false, reformat `src/`, land
> it as one "adopt house style" commit (the pending step from the perturb/pin
> flow) — then the solver's hang shape matches the reformatted repo; or (b)
> configure the ladder to the OLD style for the drop-in test. (a) is the
> intended direction and cleaner. The user's `ServeFd`/`GradedMonad` working-
> tree edits are formatting-study experiments — never format/commit them.
>
> **Recon (before starting).** The integration is surgery on `Decl.defnDoc`
> — the formatter's most intricate function. Findings that make it a straight
> shot next session:
> - **Strategy = byte-identical drop-in.** Configure the ladder to the current
>   hang-always preference so knob-on leaves the home tree `--check`-clean
>   where the solver fires; that proves correct wiring BEFORE G-L4 flips on
>   adaptivity. Then the adaptive behaviour is a pure preference change on
>   known-good machinery.
> - **Injection = a fast-path short-circuit at the TOP of the def path**, NOT
>   surgery inside defnDoc. Guard: knob on ∧ top-level ∧ modifiers reduce to
>   [optional docstring, optional single visibility kw] (no attrs/comments) ∧
>   single-line type ∧ declValSimple body. Fires → solver owns the whole head
>   (vis + `def name` + binders + `: ret`), body via the existing `valForm`.
>   Anything else falls through to defnDoc untouched — never-worse-than-input.
> - **The coupling:** visibility placement and sig shape are entangled (inline
>   wants `private` inline; hang wants it own-line). So the solver path must
>   OWN visibility (skip `modifiersDoc`'s), which is why it takes the whole
>   head. `visibilityOwnLine` (already shipped) is the hang-rung's vis rule.
> - **Rendering:** `Lines → Doc` = bake indent into `.text`, join with
>   `.hardline`; correct at nest 0 (top-level decls, where Lean doesn't indent
>   namespaces) — hence the top-level guard.
> - Bail conditions match the existing defnDoc guards (fill-multiline-type,
>   preserve-sig-inexact, eqns). Import `Solve.Layout` into `Emit.Decl` (one-
>   way, no cycle) so the exe build runs its #guards.

**G-L4 — the preference map + blank-line knobs.** The cost model becomes
config: rung weights + break penalties + the blank-line knobs (the original
ask), blanks as zero-width choice points. *Exit: blank knobs live and exercised
on a blank-dense anchor (Δlines > 0), preference map config-driven, home +
census clean.*

**G-L5 — the shape family + fold `.group`.** Extend to theorem/instance/
structure sig ladders; document/fold `.group` (= the 2-candidate `.choice`) and
`.alignOr` into the one combinator. *Exit: the solver drives every declaration
shape, census stable, pinned as the house layout engine.*

## Scoreboard

| gate | rev | what landed | checks |
|------|-----|-------------|--------|
| core | 5fcb3e9 | measure-algebra DP, Pareto frontier, omega feasibility; greedy-beat (1 vs 10) + def adaptivity #guards | build-time guards green |
| **G-L1** | ff46f7f | brute-force ground truth; solve==bruteOpt on the nested battery; frontier sub-exponential (chain-12: 4096 raw → 13) | guards green, module builds |
| **G-L2** | (this) | DefPieces bridge + defLadder/renderDef; byte-lock reproduces the exact pinned `find_upstream` shape; width-optimal + feasible on real ServeFd sigs; adaptivity holds | guards green, module builds |
