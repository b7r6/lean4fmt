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
| **G-L1** | (this) | brute-force ground truth; solve==bruteOpt on the nested battery; frontier sub-exponential (chain-12: 4096 raw → 13) | guards green, module builds |
