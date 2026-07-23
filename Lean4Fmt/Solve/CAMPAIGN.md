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

**G-L3 — live on the `def` path, gate-clean.** ✓ LANDED. Route `def`'s
inline-vs-break decision through the solver in Emit, knob-gated (`solveDefs`,
on in repo `fmt.lean`, off in the preset the census uses).

> **What landed — thin byte-identical wiring, not the pin-first reformat.**
> `defnDoc`'s `total ≤ fitW` inline test now goes through
> `Solve.inlineDefFits` = `bestUnder` (the hard-width filter, then the cost
> argmin — the solver's own selection kernel) over an inline rung (width
> `total`) vs an always-feasible break rung. On a FLAT sig, feasibility IS the
> whole story (greedy meets the optimum), so it reproduces the old test — but
> now COMPUTED by the measure algebra, live on the shipping path. A `#guard`
> proves the equivalence `inlineDefFits W total ≡ (total ≤ W)` TOTALLY (over
> all inputs, not sampled), so it cannot diverge — home stayed 401/2 (the 2
> are the untouched `ServeFd`/`GradedMonad` experiments) with the solver live
> on every repo def, corpus-gate idempotence PASS (234/0/0), census dormant
> (preset knob off) → 0 rejects, unchanged.
>
> **Why thin, and why the recon's pin-first was set aside.** Harness recon this
> session found (a) home == the whole `src/` tree, so the recon's "apply the
> pin + reformat `src/`" is a ~400-file cosmetic change sitting next to the
> experiment landmines — unnecessary RISK for a WIRING gate; and (b) the census
> styles mathlib via the `straylight` PRESET, not the repo `fmt.lean`, so a
> default-off knob is dormant on the census BY CONSTRUCTION. That split the gate
> cleanly: wire first (byte-identical, zero reformat, zero landmine), adopt +
> adapt second. The intricate `defnDoc` surgery the recon feared collapsed to a
> one-line decision swap — the solver decides, `defnDoc`/`sigDoc` still render
> (no string-fidelity risk, no vis-coupling: `modifiersDoc` still owns
> visibility). `Solve.Layout` is imported into `Emit.Decl` (one-way, no cycle),
> so the exe build runs its #guards.

> **The pin landed here** (adopt-house-style commit) — `fmt.lean` flipped to
> visibilityOwnLine + bodyOwnLine=false and the whole `src/` reformatted, on
> the byte-identical-drop-in solver of G-L3 plus the involution fix that
> `bodyOwnLine=false` required. The user's `ServeFd` hand-edit turned out to be
> already pin-clean — the inference was right. `ServeFd`/`GradedMonad`/the
> untracked `experimental/algebra` are excluded; the tracked `experimental/llm`
> tree (clean repo code, not a formatting study) adopts the style with the rest.

**G-L4 — the preference map + blank-line knobs + adaptive shapes.** Now that the
pin is live, make the solver CHOOSE among sig shapes per-def: add the
`oneLine`/`fill` rungs and real preference weights (a 2-binder def picks
`oneLine` where `onePerLine` would explode it), and fold in the blank-line knobs
(the original ask) as zero-width choice points. *Exit: adaptive shapes live
(same sig, different rung by width), blank knobs exercised on a blank-dense
anchor (Δlines > 0), preference map config-driven, home + census clean.*

**G-L5 — the shape family + fold `.group`.** Extend to theorem/instance/
structure sig ladders; document/fold `.group` (= the 2-candidate `.choice`) and
`.alignOr` into the one combinator. *Exit: the solver drives every declaration
shape, census stable, pinned as the house layout engine.*

## Scoreboard

| gate | rev | what landed | checks |
|------|-----|-------------|--------|
| core | 5fcb3e9 | measure-algebra DP, Pareto frontier, omega feasibility; greedy-beat (1 vs 10) + def adaptivity #guards | build-time guards green |
| **G-L1** | ff46f7f | brute-force ground truth; solve==bruteOpt on the nested battery; frontier sub-exponential (chain-12: 4096 raw → 13) | guards green, module builds |
| **G-L2** | 64b20fb | DefPieces bridge + defLadder/renderDef; byte-lock reproduces the exact pinned `find_upstream` shape; width-optimal + feasible on real ServeFd sigs; adaptivity holds | guards green, module builds |
| **G-L3** | 6ee4842 | `inlineDefFits` = `bestUnder` routes defnDoc's inline/break decision, `solveDefs` knob (repo on / preset off); `#guard` proves `≡ (total ≤ W)` totally; imported into Emit.Decl | home 401/2, corpus-gate 234/0/0, census 0-reject, guards green |
| involution-fix | 990bc47 | `plainLead` blank-invariant: a blank-only leading in a single-tactic by/do body no longer diverts it off the inline path (the 2-step-convergence fixed-point bug the pin surfaced on 71 files) | corpus-gate 234/0/0, home 401/2, pin fallbacks 71→0 |
| pin (adopt house style) | (this) | `fmt.lean` → visibilityOwnLine + bodyOwnLine=false; whole `src/` reformatted to the pin (314 files, experiments excluded); the formatter self-hosts (rebuilds from its own pinned source, guards green) | home pin-clean, idempotent, census dormant |
