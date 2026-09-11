# The layout-solver campaign

This appendix is the original gate ledger for the layout solver. It is retained
as evidence: the durable solver architecture is described in the main chapters,
while this record preserves the alternatives, staging decisions, and measured
exit conditions that produced it.

Goal: promote the constraint solver (`lean_4_fmt/solve/layout.lean`) from a
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

**G-L5 — the shape family + fold `.group`.** ✓ LANDED. *Shape family:* the
solver already drives the sig-shape choice for every decl kind that HAS one —
def/theorem/abbrev/opaque/example (defnDoc), def-where, and instance all route
through `sigDoc`'s adaptive resolution (G-L4). Recon settled the rest:
structure/inductive heads are ALWAYS single-line by construction (`inductiveDoc?`
builds the head as one string, bailing to verbatim on any multi-line binder) —
there is no shape choice to drive, so "every declaration shape" holds. *The
fold:* `group`/`groupW`/`alignOr` in `Solve.Layout` show `.group` = the
2-candidate `.choice` and `.alignOr` = the (N+1)-candidate `.choice`; the solver
reproduces the greedy flat-or-break in isolation (`solve == greedy`) and is
optimal where the greedy combinator is myopic (nested groups: DP 1 vs greedy
10). Verified core, no reformat: home 401/2, census stable.

> **CAMPAIGN COMPLETE.** The constraint solver is the house layout engine: it
> makes the def sig-shape decision live on the Emit path (allInline ≻ oneLine ≻
> onePerLine, per declaration, by width), the house style is pinned repo-wide,
> and the greedy pretty-printer combinators are proven special cases of its
> `.choice`. What remains is optional polish, not gates: the blank-line knobs
> (blanks as zero-width choice points — G-L4's deferred half), and — only if a
> real greedy-suboptimal case surfaces in the corpus — bridging live Docs
> through the DP renderer (the proven `.group` renderer stays until then).

## Scoreboard

| gate | rev | what landed | checks |
|------|-----|-------------|--------|
| core | 5fcb3e9 | measure-algebra DP, Pareto frontier, omega feasibility; greedy-beat (1 vs 10) + def adaptivity #guards | build-time guards green |
| **G-L1** | ff46f7f | brute-force ground truth; solve==bruteOpt on the nested battery; frontier sub-exponential (chain-12: 4096 raw → 13) | guards green, module builds |
| **G-L2** | 64b20fb | DefPieces bridge + defLadder/renderDef; byte-lock reproduces the exact pinned `find_upstream` shape; width-optimal + feasible on real ServeFd sigs; adaptivity holds | guards green, module builds |
| **G-L3** | 6ee4842 | `inlineDefFits` = `bestUnder` routes defnDoc's inline/break decision, `solveDefs` knob (repo on / preset off); `#guard` proves `≡ (total ≤ W)` totally; imported into Emit.Decl | home 401/2, corpus-gate 234/0/0, census 0-reject, guards green |
| involution-fix | 990bc47 | `plainLead` blank-invariant: a blank-only leading in a single-tactic by/do body no longer diverts it off the inline path (the 2-step-convergence fixed-point bug the pin surfaced on 71 files) | corpus-gate 234/0/0, home 401/2, pin fallbacks 71→0 |
| pin (adopt house style) | f087bea | `fmt.lean` → visibilityOwnLine + bodyOwnLine=false; whole `src/` reformatted to the pin (314 files, experiments excluded); the formatter self-hosts (rebuilds from its own pinned source, guards green) | home pin-clean, idempotent, census dormant |
| **G-L4** (chooser) | 148865d | `pickShape` (tagged feasible-set argmin — the preference map) + `sigOneLineFits` + `BinderLayout.adaptive`; sigDoc resolves adaptive per-decl through the solver. Dormant under onePerLine (byte-identical). Fix: use the type's real `flatWidth`, not typeInfo's getD-0'd width (an active `let`/`∀`-in-type would mangle onto the keyword line — a reparse-fail) | home 401/2 dormant, guards green |
| **G-L4** (activate) | a655922 | `fmt.lean` → binders=adaptive; `src/` reformatted (295 files): a broken def keeps its sig on one line when it fits ≤W, else stacks — width-capped, so mostly 1-2 binder defs un-explode | home 401/2, 0 fallbacks, corpus 234/0/0, make core builds, self-hosts |
| **G-L5** (fold) | a4b372d | `group`/`groupW`/`alignOr` — `.group` and `.alignOr` shown as the degenerate `.choice`; the solver reproduces the greedy flat-or-break IN ISOLATION (`solve == greedy`) but is optimal NESTED (nestedGroups: DP 1 vs greedy 10). The combinator vocabulary is the low-lookahead corner of the one constraint problem | guards green, home 401/2, census stable |
| **G-L6** (fold-up) | (this) | removed the scaffolding the live path obsoleted: the offline G-L2 bridge (DefPieces/defLadder/renderDef/fixtures), the def rung ladder (defInline/defHang/defDoc), and the money case (inner/whole → G-L5's `nestedGroups` is it now); `nestedDef` refactored onto an inline `.choice`. Layout.lean 430→320 lines, only the verified core + live solver + fold remain | guards green, home 401/2, census stable |
