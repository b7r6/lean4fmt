# Identity-Aware Renaming

This chapter combines the durable rename design with its original gate ledger.
The opening sections state the production contract. Later dated sections are
the engineering record: they retain failed approaches because those failures
explain why resolution, collision evidence, and build transactions are required.

Goal: promote the casing/rename axis from a verified plan-only core to a
**build-validated project pass** — the formatter renames project-defined
identifiers to the house casing (Straylight = snake on every naming axis),
token-aware, across a whole tree, with the compiler as the floor.

## The floor is INVERTED here

The layout axis is token-PRESERVING: its floor is degrade-to-identity — a
rejected file emits its input, "never worse than input." A rename is
token-CHANGING by construction (the whole point is to move the idents), so
that floor does not exist. **The floor is the build.** A bad rename is a
failed `make`, caught before it lands, reverted with zero damage — never a
silently corrupted source. Everything below rides that single invariant.

Two corollaries the layout campaign never needed:

- **Census-dormant by construction.** The naming knobs default `.preserve`;
  mathlib is not ours to rename, so the axis is off on the census preset. The
  rename rides the repo project pass only (the packaged straylight preset /
  repo `fmt.lean`), never the mathlib-coverage instrument.
- **Orthogonal to layout.** A renamed file, re-formatted, must still be a
  layout fixed point (home 401/0/0). The rename changes which bytes the idents
  are, not where the line breaks fall.

## The three axes (schema — LANDED)

Medium granularity, per the ask: **modules/namespaces** one axis,
**theorems/axioms** one axis, **everything else** (types + terms) split into
`types` and `terms` for headroom. `Style.Naming` carries the four `Case`
fields; `Rename.Axis` (`ns`/`typ`/`thm`/`term`) maps decl kind → policy field.
Straylight pins `{ namespaces := snake, types := snake, theorems :=
snake, terms := snake }` — the ServeFd "systems Lean 4" convention.

## Standing checks (every gate)

- **`make` green** — the whole tree builds. THE floor; a rename that fails to
  compile is caught here, reverted, zero damage.
- **self-host** — lean4fmt rebuilds from its own renamed source, `#guard`s
  green. The formatter eats its own naming.
- **census-dormant** — naming defaults `.preserve` → mathlib census byte-for-
  byte unchanged (0-delta), by construction.
- **home 401/0/0** — layout unperturbed: rename ∘ format is still a fixed
  point (the axes are orthogonal).
- **token-aware** — strings, line/block comments, and docstrings byte-exact;
  only real `.ident` leaves move. The `#guard "find_upstream_slot"` string
  literal survives a `find_upstream_slot` decl rename.

## The gate ladder

**G-L7.0 — foundation.** ✓ LANDED (`3cf1c4f` + `9914048`). The verified
casing kernel (`Casing.Case`, `convert`; splits on lower/digit→Upper, all-caps
acronym stays one word, leading `_`/trailing `'` preserved; edges + idempotence
`#guard`-locked), the config schema (`Style.Naming`, straylight = snake, all
four fields parseable), the plan builder (`Rename.buildPlan`: target-differs ∧
target-unique ∧ not-a-keyword, collisions counted against the FULL resulting
name set so `fooBar→foo_bar` skips rather than merges into an existing
`foo_bar`; three exclusions `#guard`-locked), and the `--rename-plan` dry-run
mode (stdin `NAME AXIS` lines → the plan, printed). Pure, demonstrated on real
decls. *No apply, no tree risk.*

**G-L7.1 — the apply, hardened.** The parse-based token rewrite made real, and
made safe against the one collision class the build floor already proved live.

- *Mechanism.* `Rename.identReplacement` (dotted-name last-component rewrite:
  `Foo.bar` under a `bar→baz` map becomes `Foo.baz`), `--rename-apply`/`--map`
  in Cli, `runRenameApplyImpl` in Main: `batchEnv` → `parseFull?` → `leafTokens`
  filtered to `.ident` → each ident's byte range via `getSubstring?` → splice
  end-to-start over the UTF-8 `ByteArray` (`ba.extract 0 s ++ new ++ ba.extract
  e n`, `String.fromUTF8!`). End-to-start so earlier ranges stay valid.
- *Exemption (the dogfood-surfaced hazard).* `buildPlan` excludes a target that
  collides with a **module basename** in the tree — the "local exemptions" the
  house style reserves. The set on lean4fmt is exactly **Diagnostic, Doc,
  Layout, Naming, Options, Style, Walk** (the `typ`/`term` decls whose name ==
  a module file basename). Without
  it, `Options → options` rewrites `import Lean4Fmt.Style.Options` → `bad
  import`. The exemption is reported (SKIP), not silent.

*Exit: the rewrite round-trips a fixture (idents move, strings/comments/
docstrings byte-exact, reparse-clean); the module-collision exemption
`#guard`-locked; exe builds; census dormant.*

**G-L7.2 — the dogfood: snake-ify lean4fmt, self-host.** Run the apply on the
formatter's own ~48 files under the straylight (snake) policy. `make` validates;
the formatter rebuilds from its own snake source (self-host), `#guard`s green;
any residual **library-name overlap** a build surfaces is resolved by the same
floor (exempt or rename-around, iterate). This is the axis proving itself on
its author.

*Exit: lean4fmt snake-ified, `make` green, self-hosts, home layout still
401/0/0 (rename ∘ format is a fixed point), token-aware clean, census dormant.*

**G-L7.3 — the house: snake the Continuity tree.** Apply across the broader
Straylight/Continuity domain code, per-package, build-validated, honoring the
per-package exemption sets — the actual house-style adoption, the "systems Lean
4" visual signal tree-wide. Domain code is already mostly snake and has fewer
self-referential module collisions than the formatter, so the apply is cleaner
than the dogfood. The whole owned tree participates; collision skips are
reported and build-gated rather than hidden behind historical file exemptions.

*Exit: the tree snake per-package, `make` green tree-wide, rejects (compile
failures) = 0, experiments untouched.*

## Scoreboard

| gate | rev | what landed | checks |
|------|-----|-------------|--------|
| **G-L7.0a** (casing core) | 3cf1c4f | `Casing.Case`/`convert`; lower/digit→Upper split, acronym-stays-one-word, `_`/`'` preserved; edges + idempotence `#guard`-locked | guards green, module builds |
| **G-L7.0b** (plan + dry-run) | 9914048 | `Style.Naming` schema (straylight = snake) + `Rename.buildPlan` (differs ∧ unique ∧ non-keyword, collisions vs full name set) + `--rename-plan`; three exclusions `#guard`-locked | guards green, dry-run demonstrated on real decls |
| **G-L7.1** (apply, hardened) | f1faaa7 | `identReplacement` + `--rename-apply` + `runRenameApply` (declsOf axis-classifies each command, global decl set, end-to-start UTF-8 splice); module-basename exemption (Diagnostic/Doc/Layout/Naming/Options/Style/Walk) | fixture round-trip (def+use move; string/comment/docstring byte-exact; reparses), exemption + dotted-rewrite `#guard`, exe builds, census dormant |
| **G-L7.2** (dogfood) | 0c0210e | snake-ify lean4fmt's own 55 files: 288 renames / 10 skipped (7 module-basename + Case keyword + ValForm/valForm collision), re-formatted the 12 width-shifted files | make green (102 jobs), self-hosts, fixed point 0-reformat, home clean but the 2 experiments, idempotent (2nd pass 0 renames), census dormant |
| **G-L7.3** (harden) | 2e88b24 | multi-workspace orchestrator (subprocess/file, bounded waves — solves the union-batchEnv failure) + field-aware collision detection (struct fields on the terms axis) | 0 parse failures on aleph (48) + core/build (37); type↔field collisions blocked; floor caught every domain hazard |
| **G-L7.3** (house rollout) | PENDING | snake the domain tree — needs name-resolution rename (see status) | — |
| **G-L7.4b** (resolver foundation) | a6b65b3 | `Session.resolve_idents` — elaborate w/ info trees, harvest `(range, resolvedFullName)` from TermInfo/FieldInfo; `--resolve-dump` probe | resolves bare-ident + qualified refs; root cause found |
| **G-L7.4a** (the olean farm) | d1c5aa3 | `build_olean_farm` — merged symlink farm (one `Continuity/` root, first on path) fixes findOLean's root-namespace mis-resolution | proof: `DischargeProof` in env, 26 Trust refs (was 0), full elaboration restored |
| **G-L7.4c** (resolver complete) | 93a24d2 | dot-projection case in `resolve_idents` (`p.isPure` → owning field const) | `p.isPure` resolves; no unresolved non-local ident |
| **G-L7.4d** (resolved rewrite) | 324c68f | `--resolve`: identity map (full names), rewrite iff resolved-in-set | cross-package fixture: local renames, imported use byte-exact, reparses |
| **G-L7.4e** (the hybrid: resolution decides, token acts) | 9c1d054 | `plan_hybrid` — a simple name renames iff every occurrence resolves to ONE defined full name (ambiguous cross-package spellings left byte-exact); token rewrite acts (catches binder types); sanity gate filters generated consts | 35 correct renames on core/build, cross-package `isPure` disambiguated; four `#guard`s; **BANK still red — two named edge cases** |
| **G-L7.4f** (field-declId capture) | ee879d4 | struct fields into the resolved `defs` (`struct_field_fulls`, emitted as `F` def-only) + an identity-aware, namespace-BLIND target-taken guard in `plan_hybrid` — skip `S → t` if any OTHER decl already spells `t` (the token rewrite is global, so the new `t` shadows it cross-namespace: `Lang` atop `target_def.lang`) | type↔field class SKIPs, reported; two new `#guard`s; guards green |
| **G-L7.4g** (pass-2 consistency) | ee879d4 | orchestrator exits nonzero on any pass-2 SKIP under `--resolve` — a half-rename reverts whole rather than leaning on the next build | 0 pass-2 SKIPs on core/build (the `--elab off` drop proved unneeded — CLI/Main parses cheap; abort is the rollout fail-safe) |
| **G-L7.4h** (THE REAL BANK) | 1f873b1 | `core/build` snaked under `--resolve` with f+g in — 29 renames / 10 skips over 12 files | `lake -R build` GREEN (73 jobs) where the token approach went red; rejects 0; committed |
| **G-L7.4i** (deterministic resolver + authorize/collide split) | 0adc64d | def set harvested from ONE elaboration (`env.constants.map₂`, was a 2nd flaky parse); split into `defs` (declId reals — authorize) vs `exists` (all local consts incl. generated — collide) so generated projections (`extends` `toParent`) never rename but still block | non-determinism gone (5/5, 3/3); `TrustStateWithPolicy.toTrustState` no longer mis-renamed; dead `resolve_rewrite_file`/`struct_field_fulls` removed |
| **G-L7.4j** (codegen — first CROSS-PACKAGE bank) | c300cc9 | codegen snaked AND build's use-sites of codegen's renamed decls rewritten in one pass (`Top` → `top`, build's `: Top` → `: top`, 16 build files) — the "A renames, B follows" path core/build's self-contained pass never tested | 33 renames / 27 skips / 106 files, deterministic 3/3; `lake -R build` GREEN codegen (133) + core/build (73) |
| **G-L7.4k** (local-binder capture) | a6e57ac | `resolve_idents` harvests each term's `lctx.decls` user names into the COLLISION set (`exists`) — the taken guard then skips a type whose snaked form shadows a param/`let`/`match` binder (`(action : Action)` → `(action : action)`). Renames become a strict subset (more skips, never more) → no green package regresses | type↔binder shadow class closed; the "pass it through without breaking" floor |
| **G-L7.4l** (aleph — non-breaking pass) | f8fc171 | aleph snaked as far as safe: binder-shadowing types left camelCase, EDSL macro quotations (EDSL.lean, 123 lines) rewritten CONSISTENTLY (global-by-resolved-identity → a name renames in quotation + def + uses alike — the macro class the token approach couldn't handle, retired) | 65 renames / 23 skips / 47 files, deterministic 2/2; `lake -R build` green (44-job lib, baseline parity; pre-existing `--bogus`/ld test-target errors unrelated) |

## The frontier finding (2026-07-24, cross-package + the determinism trap)

The user opened the frontier past the leaf: **codegen**, imported only by build.
Two things surfaced, both caught by the floor, both now closed:

- **Non-determinism (the important one).** Two identical codegen runs gave 61 vs
  56 renames — sometimes a type snaked onto an unseen term (`Attr` → `attr` atop
  `def attr`, "already declared"). The resolve worker did TWO elaborations
  (`resolve_idents` + a second `parse_full?` with elab fallback, for fields);
  when the heavy second one raced/crashed, the worker's buffered stdout — a
  decl's DEF line among it — was dropped, so the global def set was intermittently
  incomplete and a collision went unseen. Fixed by harvesting the def set from
  the SAME elaboration (`env.constants.map₂`). **A flaky def set is worse than a
  wrong one — it passes review once and breaks later; determinism is a
  correctness property here, not a nicety.**
- **Authorize ≠ collide.** `map₂` is complete but includes GENERATED consts
  (`extends` `toParent`, recursors, match arms). Feeding those to the rename
  gate renamed tokens with no source spelling. Split into `defs` (declId reals,
  may rename) vs `exists` (all consts, collision-only). Generated names now block
  targets without ever being renamed.
- **The farm needs clean oleans.** Resolution reads BUILT oleans; a stale/partial
  build (e.g. from a reverted experiment) skews the plan. Build the package clean
  before renaming. (Surfaced as a phantom 0-vs-3 that vanished after a clean build.)
- **aleph — the two walls, and both fell (`a6e57ac`, `f8fc171`).** aleph broke
  first on the **type↔local-binder shadow** (`(action : Action)` → `(action :
  action)` — the param named after its type). Local binders aren't env consts, so
  the const-based collision set never saw them; harvesting each term's `lctx`
  user-names into `exists` closes it (the shadowing types stay camelCase — partial
  snake, but green). The **EDSL macro-quotation class** I'd flagged as the harder
  wall turned out SAFE: the resolution rename is global-by-resolved-identity, so a
  name renames in its `` `(…) `` quotation, its definition, and its uses uniformly
  — EDSL.lean's 123 rewritten lines built green. The macro class the *token*
  approach couldn't stay consistent through is retired by resolution. Verdict:
  aleph passes through non-breaking (65 renames / 23 skips), the floor the user set.
- **The lesson for the rollout.** The rename is CLEAN on mostly-snake code (codegen
  fully) and NON-BREAKING-but-partial on camelCase-convention code (aleph — the
  `(x : X)` idiom forces some types to stay camelCase). Either way the floor holds:
  never a broken build.

## The dogfood finding (2026-07-24, the empirical basis for G-L7.1's exemption)

The parse-based rewrite ran clean on all ~48 lean4fmt files — token-aware, only
real `.ident` leaves moved, strings/comments/docstrings untouched, the 283-name
map applied consistently. The build floor caught exactly one hazard: `Options`
is both the Cli `structure Options` AND the `Style.Options` module, so the
rename turned `import Lean4Fmt.Style.Options` into `...options` → `bad import`.
`make` caught it before it landed; reverted cleanly (my own code). This is the
whole thesis of the axis working as designed — a bad rename is a failed compile,
never corrupted source. The fix is the exemption in G-L7.1; the full set is the
seven module-colliding decls named above.

## G-L7.3 status — tool hardened; domain rollout needs name-resolution (2026-07-24)

The apply mechanism is proven and self-hosted (G-L7.2 snaked the formatter's own
55 files). The house rollout drove two tool hardenings and surfaced the real
ceiling of the token approach. Every domain hazard below was caught by the floor
(`make` / `lake build`) — zero corrupted source, the whole thesis holding.

**Hardening 1 — multi-workspace apply (SOLVED, `2e88b24`).** A single union
`batchEnv` over a cross-workspace tree throws when an olean resolves to the wrong
build dir (aleph's `Continuity.Codec.Core.Box` → `core/trust`, which lacks it;
`make aleph` is green because lake uses the real dep graph, but the exe's flat
`lake env` path is incomplete). `importModules` is one-shot per process, so no
in-process retry is possible. `--rename-apply` is now an ORCHESTRATOR: two worker
modes (`--rename-decls`, `--rename-rewrite`) spawned one subprocess PER FILE
(clean single import each) in bounded waves. Pass 1 collects decls globally, pass
2 rewrites. **0 parse failures on aleph (48 files) and core/build (37), five
workspaces.** The parse problem is gone.

**Hardening 2 — field-aware collisions (SOLVED, `2e88b24`).** `decls_of` now
extracts structure FIELDS (the terms axis). A type↔field collision — `Lang`
snaking to `lang` while a `lang` field exists — is now blocked, not applied
(+ Arch/OS/ABI/Cpu/Gpu/CoeffectPolicy/… on core/build).

**The ceiling — cross-package identifier collisions (needs name-resolution).**
core/build uses `isPure` (its own decl) AND references `core/trust`'s
`DischargeProof.isPure` field — the SAME token. A component-wise rewrite renames
both, and the projection on the (unchanged) trust field breaks. Token rewrite
cannot distinguish two decls sharing a spelling; only ELABORATION-aware rename
(resolve each ident to its defining decl, rewrite by resolved identity) can. This
is why the formatter snaked cleanly — its names are collision-free — and domain
code does not. aleph adds a second class: macro/quotation bodies (`` `(TargetDef.mk' …) ``)
where a token rename can't stay consistent through elaboration.

**Still standing — the protected experiments gate their closures.** `GradedMonad`
(in `core/base`) and `ServeFd` (→ `evring`/`codec`/`freeside`) consume domain
names and may not be touched, so their transitive closure (reaching `stdlibex`,
the DAG floor) is off-limits until unblocked. And only LEAF packages are
renamable in isolation anyway — a non-leaf rename must update use-sites tree-wide,
re-hitting the experiments.

**The paths forward** (the decision): (a) build the name-resolution rename
(elaboration-aware, rewrite by resolved decl identity) — the honest fix for
domain code, retires both the cross-package and the macro class; (b) unblock the
experiments → the token tool can at least attempt collision-free leaf packages;
(c) hold — the tool is hardened and the formatter is snaked/self-hosted; roll the
house out when (a) lands. The two hardenings are banked either way.

## G-L7.4 scoping — the resolver works; the real blocker is module resolution (2026-07-24)

Scoped the name-resolution rename (path (a) above). `Session.resolve_idents`
elaborates a module with info trees ON and harvests, per resolved ident
occurrence, its byte range + the resolved full constant name (`TermInfo.expr` for
const references, `FieldInfo.projName` for dot-projections). Exposed as
`--resolve-dump`. **The resolver is correct** — every in-package and Lean-core
reference in a probe file resolved to its true full name; this is exactly the
disambiguation the token map lacked.

**But the probe surfaced the unified root cause behind every domain-rollout
failure — and it is not the rename axis and not the InfoTree.** It is the exe's
MULTI-WORKSPACE MODULE RESOLUTION. The monorepo's packages all share the
`Continuity.*` namespace, each building only its own subtree's oleans. The exe
merges the workspaces' `lake env` lib dirs into ONE flat search path, and
`findOLean Continuity.Trust.Discharge` then returns `core/codec`'s build dir (a
`Continuity/` root that appears on the path but does NOT own that olean) —
`.../core/codec/.../Continuity/Trust/Discharge.olean`, which does not exist.
`imports_env` (Frontend/Env.lean) then SILENTLY DROPS the import (its
`findOLean` + `pathExists` guard fails), so `DischargeProof` never enters the
elaboration env and its references don't elaborate — no resolution info for
exactly the cross-package names that cause the collisions. The same
mis-resolution *threw* (`Box.olean does not exist`) in the parse-batch path and
*silently drops* in the elaboration path.

**The fix is infrastructure, and it unblocks more than the rename:** replace the
flat merged search path with a per-package module→olean resolution that respects
lake's dependency graph (e.g. drive each file's env from `lake setup-file`, or a
built module→owning-lib map), so cross-package modules resolve to the workspace
that actually owns them. Once a domain file FULLY elaborates in the exe,
`resolve_idents` + the existing plan/exemption/subprocess/splice pipeline is the
complete name-resolution rename. Until then, G-L7.4 (and any correct
multi-workspace elaboration in the exe) is gated on the module-resolution fix.

## G-L7.4 gate ladder — to a REAL BANK (set 2026-07-24)

Goal: land the RESOLUTION rename — rewrite by resolved decl IDENTITY, not
spelling — and bank it on the domain package that broke the token approach
(`core/build`), build-validated. The farm (G-L7.4a, multi-workspace resolution)
and the InfoTree resolver (G-L7.4b, bare + qualified) are IN. Three monotone
gates close the loop.

The floor is unchanged: the BUILD. A rename that miscompiles is caught by `lake
-R build` / `make`, reverted, zero damaged source. Resolution adds a SECOND
floor — **completeness**: every non-local ident occurrence must resolve, else a
missed use-site of a renamed decl breaks. Standing checks per gate: build green,
census-dormant (`.preserve`), home 401/0/0 (layout orthogonal), and the new one
— resolution-complete (no unresolved non-local ident in the target).

**G-L7.4c — the resolver complete (projections).** Add the dot-projection case
to `resolve_idents`: a projection-syntax `TermInfo` (`p.isPure`) whose stx is the
whole `p.isPure` and whose `expr.getAppFn` is the field/projection const — pull
the FIELD ident child's range + that const. *Exit: `p.isPure` resolves to
`…DischargeProof.isPure` in `--resolve-dump`; no unresolved non-local ident in
the probe file; the field-projection class covered.*

**G-L7.4d — the resolved-identity rewrite (`--resolve`).** Swap the token map for
identity. Pass-1 decls emit FULL names; the plan keys by full name (cross-package
same-spelling names COEXIST — the collision exemption dissolves for them);
pass-2 rewrites an occurrence iff its RESOLVED full name is in the set, rewriting
the token's tail to the new name (qualification preserved). The farm rides each
worker's search path. Module-path components (import/open) are untouched by
construction — not const references — so the module-basename exemption largely
dissolves too (verify). *Exit: on a fixture with a deliberate cross-package
collision — a local `isPure` decl AND a used imported `isPure` — the local
renames, the imported use stays byte-exact, output reparses; `#guard` on the
identity-map builder.*

**G-L7.4e — THE REAL BANK: `core/build` under `--resolve`.** Run the resolution
rename on the package the token approach broke. The `isPure` / `Lang`-class
collisions resolve by identity — build's own `isPure` renames, trust's
`DischargeProof.isPure` projection is skipped byte-exact — so `lake -R build`
goes GREEN where the token rename went red. Iterate any residual. *Exit:
`core/build` snake-ified by resolution, `lake -R build` green, rejects 0,
committed. THE BANK — a domain package renamed correctly by name resolution,
floor-validated; the token approach's cross-package + macro classes both retired.*

## G-L7.4 closing gates — the two edge cases to the bank (set 2026-07-24)

G-L7.4e shipped as the **hybrid** (`9c1d054`): resolution DECIDES which simple
names are safe, a token rewrite ACTS (so binder-type positions the InfoTree
doesn't record are still caught). 35 correct renames on `core/build`, the
cross-package `isPure` disambiguated. But the BANK stayed red: two bounded,
named edge cases, each traced to one code site. Three monotone gates close them.

Standing checks unchanged: the BUILD is the floor; second floor is
resolution-completeness (no unresolved non-local ident); census-dormant, home
401/0/0, self-host (`#guard`s green), token-aware.

**G-L7.4f — field-declId capture (the type↔field collision). ✓ `ee879d4`.**
`plan_hybrid`'s `collides` only guarded source-vs-source (two safe names → one
target). It never checked target-vs-EXISTING, and struct fields never reach
`defs` on the resolve path (`resolve_idents` tags `isDef` only for
`Command.declId`; a field is a `structExplicitBinder`, no declId → the field is
absent). So `Lang → lang` landed atop the `lang` FIELD of `target_def` and the
build broke. The floor named it exactly: `List lang` where `lang : Build.lang`
of sort Type is a TERM, not a type — the field/param `lang` shadows the renamed
type. Crucially the type and field sit in DIFFERENT namespaces (`…Build.Lang`
vs `…Build.target_def.lang`), so a same-namespace check would miss it. *Fix:*
the resolve decls-worker emits struct-field FULL names (`struct_field_fulls`,
syntactic, tagged `F` = def-only); `plan_hybrid` gains an identity-aware,
namespace-BLIND target-taken guard — skip `S → t` iff any OTHER def (`d ≠ S`'s
full) spells `t` as its last component. Namespace-blind is right BECAUSE the
token rewrite is global-by-simple-name: renaming `Lang→lang` moves `Lang`
everywhere, so a colliding `lang` in ANY namespace is a hazard. (The earlier
namespace/occSimples attempts over-blocked to zero because they counted a name's
own occurrences; keying strictly on `d ≠ sFull` fixes that — 29 renames stand.)
*Banked: on core/build the `Lang`/`Cpu`/`Gpu`/`Vendor`/`Visibility`/
`Parametric`/`Faithful` names that clash with a field/term are SKIP + reported;
two new `#guard`s (field-taken skip + its no-collision converse).*

**G-L7.4g — pass-2 consistency (the fail-safe). ✓ `ee879d4`.** Pass-1 resolve
ELABORATES every file; a pass-2 cheap-parse SKIP would rewrite a file's deps but
not the file — a half-rename, previously only printed. *Fix:* the orchestrator
exits nonzero on any pass-2 SKIP under `--resolve`, so the driver reverts the
set whole. The anticipated `--elab off` drop proved UNNEEDED — `CLI/Main` parses
cheap and rewrote consistently (6 idents), so core/build hits 0 pass-2 skips.
The abort is the rollout fail-safe, not a core/build blocker. *Banked: 0 pass-2
SKIPs on core/build; abort wired for the multi-workspace rollout.*

**G-L7.4h — THE REAL BANK: `core/build` under `--resolve`. ✓ `1f873b1`.** With
f+g in, the resolution rename ran on the package the token approach broke: 29
renames / 10 skips over 12 files, resolved by decl IDENTITY. `isPure`
disambiguates (build's own renames, trust's `DischargeProof.isPure` projection
byte-exact); the `Lang`-class type↔field clashes skip; types snake with their
binder-type positions following (`TargetKind`, `SmArch`, `SourcePath`, …).
core/build is a leaf (nothing imports `Continuity.Build.*`/`Continuity.CLI`;
aleph's same-named `TargetDef` is its own sibling), so the rename is fully
contained. **`lake -R build` GREEN (73 jobs), rejects 0, committed** — THE BANK.
A domain package renamed correctly by name resolution, floor-validated; the
token approach's cross-package, type↔field, and pass-2 classes all retired.

Beyond the bank (not gates): fold the farm into the SHARED env path (fixes
multi-workspace FORMATTING + `--stats`, which hit the same silent drop invisibly
today); resume the house rollout on the safe leaf set with resolution; the
experiment closures stay gated until unblocked.
