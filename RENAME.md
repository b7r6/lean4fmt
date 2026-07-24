# The rename axis (G-L7)

Goal: promote the casing/rename axis from a verified plan-only core to a
**build-validated project pass** — the formatter renames project-defined
identifiers to the house casing (Straylight = snake, namespaces stay
UpperCamel), token-aware, across a whole tree, with the compiler as the floor.

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
Straylight pins `{ namespaces := upperCamel, types := snake, theorems :=
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
  a module file basename; `ns` names stay UpperCamel and are immune). Without
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
than the dogfood. The three formatting-study experiments stay excluded
(`ServeFd`, `GradedMonad`, `experimental/algebra`).

*Exit: the tree snake per-package, `make` green tree-wide, rejects (compile
failures) = 0, experiments untouched.*

## Scoreboard

| gate | rev | what landed | checks |
|------|-----|-------------|--------|
| **G-L7.0a** (casing core) | 3cf1c4f | `Casing.Case`/`convert`; lower/digit→Upper split, acronym-stays-one-word, `_`/`'` preserved; edges + idempotence `#guard`-locked | guards green, module builds |
| **G-L7.0b** (plan + dry-run) | 9914048 | `Style.Naming` schema (straylight = snake) + `Rename.buildPlan` (differs ∧ unique ∧ non-keyword, collisions vs full name set) + `--rename-plan`; three exclusions `#guard`-locked | guards green, dry-run demonstrated on real decls |
| **G-L7.1** (apply, hardened) | f1faaa7 | `identReplacement` + `--rename-apply` + `runRenameApply` (declsOf axis-classifies each command, global decl set, end-to-start UTF-8 splice); module-basename exemption (Diagnostic/Doc/Layout/Naming/Options/Style/Walk) | fixture round-trip (def+use move; string/comment/docstring byte-exact; reparses), exemption + dotted-rewrite `#guard`, exe builds, census dormant |
| **G-L7.2** (dogfood) | 0c0210e | snake-ify lean4fmt's own 55 files: 288 renames / 10 skipped (7 module-basename + Case keyword + ValForm/valForm collision), re-formatted the 12 width-shifted files | make green (102 jobs), self-hosts, fixed point 0-reformat, home clean but the 2 experiments, idempotent (2nd pass 0 renames), census dormant |
| **G-L7.3** (house) | BLOCKED | see status below | — |

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

## G-L7.3 status — mechanism proven, house rollout gated on two things (2026-07-24)

The apply mechanism is done and self-proven (G-L7.2 snaked the formatter's own
55 files, self-hosted). Rolling it across the Continuity tree hit two real,
orthogonal blockers — neither is a flaw in the rename axis:

**1. The protected experiments gate their dependency closures.** `GradedMonad`
lives *in* `core/base`; `ServeFd` pulls `evring` + `core/codec` + `freeside`.
Both experiments declare AND consume domain names, and they may not be touched
(user-protected formatting studies). Renaming a name an experiment references,
without renaming the experiment too, is a guaranteed compile break — which the
floor (`make`) would correctly reject. So `core/base`, `core/codec`, `evring`,
`freeside` (and their transitive closure, which reaches `stdlibex`, the DAG
floor) are OFF LIMITS until the experiments are unblocked. The safe complement
is roughly `aleph`, `codegen`, `core/build`.

**2. Multi-workspace olean resolution breaks the single-batch-env apply.**
lean4fmt snaked cleanly because it is SELF-CONTAINED (Lean-core-only, all its
oleans built and resolvable, one `batchEnv`). `aleph` spans five workspaces, and
the exe's flat `lake env printenv LEAN_PATH` resolves a cross-package module
(`Continuity.Codec.Core.Box`) to the wrong build dir (`core/trust`, which lacks
it) instead of `core/codec` (which has it) — `batchEnv` throws at env
construction. `make aleph` is green (lake uses the real dep graph); only the
exe's flat discovered path is incomplete. `importModules` is one-shot per
process, so a catch-and-retry bare-env fallback trips
`enableInitializersExecution` — the union must succeed the first time. Doing
multi-workspace safely needs the Driver's architecture (per-file own-env parse,
subprocess retry of conflicts) lifted onto the rename path — a real effort, not
a patch. The tool stays at its proven single-batchEnv state (clean for
self-contained trees).

**The paths forward** (the decision): (a) unblock the experiments (finish the
studies / allow the rename) → the DAG floor `stdlibex` + `core` become
renamable; (b) invest in the per-file-env + subprocess-retry hardening → the
multi-workspace packages (`aleph`, apps) become renamable; (c) hold at
mechanism-proven + formatter-dogfooded and roll the house out later. The
mechanism is banked either way.
