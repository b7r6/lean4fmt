# lean4fmt v2 — Design

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // LEAN4FMT // DESIGN // V2
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A flexible, multi-style source formatter for Lean 4, built on a document IR
    with a clang-format-style preset/override ontology, horizontal alignment,
    advanced blank-line policy, and an io_uring-backed parallel driver.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

## Status

Design of record for the v2 rewrite. Subject to the open questions at the end
and to preset-detail work tracked in §11. Supersedes the v1 architecture.

### Relationship to existing docs

- **`ARCHITECTURE.md`** — describes the v1 monolithic syntax walker that emits
  strings directly. This document supersedes it: the walker is split into a
  pure `Syntax → Doc` pass and a `Style`-driven `Doc → String` renderer.
- **`DESIGN.md`** — is a style guide plus v1 phasing. Its style guide content
  is *not* discarded: it becomes the specification for the **Straylight preset**
  (§6). The phasing is replaced by §12 here.
- **`Lean4Fmt/Emitter.lean`** — the working v1 emitter (~1160 lines). It is the
  correctness reference for the port: its output on `Bytes.lean` and `CLI.lean`
  is what the new `Emit/*` + `Doc/Render` spine must reproduce under the
  Straylight preset before we add any new capability.

### Step 0 (a correctness note, not a feature)

The shipped executable does **not** currently use our emitter. `Lean4Fmt.lean`
still calls Lean's `ppModule` and does not even import `Lean4Fmt.Emitter`. The
"immaculate output" validated to date ran through a separate test harness. The
first concrete deliverable of v2 is to stand up the pure spine and wire it into
the executable, replacing the `ppModule` call.

---

## 1. Thesis

The one architectural bet: **insert a Wadler/Leijen-style `Doc` IR between the
syntax walker and the output string**, and split the monolith into

```
walk   : Syntax → Doc          -- pure, expresses INTENT
render : Style → Doc → String  -- pure, decides REALIZATION
```

The v1 emitter conflates walking and rendering — it appends strings through a
hand-rolled pending-newline/pending-space state machine. That produced one
house style cleanly, but it is the wrong shape for *many* styles: every knob
(break-before-vs-after, align-or-don't, wrap-at-width, compact-vs-expanded
`do`) becomes a special case threaded through the walker, and the combinations
multiply.

With a `Doc` IR the walker says "this is a group that *may* break," "these rows
*may* align," "nest the continuation," "a blank line is *wanted* here" — and the
`Style` plus the layout engine decide what actually happens. This is the seam
that makes a large, granular knob set tractable, exactly as clang-format
separates its token annotator / continuation indenter from `FormatStyle`.

The pure core (`Syntax → Doc → String`) is trivially testable, verifiable
(idempotence, round-trip — §10), and parallelizable. Everything messy — Lean's
process-global module init, the filesystem, io_uring — lives *outside* it in
`Frontend` and `Driver`.

---

## 2. Design goals

Ordered. Earlier goals dominate later ones when they conflict.

1. **Meaning-preserving.** `parse (format s)` is structurally equal to `parse s`
   modulo trivia. A formatter that can change semantics is a bug factory. This
   is the hard gate in CI.
2. **Flexible enough for three genuinely different house styles.** The ontology
   must express **Mathlib**, **Aniva**, and **Straylight** with the *same*
   knob set. This is the falsification test: if some knob cannot express the
   difference between two of these styles, the ontology is incomplete (§6).
3. **Format mathlib4 with minimal churn.** Under the `Mathlib` preset, running
   `--check` across mathlib4 should produce a small, principled diff. Validated
   by a corpus harness (§9). This keeps us honest about flexibility and about
   not being secretly opinionated.
4. **Horizontal alignment as a first-class discipline** (§7). Struct fields,
   match arms, `let`/`:=` blocks, record fields, trailing comments. Wired into
   the `Doc` IR from day one, not bolted on.
5. **Advanced blank-line policy** (§8). Blank-line placement is one of the
   biggest levers on Lean readability and one of the most neglected. Treated as
   a first-class subsystem with its own policy record.
6. **Blindingly fast on a whole tree** (§11). io_uring for the I/O ends; a
   shared-nothing core-pinned worker mesh for the parallel work. Honest about
   the one real bottleneck (Lean's process-global parser init).
7. **Idempotent and stable.** `format (format s) = format s`. No oscillation.

---

## 3. Architecture

```
                  ┌─────────────┐
   source ──────▶ │  Frontend   │ ──▶ Syntax        impure: quarantines global-init
                  └─────────────┘
                        │
          ┌─────────────┼───────────────────────────┐
          ▼             ▼                             ▼
   ┌─────────────┐  ┌─────────────┐            ┌─────────────┐
   │  Emit/walk  │  │   Rules     │            │   (later)   │
   │ Syntax→Doc  │  │  lint pass  │            │  range map  │
   └─────────────┘  └─────────────┘            └─────────────┘
          │  ◀── Style (resolved config)
          ▼
   ┌─────────────┐
   │ Doc/Render  │ ──▶ String
   │Style→Doc→Str│
   └─────────────┘
          │
          ▼
   ┌─────────────┐
   │   Driver    │  IO, tree-walk, io_uring, mesh, watch
   └─────────────┘
```

The dividing line is **purity**. Layers L0–L2 (`Syntax`, `Doc`, `Style`,
`Emit`, `Rules`) are pure and depend only on Lean core. Layers L3+ (`Config`,
`Frontend`, `Driver`, `Cli`) are impure and may depend on `StdlibEx.*`.

---

## 4. The Doc IR

A Wadler/Leijen algebra extended with the two capabilities the clarifications
made mandatory: **alignment tables** and **blank-line requests**.

```lean
inductive Doc where
  -- Wadler/Leijen core
  | nil
  | text     (s : String)               -- must not contain '\n'
  | cat      (a b : Doc)                 -- concatenation; monoid with `nil`
  | line                                 -- flat: " "   ; broken: newline+indent
  | softline                             -- flat: ""    ; broken: newline+indent
  | hardline                             -- always newline+indent
  | group    (d : Doc)                   -- try flat; break the whole group if it won't fit
  | nest     (n : Int) (d : Doc)         -- shift the break-indent of `d` by n
  | align    (d : Doc)                   -- set break-indent to the current column
  -- extensions
  | alignTable (spec : ColSpec) (rows : Array Row)  -- horizontal alignment (§7)
  | blank      (req : BlankReq)          -- a *request* for vertical space (§8)
  | flatten    (d : Doc)                 -- force flat rendering of `d`
  | textRaw    (s : String)              -- verbatim (comments): may contain '\n'
```

`cat` with `nil` is a monoid; `flatten` distributes over `cat`; these laws are
provable and pin the renderer (§10).

### Rendering

Rendering is a single recursive walk carrying `(column, indent, mode)` where
`mode ∈ {flat, break}`. `group` performs the standard "does the flattened width
fit in `lineWidth - column`?" test and picks a mode for its subtree.

Two extensions need local, non-standard handling:

- **`alignTable`** — the renderer measures each cell in flat mode, computes
  per-column widths (capped by `Alignment.maxDelta`), and emits padded rows.
  Measurement is *local* to the table, which is exactly the "alignment run"
  semantics we want (§7).
- **`blank`** — the renderer maintains a *pending vertical space* counter,
  separate from the character stream. `hardline`, `line`/`softline` in break
  mode, and `blank` requests all feed it; the counter is resolved against the
  `BlankLines` policy at the next non-blank emission (collapse, clamp to
  min/max, respect context). This generalizes v1's `pendingNewlines` into a
  policy-driven mechanism (§8).

Rendering is pure and total; it never inspects `Syntax`. It is the natural place
to later hang **format-range** (§ open questions) via a position map, but we do
not build that now.

---

## 5. The Style ontology

clang-format resolves `Style ← BasedOnStyle preset ← explicit overrides ←
.clang-format`. We mirror it with three types.

```lean
-- Fully-resolved config the renderer reads. Grouped into sub-records so that
-- --help, docs, and presets stay navigable.
structure Style where
  layout     : Layout       -- width, indent, continuation indent
  breaking   : Breaking     -- where/how to break signatures, binders, do, if
  alignment  : Alignment    -- the alignment discipline (§7)
  blankLines : BlankLines   -- the blank-line policy (§8)
  spacing    : Spacing      -- spaces around operators, in brackets, after kw
  imports    : Imports      -- grouping/ordering of imports
  comments   : Comments     -- `--foo`→`-- foo`, doc-comment placement

-- Overrides / config deltas: the same shape, every field Optional, with an
-- `Append` where the right operand wins on `some`. CLI flags, project config,
-- and per-directory config are all `StylePatch`es merged in precedence order.
structure StylePatch where
  layout     : Option LayoutPatch
  breaking   : Option BreakingPatch
  ...

-- A preset is just a `Style` value (a named base).
def resolve (base : Preset) (patches : List StylePatch) : Style :=
  patches.foldl applyPatch base.toStyle
```

Choice-knobs are enums with `Repr`/`FromString` so config parsing and
`--set group.key=value` are mechanical:

```lean
inductive ColonPlacement | breakBefore | breakAfter
inductive AlignMode      | always | whenShort | never
inductive BlankPolicy    | preserve | impose | normalize
inductive BinderLayout   | oneLine | onePerLine | fill
```

### Config is a `.lean` file (clarification #1)

The project config is Lean source that evaluates to a `StylePatch`:

```lean
-- .lean4fmt.lean
import Lean4Fmt.Style
open Lean4Fmt.Style

def config : StylePatch := Straylight.patch {
  layout    := { lineWidth := 100 }
  alignment := { structFields := .always, matchArms := .whenShort }
  blankLines := { betweenTopLevelDecls := 1, maxConsecutive := 1 }
}
```

Benefits: no config-language parser to build or maintain; presets are ordinary
imports; the full type checker validates the config; `--set` on the CLI is just
another `StylePatch`. Cost: loading config drags in the frontend. Mitigation:
config elaboration is cached per-invocation and is independent of the files
being formatted, so it happens once. `Preset` values themselves are plain data
and require no elaboration for the built-in styles.

---

## 6. Presets (the flexibility test)

Three presets ship, and their *coexistence under one knob set* is the acceptance
test for the ontology (goal #2).

| Preset | Origin | Notes |
|---|---|---|
| **Straylight** | `DESIGN.md` style guide | House style. Width 100, horizontally dense, break-*after* colon, align struct fields and short match arms, assertive-but-tasteful blank-line policy. This is the fully-specified one today. |
| **Mathlib** | reverse-engineered from mathlib4 | Aspirational: tuned until `--check` over mathlib4 yields minimal churn (§9). Consistency of mathlib4 itself is unknown; the harness measures it. |
| **Aniva** | the `aniva` Lean 4 style | A known-clean community style (see `~/src/vendor/Pantograph`). Specifics TBD; captured as a preset once pinned down. Placeholder until then. |

Design consequence: if pinning down **Aniva** or **Mathlib** reveals a
distinction the knob set cannot express, that is a finding — we extend the
ontology, we do not hardcode. The three-preset requirement is deliberately
chosen to stress the ontology early.

> **Straylight style — open thread.** The maintainer has strong, not-yet-fully-
> transcribed beliefs about Lean readability (esp. blank-line discipline and
> alignment). `DESIGN.md` is the current seed; the Straylight preset spec is a
> living document to be filled in.

---

## 7. Alignment subsystem (clarification #3 — required)

Horizontal alignment is a first-class discipline, expressed via the
`alignTable` `Doc` node and governed by the `Alignment` sub-record.

### What gets aligned

| Site | Row shape | Knob |
|---|---|---|
| Struct fields | `[name, ":", type, default?]` | `alignment.structFields` |
| Match arms | `[pattern, "=>", body]` | `alignment.matchArms` |
| `let`/`have` blocks | `[name, ":=", value]` | `alignment.letBlocks` |
| Record-instance fields | `[field, ":=", value]` | `alignment.recordFields` |
| Trailing `--` comments | `[code, comment]` | `alignment.trailingComments` |
| Binder types (opt.) | `[name, ":", type]` | `alignment.binderGroups` |

### Run semantics

An alignment *run* is a maximal sequence of consecutive alignable items with no
interruption. The **walker** groups a run into one `alignTable`; the renderer
measures and pads it. Runs are interrupted by:

- a blank line (blank-lines and alignment interact deliberately — a blank line
  both separates paragraphs *and* resets alignment, matching clang-format's
  `AlignConsecutive*` semantics),
- a non-conforming line (different row shape),
- a comment on its own line (unless trailing-comment alignment is active).

### Guardrails

`AlignMode` controls each site: `.always`, `.whenShort` (align only if the run's
column delta stays under `alignment.maxDelta`), or `.never`. The
`maxDelta` cap directly encodes the `DESIGN.md` rule *"don't align when it would
create excessive whitespace"* — we never produce the ragged
`| .meshDataFromPeer       => …` anti-pattern.

Because measurement happens in flat mode, alignment composes with breaking: a
cell that itself must wrap opts out of the column grid for that row rather than
forcing the whole table wide.

---

## 8. Blank-line subsystem (clarification #3 — required)

> "This is one of the ways Lean is fuckin' unreadable."

Blank lines are modeled as *requests* (`Doc.blank`) resolved by policy, never as
raw newlines emitted by the walker. The `BlankLines` sub-record:

```lean
structure BlankLines where
  policy               : BlankPolicy   -- preserve | impose | normalize
  betweenTopLevelDecls : Nat
  betweenImportGroups  : Nat
  afterNamespaceOpen   : Nat
  beforeNamespaceEnd   : Nat
  beforeDocComment     : Nat           -- blank before a decl's doc comment
  beforeSectionBanner  : Nat           -- blank around box-drawing banners
  afterSectionBanner   : Nat
  betweenDeclKinds     : Bool          -- blank between runs of different decl kinds
  aroundBlockComments  : Nat
  insideDoPhases       : Bool          -- blank between a `let`/`have` run and the tail expr
  maxConsecutive       : Nat           -- clamp runs of blanks
```

`BlankPolicy` sets the overall stance:

- **`preserve`** — honor the author's single blanks; only clamp to
  `maxConsecutive` and strip trailing/leading. Minimal-churn stance (good for
  the **Mathlib** preset).
- **`impose`** — the formatter decides blank placement entirely from policy,
  ignoring the author's blanks. Opinionated stance (candidate for
  **Straylight**).
- **`normalize`** — a middle path: impose the *structural* blanks (between
  decls, around namespaces, import groups) but preserve author blanks *within*
  bodies.

The renderer's pending-vertical-space counter (§4) is where this resolves:
requests and structural hardlines feed the counter; at the next real emission
the policy clamps and contextualizes it. Because it is centralized, we get
"collapse three blanks to one," "exactly one blank between top-level decls," and
"blank before every doc comment" for free and consistently.

---

## 9. Mathlib4 conformance harness (goal #3)

A corpus differential test, in the spirit of `StdlibEx.Proof.differential`.

```
for each file f in mathlib4:
    original  := read f
    formatted := lean4fmt --style Mathlib f
    record diff(original, formatted)      -- via StdlibEx.Bytes.memmem for first-diff
report: files touched, total hunks, churn histogram
```

Goal: drive churn toward a small, *principled* residue (places where mathlib4 is
internally inconsistent and we impose one choice). The harness doubles as:

- a **flexibility check** — large unexplained churn means the `Mathlib` preset
  cannot express mathlib4's conventions, i.e. the ontology is too rigid;
- a **regression guard** — churn must not grow between releases;
- a **fuzz-ish crash test** — the whole of mathlib4 must format without error.

We do the same, at smaller scale, for a corpus in the `aniva` style and for
our own tree under **Straylight**.

---

## 10. Verification obligations

The Doc split makes these *statable*, which the v1 string-append emitter did
not.

- **Doc algebra laws.** `cat`/`nil` monoid; `flatten` distributes over `cat`;
  `group (flatten d) = flatten d`. Provable; pins the renderer.
- **Idempotence.** `format (format s) = format s` over a corpus
  (`differential`-style gate).
- **Round-trip safety.** `parse (format s) ≈ parse s` (structural equality
  modulo trivia). The load-bearing CI gate — a formatter must never change
  meaning.
- **Alignment/blank determinism.** Same input + same `Style` ⇒ byte-identical
  output. No dependence on iteration order or hashing.

Any future `@[extern]` fast path in the renderer's hot loop is gated by
`StdlibEx.Proof.differential` against the Lean reference, per the house Track-A
discipline.

---

## 11. Module tree

Package `lean4fmt`, root namespace `Lean4Fmt.*`, following StdlibEx conventions
(namespace = path, barrel modules, banner comments).

```
Lean4Fmt.lean                    -- lib barrel
Main.lean                        -- executable root (thin: Cli → Driver)
Lean4Fmt/
├── Syntax/                      L0  pure, Lean-core only
│   ├── Kinds.lean               --   SyntaxNodeKind constants + classifiers (isBinOp, …)
│   ├── Trivia.lean              --   leading/trailing extraction, comment detect/normalize
│   └── Query.lean               --   role-based child access, safe indexing
│
├── Doc.lean                     L0  pure, Lean-core only  ── THE NEW CORE
├── Doc/
│   ├── Core.lean                --   the Doc inductive + monoid + laws (§4)
│   ├── Builders.lean            --   sepBy, brackets, joinWith, alignTable helpers
│   └── Render.lean              --   width-aware layout: Style → Doc → String
│
├── Style.lean                   L1  pure, depends on nothing (Render depends on it)
├── Style/
│   ├── Options.lean             --   resolved `Style` + option enums, grouped sub-records
│   ├── Patch.lean               --   `StylePatch` (all-Option) + Append merge semantics
│   ├── Preset.lean              --   Straylight / Mathlib / Aniva
│   └── Resolve.lean             --   resolve : Preset → List StylePatch → Style
│
├── Emit.lean                    L2  pure: Syntax → Doc   (depends Syntax, Doc, Style)
├── Emit/
│   ├── Monad.lean               --   EmitM = ReaderT Style (Writer Diagnostic) building Doc
│   ├── Module.lean              --   header/imports/namespace/section/end
│   ├── Decl.lean                --   def/theorem/abbrev/opaque/axiom/instance + modifiers
│   ├── Command.lean             --   structure/inductive/class + deriving
│   ├── Term.lean                --   app/fun/let/match/if/binop/literals/struct-inst
│   ├── DoNotation.lean          --   do/doSeq/doLet/doLetArrow/doFor/doIf/doMatch
│   └── Tactic.lean              --   (later) by-blocks, tactic seqs
│
├── Rules.lean                   L2  pure lint pass (depends Syntax, Style)
├── Rules/
│   ├── Diagnostic.lean          --   Diagnostic, Severity, render (moved out of v1 Emitter)
│   ├── Trivia.lean              --   trailing-ws, comment spacing, file-ending
│   └── Naming.lean              --   (later) naming, import ordering
│
├── Config.lean                  L3  loads .lean4fmt.lean → StylePatch
├── Config/
│   ├── Discover.lean            --   walk up dirs for .lean4fmt.lean (like .clang-format)
│   └── Load.lean                --   elaborate the config file to a StylePatch (cached)
│
├── Frontend.lean                L3  IMPURE quarantine — the global-init reality
├── Frontend/
│   ├── Parse.lean               --   source → Environment → Syntax (replaces ppModule path)
│   └── Session.lean             --   superset-env / process-per-file strategy
│
├── Driver.lean                  L4  IMPURE orchestration — StdlibEx.{IOUring,Fanotify,Logging,Fifo}
├── Driver/
│   ├── Format.lean              --   single file: parse → emit → render → string
│   ├── Check.lean               --   diff vs disk (StdlibEx.Bytes.memmem first-diff), exit codes
│   ├── Walk.lean                --   discovery via StdlibEx.Linux.Fanotify.scanTree
│   ├── Io.lean                  --   batched read/write via StdlibEx.IOUring.Loop
│   ├── Pool.lean                --   parallel workers via StdlibEx.IOUring.Mesh + Fifo (incubator, §11.2)
│   └── Watch.lean               --   format-on-change via Fanotify
│
└── Cli.lean                     L5  arg schema-as-data via StdlibEx.CLI; builds StylePatch
```

DAG, bottom-up: `Syntax`,`Doc` → `Style` → `Emit`,`Rules` → `Config`,`Frontend`
→ `Driver` → `Cli`/`Main`. Nothing in L0–L2 touches IO or `StdlibEx`.

### 11.1 StdlibEx adoption, staged

`StdlibEx.*` sits *below* lean4fmt in the project DAG (root namespace
`StdlibEx.*`, no upward edges). Adopt in stages so the pure core never blocks on
the substrate.

| Stage | Edge | Consumer | Payoff |
|---|---|---|---|
| 1 (now) | `StdlibEx.CLI` | `Cli.lean` | schema-as-data arg surface; dogfoods the parser |
| 1 (now) | `StdlibEx.Bytes.memmem` | `Driver.Check` | fast first-differing-region diff; round-trip byte compare |
| 2 | `StdlibEx.Linux.Fanotify.scanTree` | `Driver.Walk` | `(path, mtime, size)` discovery + mtime skip-cache |
| 2 | `StdlibEx.Logging` | `Driver.*` | structured `--verbose` output |
| 3 | `StdlibEx.IOUring.Loop` | `Driver.Io` | batched open/statx/read/close + batched writes |
| 4 | `StdlibEx.IOUring.Mesh` + `Datastructures.Fifo` | `Driver.Pool` | shared-nothing core-pinned workers |
| test | `StdlibEx.Proof.differential` | verification | gate any `@[extern]` renderer fast path |

### 11.2 Parallelism primitive incubation (clarification #4)

The core-pinned worker-pool abstraction (`Mesh` + `Fifo` work queue + `MSG_RING`
handoff) is **incubated in `Driver/Pool.lean`**. Once its interface is clean and
proven on a real workload, it is promoted into `StdlibEx` (candidate home:
`StdlibEx.IOUring.Mesh` helpers, or a new `StdlibEx.Parallel`). We do not design
the general abstraction up front; we grow it from the formatter's concrete need
and lift it when it stops changing.

---

## 12. io_uring reality (honest version)

io_uring is not a "parallel format" button. The actual bottleneck: **parsing
needs a Lean `Environment` with the file's imports' syntax extensions, and
Lean's module init is process-global and not re-entrant** (`interpretedModInits`
— the documented multi-file limitation in `DESIGN.md`). That constrains the
*parse* phase, not the *emit* phase.

- **I/O ends → io_uring's home turf.** Reading N files, writing N formatted
  files, the watch-mode change feed — classic batched I/O; `IOUring.Loop`
  collapses each to one syscall per iteration. Uncomplicated win.
- **Emit/render → embarrassingly parallel, pure.** `Syntax → Doc → String` has
  no shared state; distribute work units across core-pinned `IOUring.Mesh`
  workers via `MSG_RING`. This is where the speed actually comes from once
  files are parsed.
- **Parse → the contended phase.** Two viable strategies, decided in
  `Frontend/Session`:
  1. **Superset environment** — build one `Environment` for the union of imports
     across the tree, once, reuse it read-only per file. Fast, single-process;
     assumes a coherent closure and that read-only reuse is safe across files
     (needs validation).
  2. **Process-per-file worker pool** — each worker is its own process (fresh
     global state), fed paths over the mesh. Robust against the init trap; costs
     spawn + per-worker env build, amortized over many files per worker.

  **Lean:** ship (2) first for correctness (it sidesteps the global-init trap
  and parallelizes the *expensive* parse too), then pursue (1) as a measured
  optimization. The pure core is unaffected either way — only `Frontend/Session`
  and `Driver/Pool` change.

---

## 13. Roadmap

- **P0 — Spine.** `Doc/Core` + `Doc/Render` + `Style/*` (Straylight only). Port
  v1 `Emitter.lean` into `Emit/*` as a `Syntax → Doc` walker. **Wire into
  `Main.lean`, replacing `ppModule`.** Reproduce v1 output on `Bytes.lean` and
  `CLI.lean` byte-for-byte. Round-trip + idempotence gates green.
- **P1 — Alignment & blank lines.** `alignTable` + `Alignment` record;
  `Doc.blank` + `BlankLines` policy. Prove determinism.
- **P2 — Ontology & presets.** `StylePatch` merge; `.lean4fmt.lean` discovery +
  load; `Mathlib` and `Aniva` presets seeded; mathlib4 conformance harness
  online.
- **P3 — Driver I/O.** `StdlibEx.CLI` arg surface; `Bytes.memmem` diffs;
  `Fanotify.scanTree` discovery; `Logging`.
- **P4 — Parallelism.** `IOUring.Loop` batched I/O; `IOUring.Mesh` worker pool
  (incubator). Watch mode.
- **P5 — Promotion.** Lift the clean worker-pool primitive into `StdlibEx`.

---

## 14. Open questions

1. **Straylight style spec.** The maintainer's readability beliefs (blank-line
   discipline, alignment) need transcription into the Straylight preset. `DESIGN.md`
   is the seed. (Owner: maintainer.)
2. **Aniva style.** Pin down the concrete rules before writing the preset.
   Reference corpus: `~/src/vendor/Pantograph`.
3. **Mathlib preset tuning.** Iterative, harness-driven (§9). How much residual
   churn is "acceptable" needs a number.
4. **Superset-env safety.** Validate whether one read-only `Environment` can
   safely re-parse many files, or if (2) process-per-file is mandatory.
5. **Format-range** (`--lines a:b`, clang-format style). **Deferred**
   (clarification #5): not worth trouble on its own. Kept in mind only insofar
   as it might tip an otherwise-marginal design choice in `Doc/Render`'s
   position handling; we do not build the position map preemptively.
```
