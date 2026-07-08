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

Design of record for the v2 rewrite. The **v1 prototype is locked in** — it did
its job as a spike and taught us the invariants, hazards, and the one hard
external blocker. This document now folds those findings back into the
production design (§0). Supersedes the v1 architecture.

### Relationship to existing docs

- **`ARCHITECTURE.md`** — describes the v1 monolithic syntax walker that emits
  strings directly. This document supersedes it: the walker is split into a
  pure `Syntax → Doc` pass and a `Style`-driven `Doc → String` renderer.
- **`DESIGN.md`** — is a style guide plus v1 phasing. Its style guide content
  is *not* discarded: it becomes the specification for the **Straylight preset**
  (§6). The phasing is replaced by §13 here.
- **`Lean4Fmt/Emitter.lean`** — the working v1 prototype (~1.3k lines). It is the
  correctness reference for the port. Its final measured behaviour on the
  continuity corpus (via a test harness, not the shipped exe): **0 mangled, 0
  non-idempotent, 0 fallbacks** across all 193 *harness-parseable* files (178
  actively reformatted, 15 already-in-form), every output validated by full
  `lean`. Builds under both `v4.31.0` and `v4.32.0-rc1`. The 10 files it can't
  touch fail at the *parser*, not the emitter (§0.4).

### Step 0 (still true, still the first deliverable)

The shipped executable does **not** use the emitter. `Lean4Fmt.lean` still calls
Lean's `ppModule` and does not import `Lean4Fmt.Emitter`. All prototype results
above ran through a throwaway harness. The first concrete v2 deliverable is to
stand up the pure spine and wire it into the executable, replacing `ppModule`.

---

## 0. Prototype postmortem — what the spike proved

The v1 spike was pushed hard: from "mangles most real files" to clean, idempotent,
meaning-preserving output across the whole continuity tree. The lessons below are
not incidental — they are load-bearing constraints the v2 design must honour.

### 0.1 The correctness spine is two runtime invariants, not just CI gates

Two properties turned out to be the entire game, and both must be *checkable at
runtime*, not merely asserted:

1. **Token-stream preservation.** A formatter may only move whitespace/trivia;
   it must never add, drop, reorder, or merge a token. Reducing "did we mangle?"
   to `tokens(parse(s)) == tokens(parse(format(s)))` caught every structural bug
   we introduced (doubled commas, dropped `mut`, `class`→`structure`, merged
   `let`s) — things that still *parsed* and so slipped past eyeballing.
2. **Idempotency as a fixed point.** `format(format(s)) == format(s)`, byte for
   byte. This is a far sharper tool than it sounds: almost every layout bug we
   had was *invisible in a single pass* and only showed up as drift on the
   second. Idempotency testing is the cheapest, highest-yield bug detector we
   found.

**Production consequence.** These are promoted from "verification obligations"
(§10) to a **runtime safety gate** the driver runs by default (§4.2). Because the
v2 core is meaning-preserving *by construction* via the Doc IR, the gate should
never fire — but it is the seatbelt that guarantees we never emit worse-than-input,
on any corpus, including mathlib, without having to prove the emitter total first.

### 0.2 Almost every idempotency bug was context-dependent indentation

The ad-hoc string emitter had to *guess* the indentation of a continuation from
local state (pending newlines, an ad-hoc `indentLevel`). Nearly every non-idempotency
traced to a wrong guess:

- verbatim blocks re-anchored to the wrong base (first line's indent stripped),
  so nested blocks grew 2 spaces per pass;
- a `+1` indent that is correct after `:= by` but wrong for a `let`-chain tail,
  which must stay column-aligned with its `let`s;
- newlines that lived in a token's *trailing* trivia, so a skipped explicit
  newline silently merged two `let`s.

This is the empirical case **for the Doc IR**: indentation must be *compositional*
(`nest`/`align` around subtrees), computed by the renderer from structure — never
guessed from mutable state mid-walk. Everything in §0.2 evaporates when nesting is
structural. (§4.)

### 0.3 Verbatim reproduction is mandatory — and must itself be idempotent

Whole-language coverage is impossible by active formatting alone: tactic blocks,
`where`/`let rec`, `calc`, custom-syntax DSLs (`[cxx|]`, `[cxxfn|]`), and exotic
match/equation patterns are too many to restyle and too column-sensitive to risk.
The prototype's breakthrough was an **opaque reproduction** path: reproduce any
subtree we don't actively restyle from its original source, re-anchored to the
current indent. This is now a first-class designed component (§4.1), with rules
that were paid for in blood:

- **Strip trailing whitespace only; keep the first line's leading indent** — the
  base-indent must be computed over *all* lines including the first, or
  re-anchoring is not a fixed point.
- **Re-anchor** = dedent to the block's own min indent, re-indent to the current
  level. Emit at the *current* level; never add a context-guessed `+1`.
- **Never introduce a blank** where a newline is already pending (splits bodies
  from heads).
- Prefer `Syntax.reprint`; fall back to the exact source slice
  (`getSubstring?`) when reprint is unavailable (it is, for some nodes, after
  `updateLeading`).

### 0.4 Line comments are a first-class layout hazard

A `--` line comment eats the rest of its physical line. Therefore **nothing that
contains a line comment may ever be flattened/inlined**: doing so lets the comment
swallow an `else`, a `}`, a match arm, or the next list element. In v1 this became
a predicate (`hasLineComment`) gating inlining and routing comment-bearing
`if`/app/list/ctor/struct/match to verbatim. **In v2 this is a renderer law:** a
`group` whose content carries a line comment is *un-flattenable* — it always
renders in break mode. (Doc/Render, §4.)

### 0.5 You cannot format Lean without (partially) elaborating it

The deepest finding of the whole spike, and the one that reshapes the design:
**there is no pure "parse then format" path for real Lean.** A file's own syntax
is not fixed by its imports — it is *extended as the file elaborates*. `notation`,
`macro`, `syntax`, `scoped` declarations, `open`, and `set_option` all mutate the
parser tables, and much surface syntax (mathlib's `Type*`/`Sort*` auto-universe
binder is the canonical example) is only available *after* elaborating the
commands or imports that register it. Parsing and elaboration are interleaved by
construction in Lean — that is what `Lean.Elab.Frontend` does, one command at a
time: parse a command against the current tables, elaborate it (which may extend
the tables), then parse the next.

We proved this the hard way, in two steps:

1. `Lean.Parser.testParseModule` (the harness) is a *test helper*, unfit for
   production: it cannot parse `Type*`/`Sort*` even minimally, does not track
   `namespace`/`open` scope across commands, prints diagnostics to stdout
   (corrupting output), and recovers leniently (silently "succeeding" on
   malformed input).
2. Replacing it with the real **command-loop parser** — `parseHeader` + iterated
   `parseCommand` with a `ParserModuleContext` whose `currNamespace`/`openDecls`
   we advanced by hand — *still* failed: `Mathlib/Logic/Basic.lean` came back
   with 251 of 319 commands carrying missing nodes. The missing tables were the
   ones that only exist after *elaborating* the preceding commands. Hand-tracking
   scope is not enough; the elaborator has to run.

**Consequence — a first-class design constraint.** To format a file, the
`Frontend` must load and run the elaborator over **some prefix/portion of the
full artifact** — at minimum the imports, and in general enough of the file's own
commands to keep the parser tables current. The *exact amount* is
**as-yet-undetermined** and is now an explicit research question (§14.7):

- The **floor** is: process the header (load imports' oleans) — already required,
  already the multi-file-init bottleneck (§12).
- The realistic requirement is the **interleaved frontend**: elaborate each
  command far enough to register any tables it introduces, collecting the parsed
  command `Syntax` as we go, then format the collected syntax. This is heavier
  than a parse and can surface elaboration errors (`sorry`, missing instances)
  that are *not* our concern — the Frontend must collect syntax regardless of
  elaboration success.
- Open optimizations (unmeasured): can we elaborate *lazily* — only far enough to
  keep parsing correct, skipping proof bodies / tactic elaboration? Can a
  per-file **elaboration budget** or a "parse-tables-only" fast path cover the
  common case, falling back to full elaboration on demand?

This does not touch the pure core (`Syntax → Doc → String`) — it makes the
`Frontend` boundary bigger and more expensive, and it sharpens §12: the *parse*
phase is not just contended (global init), it is genuinely *compute-heavy*
(elaboration), which strengthens the case for process-per-file workers over a
shared read-only environment.

Practical fallback in the meantime: the safety gate (§4.2) degrades any file the
current parser can't handle to identity, so shipping without the interleaved
frontend is safe — such files simply pass through unformatted (this is why
mathlib is a safe no-op today, and why the interleaved frontend is deferred with
mathlib).

### 0.6 Toolchain-version sensitivity is real

The emitter built under `v4.31.0` but not `v4.32.0-rc1` until `maxRecDepth` was
raised (the long `emitNode` `if`-chain overflows the elaborator's default in
4.32). The trivia APIs also drift across versions (`Substring.Raw.toString`,
`trimAscii`/`trimAsciiStart` vs `trim`, `getSubstring?`, dependent `String.Pos`).
**v2 must pin the toolchain** and keep trivia access behind `Syntax/Trivia.lean`
so a version bump touches one module, not the whole walker.

### 0.7 The regression corpus (bugs that must never come back)

Each of these was a real, meaning-changing mangle the prototype hit and fixed.
They become golden round-trip + idempotency tests in v2:

| # | Bug | Root cause | v2 guard |
|---|---|---|---|
| 1 | `class C` → `structure C` | hardcoded keyword in structure emitter | emit the actual `structureTk` token |
| 2 | `let mut x` → `let x` | dropped optional `mut` modifier | preserve all binder/decl modifiers |
| 3 | dropped `where` / `termination_by` | value emitter ignored trailing decls | emit full `declVal` incl. suffixes |
| 4 | `⟨a,b⟩` → `⟨a, ,b⟩` | re-emitted comma atoms + own separators | separators come from one source only |
| 5 | `∀ a extra` → `∀ aextra` | binder group emitted without spacing | space-join binders |
| 6 | `fun _ =>` dropped `_` | fun emitter only kept `.ident` binders | emit all binder syntaxes |
| 7 | `importFoo` / `openFoo` | keyword+path with no separator | header/open handlers |
| 8 | comment eats `else`/`}`/arm | inlining a line-comment-bearing node | §0.4 renderer law |
| 9 | equation-def arm dropped | match-alt path lost `⟨…⟩`/`{…}` patterns | opaque reproduction (§0.3) |
| 10 | multi-line `by` flattened in arm | tactic block treated as "simple" | tactic/proof blocks never inline |

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
  | verbatim   (src : String) (baseIndent : Nat)  -- opaque reproduction (§4.1)
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

**Renderer law (from §0.4).** A `group` whose content carries a line comment
(`--`) is *un-flattenable*: it must render in break mode. The walker marks such
groups; the renderer honours it unconditionally. This is not a heuristic — it is
required for meaning preservation, since flattening would let the comment swallow
following tokens.

### 4.1 Opaque reproduction (the verbatim node)

Whole-language coverage requires an escape hatch for constructs we do not (yet)
actively restyle — tactic blocks, `where`/`let rec`, `calc`, custom-syntax DSLs,
exotic patterns (§0.3). This is a Doc node:

```lean
  | verbatim (src : String) (baseIndent : Nat)   -- reproduce source, re-anchored
```

The walker produces `verbatim` for any subtree without an active formatter,
capturing the exact original text (`Syntax.reprint`, or the source slice via
`getSubstring?` when reprint is unavailable). The renderer re-anchors it:

- compute the block's own minimum indent over **all** non-blank lines
  (`baseIndent`), including the first;
- dedent every line by `baseIndent`, re-indent to the renderer's *current*
  indent level — never a context-guessed offset;
- strip trailing whitespace only; do not add a blank when a newline is already
  pending.

Because indent is compositional in the Doc IR (`nest`/`align`), a `verbatim`
node nested inside an actively-formatted context re-anchors correctly and
idempotently by construction — the class of bugs in §0.2 cannot recur. As active
formatters are added over time, they simply replace `verbatim` for those kinds;
coverage grows monotonically and the safety gate (§4.2) guarantees every
intermediate state is still correct.

### 4.2 The runtime safety gate (from §0.1)

The driver wraps single-file formatting in a self-checking gate:

```
format s  ⇒  s'
  require  tokens(parse s) == tokens(parse s')      -- meaning preserved
  require  format s' == s'                           -- idempotent (fixed point)
  require  header(s') imports == header(s) imports   -- imports stay at the top
  otherwise: emit s unchanged (identity is always safe) and flag the file
```

With the v2 Doc core these checks are expected to always pass; the gate exists so
that on *any* input — a mathlib file using a construct we haven't taught the
walker, a future Lean syntax — we degrade to identity rather than to a mangle. It
is the mechanism that lets us honestly claim "never worse than input" on corpora
we have not yet exhaustively covered. (The gate reparses via `Frontend`, §0.5, so
it is only as strong as the parser — another reason `Frontend` must be real.)

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
not. The prototype (§0.1) proved the two runtime invariants below are the
correctness spine; here they are also the CI gates.

- **Doc algebra laws.** `cat`/`nil` monoid; `flatten` distributes over `cat`;
  `group (flatten d) = flatten d`. Provable; pins the renderer.
- **Idempotence.** `format (format s) = format s`, byte-identical, over a corpus.
  The prototype's highest-yield bug detector (§0.1); also the runtime gate (§4.2).
- **Token-stream preservation.** `tokens (parse (format s)) = tokens (parse s)`.
  Strictly stronger than "still parses"; catches drop/merge/reorder that keep the
  file parseable (§0.7). Runtime gate (§4.2) + CI.
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
│   ├── Parse.lean               --   interleaved parse+elaborate (§0.5): run the
│   │                            --   frontend far enough to keep parser tables
│   │                            --   current, collect command Syntax, quietly
│   ├── Gate.lean                --   runtime safety gate (§4.2): token-preserve +
│   │                            --   idempotent + header + degrade-to-identity
│   └── Session.lean             --   how much to elaborate (§0.5/§14.7); superset-env
│                                --   vs process-per-file (§12)
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
- **Parse → the contended *and* compute-heavy phase.** §0.5 sharpened this:
  parsing requires running the elaborator (to keep parser tables current), so
  this phase is not merely gated by global init — it is genuinely expensive.
  Two strategies, decided in `Frontend/Session`:
  1. **Superset environment** — build one `Environment` for the union of imports
     across the tree, once, reuse it read-only per file. Amortizes import load;
     but each file still needs its *own* commands elaborated far enough to parse
     (§0.5), so this helps the header floor, not the per-file elaboration cost.
     Also assumes a coherent closure and that read-only reuse is safe.
  2. **Process-per-file worker pool** — each worker is its own process (fresh
     global state), fed paths over the mesh. Robust against the init trap; costs
     spawn + per-worker env build + per-file elaboration, amortized over many
     files per worker.

  **Lean:** ship (2) first for correctness (it sidesteps the global-init trap
  and parallelizes the *expensive* parse+elaborate too), then pursue (1) as a
  measured optimization. The pure core is unaffected either way — only
  `Frontend/Session` and `Driver/Pool` change. How *little* elaboration we can
  get away with per file (§14.7) directly sets this phase's cost.

---

## 13. Roadmap

- **P-1 — Prototype (done, locked in).** v1 `Emitter.lean` string-walker with an
  opaque verbatim fallback. Reached 0-mangle / 0-non-idempotent / 0-fallback on
  the continuity corpus; builds under 4.31 and 4.32. Its role is over: it is the
  behavioural reference and the source of §0. Not shipped.
- **P0 — Spine.** `Doc/Core` (incl. `verbatim` §4.1 + un-flattenable-comment law
  §0.4) + `Doc/Render` + `Style/*` (Straylight only) + `Frontend/Parse`
  (interleaved parse+elaborate, §0.5) + the runtime safety gate (§4.2). Port v1
  `Emit/*` as a `Syntax → Doc` walker. **Wire into `Main.lean`, replacing
  `ppModule`** (done in prototype form: exe now runs the emitter behind the gate;
  the parser is still the `testParseModule` floor pending §0.5/§14.7). Reproduce
  v1 output on `Bytes.lean`/`CLI.lean`; import the §0.7 regression corpus as
  tests. Round-trip + idempotence + token-preservation gates green.
- **P1 — Alignment & blank lines.** `alignTable` + `Alignment` record;
  `Doc.blank` + `BlankLines` policy. Prove determinism.
- **P2 — Ontology & presets.** `StylePatch` merge; `.lean4fmt.lean` discovery +
  load; `Mathlib` and `Aniva` presets seeded; mathlib4 conformance harness
  online (now unblocked by the real parser).
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
6. **Real parser** — no longer "just a parser," **decided** by §0.5: formatting
   requires *interleaved parse+elaboration* (`Frontend/Parse`), not a standalone
   parser. Hand-tracking `namespace`/`open` scope is insufficient; the elaborator
   must run to register notation. This is the gate that unblocks mathlib.
7. **How much of the artifact must we elaborate?** (§0.5) — open research
   question with real cost consequences (§12). The floor is "load imports"; the
   ceiling is "fully elaborate the file." Candidates to measure: elaborate every
   command but skip proof/tactic bodies; a "extend-parser-tables-only" fast path
   with fallback to full elaboration; a per-file elaboration budget. The answer
   sets the per-file cost of the whole tool and the shape of `Frontend/Session`.

### Deferred: mathlib validation

mathlib's olean cache is fetched (`~/src/vendor/mathlib4`, `v4.32.0-rc1`) and the
emitter compiles under that toolchain, but mathlib is **intentionally deferred**
until we return with a real project tree: it is blocked purely on `Frontend/Parse`
(§0.5), which is P0 work anyway. When P0 lands, the mathlib conformance harness
(§9) comes online with no formatter changes. mathlib will still be there.
```
