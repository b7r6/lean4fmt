# lean4fmt — Architecture (as built)

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // LEAN4FMT // ARCHITECTURE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A multi-style, canonicalizing source formatter for Lean 4: a pure
    Syntax → Doc walk, a Style-driven Doc → String renderer with proven
    content laws, a runtime safety gate, and a perturbation fuzzer that
    measures the canonicalization property directly.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

This document describes the system **as built** (~8.4k lines under
`Lean4Fmt/`). `DESIGN_V2.md` is the design of record and rationale; this is
the map of what exists, what is measured, and what remains. The v1 prototype
this file used to describe lives on only as `Lean4Fmt/Emitter.lean` (the
correctness reference for the port) and as the postmortem in `DESIGN_V2.md §0`.

---

## 1. The one-paragraph theory

A formatter is a function from **parse trees** to **bytes**. Our target
property — stronger than "pretty" and stronger than "safe" — is
**canonicalization**: for a fixed style, the output is a function of the parse
tree and the comment attachments *only*. Two sources that parse identically
(differing in whitespace trivia) must format identically; formatting is a
projection onto one fixed point per equivalence class. Safety (token/tree/
comment preservation, idempotence) is enforced at runtime by a gate; canonical
convergence is *measured* by a perturbation fuzzer. Everything else in the
system — the Doc IR, the seam model, verbatim re-anchoring, the respacing
engine — exists to grow the actively-formatted surface without ever violating
those two.

## 2. Pipeline

```
                 ┌────────────────────────────────────────────────────────────┐
  source bytes   │ Frontend (Lean4Fmt/Frontend/*)                             │
──────────────►  │  Parse.lean    cheap testParseModule (no elaboration)      │
                 │  Session.lean  elaborating fallback (same-file notation)   │
                 │  Env.lean      shared batch env (one union importModules)  │
                 │  Gate.lean     formatSafe — the runtime safety gate        │
                 └───────────────┬────────────────────────────────────────────┘
                                 │  Lean.Syntax (updateLeading applied)
                 ┌───────────────▼────────────────────────────────────────────┐
                 │ Emit (Lean4Fmt/Emit/*)          pure, open recursion       │
                 │  walk : Syntax → EmitM Doc                                 │
                 │   ├─ dispatch by kind → category emitters                  │
                 │   │    Module / Command / Decl / Term / DoNotation /       │
                 │   │    Tactic / Binders  (each takes `walk` as parameter)  │
                 │   ├─ default: single-line nodes respace via tokenJoin?     │
                 │   ├─ interception: single-line whole-node bails re-join    │
                 │   └─ fallback: verbatim (opaque reproduction, logged)      │
                 └───────────────┬────────────────────────────────────────────┘
                                 │  Doc  (+ Array Diagnostic)
                 ┌───────────────▼────────────────────────────────────────────┐
                 │ Render (Lean4Fmt/Doc/*)         pure, total, proven        │
                 │  group fit / nest / align / alignOr grids / fillSep /      │
                 │  blank clamping / verbatim re-anchoring /                  │
                 │  string-aware trailing-ws strip                            │
                 └───────────────┬────────────────────────────────────────────┘
                                 │  String
                 ┌───────────────▼────────────────────────────────────────────┐
                 │ Gate (§5): reparse → tokens, kind spine, comment content,  │
                 │ header imports, fixed point — else emit the input          │
                 └────────────────────────────────────────────────────────────┘
```

The driver (`Lean4Fmt/Driver/*`) wraps this per-file unit with fmt.lean
discovery, a pooled batch pass over a shared frozen environment, parallel
subprocess retry for env-conflict files, `--write/--check/--stats` modes, and
a watch mode. `Cli.lean` + `Log.lean` (pure-Lean leveled logging) are the exe.

## 3. Module tree

```
Lean4Fmt/
  Doc/            The document IR and renderer (the proven core)
    Core.lean       Doc constructors (total: containers hold Lists)
    Render.lean     flatWidth, go/goFill/goCells, wrBlock re-anchoring,
                    hasMultilineVerbatim vs hasMultilineReanchor,
                    stripTrailingWs (string-aware), stats
    Content.lean    content function (the T1 invariant's right-hand side)
    Seam.lean       seam kit: splitLines/trimEndWs/dedent, leadingSep?
    Builders.lean   commaList and friends
  Emit/           Syntax → Doc (the walker + category emitters)
    Monad.lean      EmitM, Walk, bareSrc, verbatim/verbatimQuiet, armsAligned
    Tokens.lean     leafTokens, gapRule, tokenJoin?, tokenJoinFlat?, canonTok
    Binders.lean    shared binder kit (binderText?/binderDoc)
    Module.lean     header, top-level rhythm, module trivia canonicalization
    Command.lean    structure/inductive/class ctor+field loops, §7 item grids,
                    mutual, trivial commands
    Decl.lean       declarations: sig, valForm placement, eqns, instance,
                    example, where
    Term.lean       expression space: binops/chains, match, let-chains, ite,
                    quantifiers, lists/tuples/structInst + comma seams
    DoNotation.lean do statements, doLet/Arrow/LetRec/Reassign, doIf/doMatch/
                    doFor, stmts?/seqLinesDoc?/branchDoc?
    Tactic.lean     by-blocks, bullets, ; chains, per-tactic ports
  Syntax/         Read-only syntax utilities
    Trivia.lean     leading?/trailing?/lastTokenTrailing?, comment counting
    Kinds.lean      ownsSeams, isNeverInline, hasUnownedLineComment,
                    hasUnownedInteriorComment
    Query.lean      leafToks, kindSpine, commentContent (gate predicates)
  Style/          The style ontology
    Options.lean    Style record: layout/breaking/alignment/blankLines/
                    spacing/imports/comments axes
    Preset.lean     straylight (house), aniva, purtell — all PRESCRIPTIVE
    Config.lean     fmt.lean DSL: parse + applyEntry (single source of keys)
    Resolve/Patch   preset resolution + field-wise overrides
  Frontend/       Parse + gate (see §2, §5)
  Driver/         Discovery, pooling, IO, watch; corpus-gate.sh is the CI gate
  Rules/          Lint diagnostics (naming, trivia) — separate from layout
  Proofs.lean     T1–T4 content laws over the ACTUAL renderer (no model)
  Emitter.lean    v1 prototype (locked; reference only)
fuzz/
  perturb.py      parse-preserving trivia mutator (content pins encoded)
  fuzzone.sh      per-file fuzz driver (spine-filtered)
corpus-gate.sh    shipping-exe gate: double --write idempotence + coverage
```

## 4. The Doc IR and renderer

`Doc` is a Wadler/Leijen-style document with additions that carry this
system's specific obligations:

- `text` — active layout output (canonical bytes).
- `textRaw` — comment content, byte-exact, **placement-stable**: multi-line
  textRaw emits its lines raw at their source columns; it does not re-anchor.
- `verbatim src baseIndent` — opaque reproduction (§4.1 of DESIGN_V2): the
  safe fallback for unported constructs. Multi-line verbatim **re-anchors**:
  the renderer dedents by `baseIndent` and re-indents at the placement column.
  This distinction (re-anchoring vs raw) is load-bearing: a mutual member may
  contain a multi-line docstring (`textRaw` — harmless) but not a multi-line
  `verbatim` (drifts at +2); `hasMultilineVerbatim` vs `hasMultilineReanchor`
  encode exactly this.
- `group` / `line` / `softline` / `hardline` / `nest` / `align` / `flatten` —
  the classical fit machinery. `flatWidth` is *exact* (proved, T2), so a
  group's fit check is an oracle, not a heuristic.
- `blank n` — a blank-line *request*, clamped by policy at render time;
  pending-newline accumulation means a blank followed by a hardline is still
  one blank (this collapse is what makes glued `:= do` bodies compose).
- `alignTable` / `alignOr` — the §7 alignment subsystem: padded grids chosen
  at render time iff the column delta ≤ `maxDelta` AND every padded row fits;
  `alignOr` falls back to an ordinary layout otherwise. Grids are taken only
  when grid content decidably equals fallback content (coherence by
  construction).
- `fillSep` — pack-and-wrap for literal pools (byte tables, long `open`
  lists, fill-mode constructor parameters).

**Totality and proofs.** The Doc core is total (structural mutual recursion,
no fuel), and `Proofs.lean` states the laws about *these* functions:

- **T1 (unconditional)** `nonWs (render style d) = content d` — rendering can
  only move, insert, or collapse whitespace. No hypotheses; content is defined
  over verbatim/textRaw payloads too.
- **T2** `flatWidth d = some n` → the flat render is one newline-free string
  of length exactly `n` (fit-check exactness). Proving it found two real
  fit-oracle bugs.
- **T3** `leadingSep? lead = some d → content d = nonWs lead` — the seam kit
  cannot eat a comment; the comment-eater class is a compile error.
- **T4** writer hygiene (no trailing indent without content).

The renderer ends with `stripTrailingWs`: a lexical-mode scanner (strings,
raw strings, char literals, nested block comments) that drops trailing
whitespace at every line end **except** inside string literals (token
content) and inside doc comments (`/--`/`/-!` — their text is a leaf token;
stripping there changes the token stream). This is what makes verbatim blocks
canonical at line ends.

## 5. The runtime safety gate

`Frontend/Gate.lean::formatSafe` keeps the active output only if **all** hold
after reformatting and reparsing:

1. **Tokens** — `leafToks` equal (no token added/dropped/merged).
2. **Kind spine** — preorder node kinds equal (identical tokens can re-scope
   in whitespace-sensitive regions — tactic bullets, branches).
3. **Comment content** — whitespace-blind comment bytes equal.
4. **Header** — imports stay in the header.
5. **Fixed point** — `format (format s) = format s`, byte-for-byte.

Otherwise the *input* is emitted unchanged, with a diagnostic. The gate is the
seatbelt that lets partial construct coverage ship: a wrong port degrades to
identity on the affected file, never to damage.

**What the gate cannot see** — and the checks that cover the difference:

- The gate's comment check is content-based; a *dropped-then-identical* pass
  can hide a comment moved into oblivion on files the gate rejects late. The
  **comment diff check** (emit each changed file, compare `--` counts against
  the source) runs every round that touches comment guards. It has caught
  three silent comment-eaters the gate passed.
- The gate cannot distinguish "canonical" from "carries origin bytes" — that
  is the fuzzer's job (§7).

The shipping-tool gate is `corpus-gate.sh`: copy the corpus, `--write` twice,
diff the passes, print coverage. CI-invocable, exits nonzero on any drift.

## 6. The walker: dispatch, seams, verbatim, respacing

### Dispatch

`Emit.walk` is the single recursion point. Category emitters are
**open-recursion** functions taking `walk` as a parameter (Lean cannot have
mutual recursion across modules). A handler is *only* reachable if its kind is
in the dispatch chain in `Emit.lean` — a complete handler with no dispatch
entry silently falls through to the default (this has burned us repeatedly;
when a handler "mysteriously bails", grep the dispatch first).

The **default** for undispatched kinds: a single-line node rides as active
text, respaced through `tokenJoin?`; a multi-line node reproduces verbatim.
This is what makes literals, types, and custom notation active without
per-kind ports. A **walk-level interception** extends the same rule to
dispatched-but-bailed nodes: if an emitter returns a single-line whole-node
verbatim, the walk re-joins it canonically.

### Token respacing (`Emit/Tokens.lean`)

`tokenJoin?` renders a single-line construct from its leaf tokens with
canonical gaps: a pair-rule table (`gapRule`) decides glue-vs-space for known
pairs (openers glue right, `,`/`;` glue left and space right, `:=`/`=>`
space both sides, ident-`(` spaces); otherwise the source gap's *evidence*
decides (whitespace gap → one space, zero gap → glued). Three hard-won rules:

- Zero gaps need **positive trivia evidence** (both neighbors' trivia lookups
  present) — synthetic-info tokens would otherwise glue and relex.
- **Skipped empty leaves carry trivia**: cdot expansions insert synthetic
  `[anonymous]` idents whose trailing holds the real space; their trivia folds
  into the next gap (else `(· + ·)` glues).
- `choice` nodes (ambiguous parses) duplicate tokens when flattened — bail.

`canonTok` (= `tokenJoin?` with a bareSrc-trim fallback) is the standard
spelling for every emitted head piece. The recurring origin-carrier pattern:
any `(bareSrc x).trimAscii` used as *emitted* text carries source spacing —
swap to `canonTok` when it is an emission, keep it when it is a guard.

### The seam model

Comments and blank lines between structural items belong to exactly one owner
(the *seam*). Statement loops (do-blocks, ctor lists, field lists, let-chains,
match/eqns arms, mutual members) place each item's leading trivia structurally
(`leadingSep?` — T3-protected) and re-append same-line trailing comments.
`Syntax/Kinds.lean::ownsSeams` lists the kinds whose emitters do this;
the comment-hazard guards (`hasUnownedLineComment` for term entry,
`hasUnownedInteriorComment` for arm sites) count only comments *nobody* owns.
Two subtleties encoded there:

- A seam-owning descendant's **head-leading** is the parent's zone, not the
  child's interior (a comment between `=>` and a `match` body was silently
  dropped before this distinction).
- An emitter whose layout has no seam for a slot's **tail trailing** must
  check `lastTokenTrailing?` of that slot and bail (ite/dite: `then x -- note`
  before `else`).

### Verbatim and its hazards

`verbatim` logs an opt-out diagnostic (the census trail, `--log-level debug`);
`verbatimQuiet` is for speculative probes. Multi-line verbatim re-anchors —
correct at any placement column for its *own* content, but a whole *mutual
member* reproduced verbatim drifts at +2, so the mutual bails on
`hasMultilineReanchor` members (verbatim only — multi-line docstrings are
`textRaw` and placement-stable; counting them kept every documented mutual
verbatim for months).

## 7. The zero-passthrough campaign: fuzzer, pins, instruments

**Directive**: zero passthrough. Every knob set is a canonical function —
one fixed point per parse tree, origin-agnostic.

**The metric** is the perturbation fuzzer (`fuzz/perturb.py` +
`fuzz/fuzzone.sh`): mutate a file's trivia parse-preservingly (trailing
spaces, doubled inner gaps, blank-run extensions), filter mutations that break
the parse (spine comparison), and assert
`format(perturbed) == format(original)`. Failures are the ranked work queue.

**Content pins** (user decisions the fuzzer must respect — these are *not*
formatter bugs):

1. **Blank lines**: adjacency between one-liner top-level decls is content;
   all other top-level gaps canonicalize to exactly
   `blankLines.betweenTopLevelDecls`.
2. **Comment interiors** are content, byte-exact, including their blank
   lines. (Trailing whitespace at comment line ends is not content — the
   strip applies; the gate's whitespace-blind `commentContent` agrees.)
3. **Quasiquotation** is content: `macro_rules`/`syntax`/`notation`/`elab`
   quotations and DSL templates (`[hs_decl| … |]`) stay byte-exact; the
   perturber's state machines skip them.
4. **Presets are prescriptive**: preservation values are banned from presets
   (`preserve*` axes exist only as fmt.lean migration keys).

**Instruments** (the debugging toolkit that emerged, in escalation order):

1. *Aggregate census* — collect first-diff-hunks over all failures, classify
   by first token / shape; port the dominant class.
2. *Opt-out trail* — `--log-level debug` names the bailing kinds and byte
   positions. Caveat: the walk interception replaces some logged bails, so
   the trail over-reports verbatim for single-line nodes.
3. *Poison-chain bisection* — for a file that stays verbatim against
   expectations: drop members/arms on a copy until it activates; then
   distinct-rule diagnostics on each bail site of the suspect emitter; log
   **all** poisoners, not the first (an early return hides the second).
4. *Perturbation markers* — byte-equality is an invalid activation probe on a
   dogfooded corpus (active §7 grids reproduce hand-aligned bytes exactly);
   inject a targeted double-space and test survival instead.

**The verification loop** (every round): `lake build` → corpus sweep (222 OK /
0 fail expected; 12 PARSEFAIL are a harness limitation, the shipping exe
parses them via the elaborating fallback) → comment diff check on changed
files → core fuzz (40 files × 3 seeds) → full-corpus fuzz (234 × 3) →
`corpus-gate.sh` → dogfood `--write` to fixpoint → commit → memory.

## 8. Style ontology

`Style` is a record of orthogonal axes (`layout.*`, `breaking.*`,
`alignment.*`, `blankLines.*`, `spacing.*`, `imports.*`, `comments.*`).
Presets are complete Styles; `fmt.lean` files (valid Lean, parsed never
executed) patch fields along the directory chain, nearest wins, `preset`
resets. `Style/Config.lean::applyEntry` is the single source of truth for the
key space — unknown keys are loud per-file errors.

Presets: **straylight** (house: 100 cols, 2/4 indent, breakBefore colon,
onePerLine binders, whenShort grids with maxDelta 16, normalize blanks),
**aniva** (Pantograph-shaped), **purtell** (lithe-shaped) — all prescriptive.
The measured structural finding: preserve-based styles cannot round-trip
through a prescriptive wash (break info is destroyed); the achievable contract
is direct `HEAD → author-style = HEAD`, and origin-agnosticism ≡ active
coverage (verbatim residue is exactly where the wash test disagrees).

## 9. Progress ledger

Chronological, each stage gate-verified and dogfooded (see `git log` for the
per-commit detail; `MEMORY`/session notes hold the pitfalls):

| Stage | State |
|---|---|
| v1 prototype | locked; postmortem in DESIGN_V2 §0 |
| v2 spine (Emit→Doc→Render + gate) | shipped; corpus 234/234 |
| Construct ports (decls, do, match, structure/inductive/instance, tactics, terms) | coverage 22.4% → 68.9% |
| Proof spine (T1–T4) | all four laws hold, zero sorries; found 3 real bugs |
| Batch perf | 234 files in 3.7s / 1.4GB (pooled shared env + retry waves) |
| fmt.lean config + presets + blank rhythm + bodyOwnLine | shipped (review-loop items) |
| Milestone 1: daily driver on Continuity | closed (dogfood commit `7637744`) |
| Milestone 2 opened: aniva/purtell cut prescriptive | Pantograph/lithe direct-wash measured |
| Zero-passthrough: respacing engine + fuzzer | core set 92/120 → **0/120** (`8848c74`) |
| Full-corpus ledger | 227 → 160 (fuzzer honesty) → 144 → 123 → 114 → 110 → 102 → **0/702** (`9a170bb`) |
| Coverage | **78.4%** code-active; honest ceiling ≈81% (strings/quasiquotes/moduleDoc are correctly verbatim forever) |

Current head: `9a170bb` (+ dogfood `27cdc9b`). **The campaign's primary goal is
closed**: zero fuzz divergences over the whole non-vendor tree (347 files × 3
seeds; the 234-file corpus metric is 0/702). The closing move was the LEXICAL
whitespace canon (`canonVerbatimWs`, §6): opaque verbatim content and every
bareSrc emission fallback collapse interior space runs and blank runs
string/comment/template-aware, so even UNPORTED constructs are canonical
functions of tokens+comments. Quotation constructs (`Term.quot`/`dynamicQuot`,
`macro_rules`/`syntax`/`notation`/`elab` families — `Syntax.hasQuotationKind`)
and DSL templates (`[ident| … |]`, a scanner mode) ride byte-exact per the
quasiquotation pin. Consequence shipped in `27cdc9b`: hand-padded alignment
inside verbatim regions de-aligns — alignment is the emitter's to re-derive
(armsAligned/alignTable), not origin bytes to preserve.

## 10. Future work

Ordered by the standing plan; each item names its acceptance instrument.

1. ~~**Full-corpus fuzz → 0/702**~~ **DONE** (`9a170bb`): the lexical ws-canon
   closed the whole tail in one move — see §9. Standing follow-ups: (a) grid
   RE-alignment for comment-interleaved arm sets (the de-aligned
   `CxxType.render`-style tables want a comment-tolerant `armsAligned`); (b)
   cosmetic: eqns arm body `do` placement is inconsistent (single-statement
   do breaks to its own line; semicolon-do stays inline) — unify under
   `breaking.compactDo`. The fuzzer stays in CI position: any new emitter
   must keep the tree at 0.
2. **Vendor wash test** — the cross-style origin-agnosticism endpoint:
   straylight → aniva vs direct-to-aniva byte-identical on Pantograph (and
   purtell/lithe), once the corpus converges. Task #5 (lithe do-body indent
   anchoring, 16 files) folds in here.
3. **v2 spacing-table extension** (task #6 close-out) — grow `gapRule` as the
   census demands; no quirk special-cases, legitimate spellings only
   (clang-format is the axis-richness north star).
4. **Knob line**: attribute placement, record comma style (leading/trailing),
   indent width de-hardcoding (`nest 2` is scattered), short-body/short-arm
   thresholds, binder packing. Several Style axes exist but are inert —
   wiring them is measurement-driven (a knob that only fires on the active
   path reads as nondeterministic taste; check span paths too).
5. **`preserveToplevelBlankLines`** — permitted only if measured to buy a
   large negative diff on the golden corpora. Measure before adding.
6. **Milestone 2 plumbing**: `lake env` discovery to replace the hand-built
   LEAN_PATH olean farm; packaging (flake/lake dep); foreign-corpus gate
   runs and burn-down.
7. **Linting phase** (roadmap step 3): run `Rules/*` on ourselves; grow the
   rule set.
8. **Mathlib4** (final boss, explicitly conditional): the verbatim-fallback +
   gate architecture makes it plausible; parsing requires its built env
   (union-import + pooled format projects to minutes); decide scope after
   milestone 2.
9. **Renderer debt** (accepted, documented): continuation-aware `fits` —
   currently zero observable symptoms, deliberately not built; forall
   binder-fill (one over-width line corpus-wide).
10. **StdlibEx logging shim** — `log.cpp` must compile with Lean's clang
    (GNU-ABI libstdc++ vs Lean's libc++ dual-runtime abort, DESIGN_V2
    decision VII); lean4fmt uses pure-Lean `Log.lean` until then.

## 11. Operational notes

- Fuzz/sweep harness: canonical copies in `fuzz/`; runtime copies live in
  `/tmp` (`corpus.list`, `corefuzz.list`, `v2harness.lean`, `perturb.py`,
  `fuzzone.sh`) with `MERGE=/tmp/treefarm` (symlink olean farm) and `CORE` =
  the nix Lean libdir — ephemeral, rebuild if missing. Always run from repo
  root with an absolute `FMT_LIB`.
- Never batch many files into one lean process with per-file `processHeader`
  (import closures accumulate; it has OOM-crashed the machine). One process
  per file, `xargs -P` bounded.
- The 12 PARSEFAIL files in `/tmp`-harness sweeps are a harness limitation
  (testParseModule cannot see same-file notation); the shipping exe formats
  them via the elaborating fallback, and `corpus-gate.sh` covers them.
- Config knob tests must use the real exe with `-w` (default mode prints to
  stdout; the /tmp harness bypasses fmt.lean discovery entirely).
