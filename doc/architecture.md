# Architecture

This chapter maps the design laws onto the production tree. It is descriptive:
when this chapter and the implementation disagree, fix the chapter or the code
in the same change. Rationale belongs in [the design](design.md); historical
measurements belong in [the campaign](campaign.md).

## 1. System boundary

The formatting unit accepts source bytes, a target path, an imported Lean
environment, and a resolved style. It returns bytes, diagnostics, and coverage
accounting. It does not write the file.

```text
source + path + environment + style
                │
                ▼
       parse / elaborate frontend
                │ Syntax + source ranges
                ▼
        structural emitter walk
                │ Doc + diagnostics
                ▼
          style-aware renderer
                │ candidate bytes
                ▼
           runtime safety gate
                │
       candidate or original source
```

The driver owns discovery, configuration, concurrency, reporting, and writes.
This boundary is deliberate: orchestration may decide *when* a file is
processed, but never *what its syntax means* or *how its layout is chosen*.

## 2. Source tree

```text
lean_4_fmt/
├── casing.lean             pure casing conversion
├── cli.lean                command-line schema and parsing
├── config/                 executable configuration support
├── doc/
│   ├── core.lean           document algebra
│   ├── builders.lean       common combinators
│   ├── content.lean        content and width analysis
│   ├── seam.lean           comment/trivia ownership
│   └── render.lean         total style-aware renderer
├── driver/
│   ├── format.lean         frontend-to-gate formatting unit
│   ├── config.lean         project policy discovery
│   ├── check.lean          fixed-point reporting
│   ├── job.lean            file work description
│   ├── pool.lean           bounded parallel execution
│   ├── walk.lean           tree discovery
│   └── io.lean             mutation boundary
├── emit/
│   ├── module.lean         module assembly
│   ├── command.lean        command families
│   ├── decl.lean           declarations and equations
│   ├── term.lean           term grammar
│   ├── binders.lean        binder groups
│   ├── do_notation.lean    do-statement families
│   ├── tactic.lean         tactic grammar
│   ├── tokens.lean         leaf canonicalization
│   └── ws_sensitivity.lean known whitespace-content classes
├── frontend/
│   ├── env.lean            imported environments and batch sessions
│   ├── parse.lean          cheap parser path
│   ├── session.lean        interleaved parse/elaboration fallback
│   └── gate.lean           candidate validation and identity fallback
├── rules/                  diagnostics, trivia, naming, house lint
├── style/                  options, presets, patches, resolution, laws
├── syntax/                 kind registry and syntax/trivia queries
├── rename.lean             pure naming plans and identity rewrites
└── proofs.lean             executable and stated document laws

main.lean                   batch driver and project rename orchestration
```

Barrel modules expose subsystem boundaries. Lower layers do not import the
driver. The document algebra imports no Lean frontend state.

## 3. Frontend

### 3.1 Environment construction

The target repository determines the Lean toolchain and import world. The
frontend builds an environment from the module header and search path. Batch
work shares a compatible frozen environment; incompatible import worlds are
isolated rather than merged optimistically.

The executable is built with interpreter support because imported syntax may
register initializers required by parsing.

### 3.2 Graduated parsing

The cheap path parses the module against imported syntax. It handles ordinary
files without paying for elaboration. If commands introduce syntax used later in
the same file, the session path invokes Lean's interleaved frontend. Proof bodies
are elaborated as `sorry` for table discovery: the syntax remains original while
irrelevant proof search is avoided.

Both paths reject missing syntax nodes. Recovery output is not a source tree.

### 3.3 Source evidence

Syntax alone is insufficient for a source transformer. The frontend retains
source ranges, leading trivia, comment attachment information, and leaf-token
spelling. These facts support opaque reproduction, token comparison, coverage
attribution, and identity-aware renaming.

## 4. Emission

`Emit.walk` is open recursion: category emitters receive the recursive function
instead of importing each other cyclically. Dispatch is by registered syntax
kind. A handler returns a `Doc` and diagnostics in the emission monad.

The fallback hierarchy is:

1. structurally emit a recognized construct;
2. canonically join a safe single-line token sequence;
3. reproduce the smallest stable syntax owner verbatim.

No fallback invents syntax. Every opaque fragment contributes to the measured
verbatim total with a reason and kind.

### 4.1 Seam ownership

Emitters decompose syntax at ownership seams. A seam owns delimiters and the
trivia between neighboring children. Examples include declaration/value,
pattern/arm-body, field/value, and statement/continuation.

Ownership is exclusive. If both children own a comment, it is duplicated. If
neither owns it, it disappears. The seam helpers make that accounting explicit
and allow an unsupported child to degrade without making its siblings opaque.

### 4.2 Whitespace-sensitive syntax

Some adjacency is semantic because macros inspect token placement or because
Lean's longest-match parser chooses a different notation. These forms are
classified in `emit/ws_sensitivity.lean` and protected at a stable syntax
owner. New source-substring fences are treated as bugs unless no structural
classification exists.

## 5. Document algebra and renderer

The `Doc` algebra records intent: alternatives, indentation, alignment,
vertical-space requests, raw comments, and opaque source. The renderer alone
tracks the current column and remaining width.

Important constructors include:

- `group`, choosing a flat or broken form;
- `nest` and `align`, controlling indentation after breaks;
- `alignTable` and `align_or`, providing bounded grids with canonical fallback;
- `fillSep`, packing flat items across lines;
- `blank`, requesting policy-clamped vertical space;
- `pad`, reserving width for caller-owned suffixes;
- `textRaw` and `verbatim`, carrying content that normal text cannot.

A group containing a line comment cannot flatten. A table whose padding exceeds
policy or whose rows cannot fit chooses its fallback document. These are normal
algebraic choices, not renderer exceptions.

Rendering is total over `Doc`. Coverage accounting is accumulated during the
same traversal, so “active,” “verbatim,” and “trivia” describe what actually
rendered rather than what the emitter hoped to render.

## 6. Runtime safety gate

The gate validates the completed candidate in this order:

1. reparse the candidate;
2. compare protected leaf tokens;
3. compare comment content;
4. compare the syntax-kind spine;
5. compare the import header;
6. render the candidate again and require byte identity.

If every check passes, the candidate is returned. Otherwise the original source
is returned with a diagnostic and an optional drill artifact. An exact-path
identity clearance can classify a known failure after validation fails; it
cannot authorize changed bytes.

This gate is the production boundary. Tests exercise components. The gate
decides the artifact.

## 7. Policy

A resolved `Style` contains layout, breaking, alignment, blank-line, spacing,
import, comment, naming, and lint groups. Presets are complete values. Patches
contain optional groups and compose with right-biased precedence.

`fmt.lean` discovery walks from repository root to the file. Every matching
configuration contributes a patch. Resolution is deterministic and
component-path-aware. Unknown keys fail rather than disappear.

Formatting reads layout policy. Linting reads hazard policy. Renaming reads
naming policy but runs only through an explicit project command.

## 8. Lint and rename paths

Lint rules consume syntax and resolved policy and produce structured
diagnostics. They do not rewrite. The distributed gate seals source,
configuration, executable, shard ownership, and clearance fingerprints before
workers run.

Renaming uses a separate elaboration pass with info trees enabled. It records
source ranges paired with resolved declaration identities, builds a collision-
checked plan, applies byte edits from right to left, reparses, and delegates the
final authority to the project build. Module-path casing runs earlier through
the import DAG because a module name is also a filesystem and import identity.

## 9. Driver and concurrency

The driver resolves all file paths and policies before dispatch. Workers receive
explicit jobs. Results are merged deterministically. Only the IO layer writes,
and only in `--write` mode after the per-file safety gate succeeds.

Process isolation remains available for frontend conflicts because Lean's
environment and initializer behavior are not purely local. Concurrency is an
optimization over a fixed semantic plan; changing worker count must not change
bytes or diagnostics.

## 10. Verification surfaces

Development runs independent gates because no single check covers every
failure class:

- `lake build` checks the implementation and its compile-time laws;
- a corpus gate formats the home corpus twice and requires zero drift;
- comment-diff checks catch ownership mistakes invisible to token comparison;
- perturbation fuzzing measures independence from irrelevant source trivia;
- focused witnesses isolate syntax-family decisions;
- Mathlib samples expose breadth cheaply;
- the full-census lock covers the complete 8,245-file production run;
- project builds are the floor for token-changing rename transactions.

The gate harness lives with the development tree; this repository ships the
formatter, its compile-time laws, and the evidence record. The standing local
check is the tree itself: every file here is at the fixed point of the binary
built from it.

## 11. Change protocol

When adding a syntax handler:

1. register and inspect the exact syntax shape;
2. identify child and trivia ownership;
3. construct flat and broken documents;
4. choose the smallest stable opaque fallback;
5. add focused witnesses for comments and width boundaries;
6. run reparse, token, comment, spine, and fixed-point checks;
7. compile affected projects;
8. run the home corpus;
9. widen the census and ratchet its clearance.

When changing a lower layer, widen accordingly. Renderer changes touch every
construct. Seam changes touch every caller. Frontend changes touch the trust
boundary. A small diff is not necessarily a small change.

## 12. Current production boundary

The full Mathlib lock parses 8,245 files with no missing statistics and no
unclassified safety rejection. It ships 91.9% of the portable surface actively
and names 113 exact-path identity results. The local 234-file corpus is a clean
fixed point.

These figures describe the current implementation; they are not architectural
constants. The invariant is that every future number remains honest and every
new exception is explicit.
