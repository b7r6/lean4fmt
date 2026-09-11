# lean4fmt — A Design for Trustworthy Source Transformation

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // LEAN4FMT // DESIGN // V2
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A formatter is a small compiler whose output happens to be source code.
    Its first duty is therefore not beauty. Its first duty is custody.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

## Preface

Lean source is unusually demanding material for a formatter. Its grammar is
extensible; parsing and elaboration are interleaved; whitespace may participate
in macro syntax; comments can alter the lexical fate of the next token; and the
same surface identifier may denote different declarations in different scopes.
A tool that merely knows the core grammar cannot safely rewrite a real Lean
tree. A tool that merely reproduces the parser's pretty printer cannot express a
project's style. A tool that merely looks correct on examples is not fit to
rewrite a mathematical library.

lean4fmt is built around a stricter proposition:

> Every transformation must carry enough local evidence to be attempted, and
> every emitted file must pass a global semantic safety gate. Where evidence is
> absent, the source is preserved exactly and the boundary is measured.

This document is the design of record. It describes the system as it exists,
the laws that constrain its evolution, and the procedure by which new syntax is
admitted. Historical measurements and the sequence of discoveries live in
[the campaign](campaign.md); the source-level map lives in [the architecture](architecture.md); naming migration
details live in [the renaming chapter](renaming.md).

## 1. The object being built

lean4fmt is four related tools sharing one frontend and one policy model:

1. a deterministic formatter from Lean syntax to a document algebra;
2. a linter for house-style constraints that formatting should not silently
   repair;
3. an elaboration-aware project renamer for casing migrations;
4. a census instrument that distinguishes attempted formatting from formatting
   safe enough to ship.

These are not four modes bolted onto a printer. They are four interpretations of
the same facts: syntax, ownership, resolved identity, policy, and proof residue.

The formatter's semantic contract for source `s`, style `p`, and result `r` is:

```
format p s = r

tokens(r)       = tokens(s)
comments(r)     = comments(s)
imports(r)      = imports(s)
syntaxSpine(r)  = syntaxSpine(s)
format p r      = r
```

When any check fails, the ordinary result is `s`, accompanied by a diagnostic.
The failure mode is therefore identity, never a plausible-looking damaged
program.

Renaming deliberately changes identifier tokens, so it has a different
contract. A rename is planned over resolved declaration identities, applied in
dependency order, reparsed, compiled, and committed only if the whole selected
closure remains green. Formatting and renaming meet again at the fixed-point
gate: the renamed tree must still be canonical under its style.

## 2. Design laws

The implementation is governed by a small set of laws. Features are admitted by
showing how they preserve these laws, not by accumulating special cases until a
corpus happens to pass.

### 2.1 Custody

No emitted change may add, delete, reorder, split, or merge non-trivia tokens.
Comment text and order are equally protected. This is checked after rendering,
not inferred from the emitter's intentions.

### 2.2 Fixed point

For fixed policy `p`:

```
format p (format p s) = format p s
```

Idempotence is part of correctness. A second-pass change means that some layout
decision depended on historical whitespace rather than syntax and policy.

### 2.3 Origin independence

If two inputs have the same relevant syntax and comment attachments, a
prescriptive style should produce the same output. Source whitespace may be
content, an explicit opaque boundary, or irrelevant trivia; it may not be an
unacknowledged layout input.

### 2.4 Local opacity

Unsupported syntax is preserved at the smallest complete owner whose placement
is stable. One opaque child must not force portable siblings or an enclosing
declaration opaque. Opacity composes upward through explicit seams.

### 2.5 Monotone policy

Adding a rule or tightening a threshold may expose new violations, but it must
not weaken unrelated policy. Overrides have explicit precedence, and exception
sets compose by union. A later campaign changes the fixed point by changing the
policy algebra, not by editing a hidden list of procedural exceptions.

### 2.6 Loud uncertainty

Parse failure, unresolved environment state, an unsafe candidate, a collision,
or an unknown syntax shape is observable. Production may choose identity for a
named case; it may not confuse identity with successful active formatting.

## 3. The pipeline

```
                       project policy
                             │
source ──► frontend ──► syntax + trivia ──► emitter ──► Doc ──► renderer
   │          │                                      │          │
   │          └── imported env / elaboration         └── style ─┘
   │                                                           │
   └──────────────────────── safety gate ◄─────────────────────┘
                                │
                         candidate or identity
```

The phases are intentionally asymmetric.

- The frontend is effectful and version-sensitive because Lean syntax is.
- The emitter is a structural walk that records layout intent.
- The document algebra is pure and independent of Lean.
- The renderer decides line breaks from the document and resolved style.
- The gate reparses and validates the completed candidate.
- The driver coordinates files, environments, diagnostics, writes, and
  concurrency; it does not decide layout.

This separation is the central architectural choice. Syntax code should not
manipulate columns, rendering code should not inspect parser kinds, and a worker
pool should not acquire semantic authority merely because it can write files.

## 4. The frontend: Lean is not context-free

Real Lean modules cannot in general be parsed against a grammar fixed at process
startup. Imports install syntax. Commands within the file install more syntax.
Namespaces, scoped notation, macros, and options change how subsequent bytes are
read. The faithful model is Lean's own frontend: parse a command, elaborate it
far enough to update the environment, then parse the next command.

lean4fmt therefore uses a graduated frontend:

1. load the imported environment under the target repository's toolchain;
2. take the cheap parser path where it is sufficient;
3. fall back to the interleaved frontend when file-local syntax demands it;
4. elaborate proof bodies as `sorry` for table discovery, preserving their
   parsed syntax while avoiding irrelevant proof-search cost;
5. retain source ranges and trivia needed by reproduction and resolution.

The target toolchain is part of the input. Lean syntax kinds and compiled
environments are version-coupled, so foreign-tree census runs build and execute
lean4fmt under that tree's pinned `lean-toolchain`.

Frontend failure is not an invitation to guess. The file returns unchanged with
a parse diagnostic.

## 5. The document algebra

The emitter does not print strings. It constructs `Doc`, a Wadler–Leijen-style
algebra extended for source transformation:

- `text`, concatenation, `line`, `softline`, and `hardline`;
- `group`, `nest`, `align`, and `flatten`;
- `fillSep` for width-aware packing;
- `alignTable` and `align_or` for bounded alignment;
- `blank` for policy-mediated vertical space;
- `pad` for width reserved by a caller-owned suffix;
- `textRaw` for comment content;
- `verbatim` for an opaque source fragment with a known base indentation.

The distinction between intent and realization matters. `line` means “space if
this group fits, otherwise a line break”; it does not mean “look at the source
and copy whatever was there.” `blank 1` requests vertical space; the renderer
may clamp it according to context and policy. `align_or` makes the fallback
layout part of the document rather than an emergency renderer heuristic.

The core concatenation operation forms a monoid:

```
nil <> d = d
d <> nil = d
(a <> b) <> c = a <> (b <> c)
```

Those simple laws are valuable. They let emitters assemble prefixes, values,
comments, and suffixes independently without smuggling layout state between
them.

### 5.1 Rendering

Rendering is a bounded choice between flat and broken forms. A group is flat
only when its measured width fits and its content is flattenable. Nesting affects
indentation only after a break. Alignment binds future breaks to the current
column. No emitter guesses the current column.

Line comments are unflattenable. If `--` were moved into the middle of a line,
it could consume a delimiter, an `else`, or the next arm. The renderer therefore
treats the presence of a line comment as a semantic layout constraint.

### 5.2 Opaque reproduction

Whole-language coverage requires a principled identity element for unsupported
subtrees. `verbatim source baseIndent` preserves the fragment's bytes while
allowing it to be placed at a stable owner seam. Reproduction obeys three rules:

1. preserve content and relative indentation;
2. re-anchor only when the owner explicitly controls the new base column;
3. never infer a continuation indent from the fragment's previous placement.

Opaque is not failure. It is a typed boundary between what the formatter can
currently derive and what it must hold in trust. Coverage accounting makes the
cost visible so the boundary can move deliberately.

## 6. The emitter: ownership before appearance

The emitter is organized by syntax family—commands, declarations, terms,
binders, do-notation, tactics, and tokens—but its deeper abstraction is the
seam.

A seam is a place where two independently meaningful pieces may be joined: a
declaration head and value, a match pattern and arm body, a structure field and
its value, a `where` introducer and its equations. Every seam owns:

- the separator tokens;
- the comments between its children;
- whether a flat join is legal;
- the indentation of the broken form;
- the smallest safe opaque fallback.

This ownership rule prevents the two dominant formatter bugs: comments emitted
twice because both neighbors claimed them, and comments lost because neither
did. It also enables per-piece degradation. An unsupported equation pattern can
remain exact while adjacent equations are actively formatted.

Token respacing is the leaf case of the same model. Canonical spacing is decided
from syntax-aware token pairs. Tokens whose payload or adjacency is
whitespace-sensitive remain under an explicit owner. Raw substring tests are
not durable classifiers; syntax kind and source range are.

## 7. Style is data

A style is a product of independent policy groups: layout, breaking, alignment,
blank lines, spacing, imports, comments, naming, and linting. Presets provide
coherent starting points; project configuration and command-line options refine
them.

Project configuration uses a deliberately small declarative subset of Lean in
`fmt.lean`:

```lean
def preset := "straylight"
def layout.lineWidth := 100
def linting.symbolFloor := 3
def linting.symbolAllow.1 := "α,β"
```

The file is parsed, not executed. Unknown keys and malformed values are errors.
This keeps policy reviewable, toolchain-independent, and safe to discover while
walking an untrusted tree.

### 7.1 Patch algebra

A `style_patch` contains optional policy groups. Applying a patch replaces only
present groups. Patch composition is right-biased: later policy wins.

For patches `a`, `b`, and `c`, and empty patch `ε`:

```
(a ++ b) ++ c = a ++ (b ++ c)
ε ++ a = a
a ++ ε = a
```

The operation is intentionally not commutative; precedence is meaningful.

A policy tree is an ordered list of path-rooted patches. Resolution walks from
root to leaf and applies every matching patch in order. Tree overlay is list
concatenation, so its associativity follows directly. Component-wise prefix
matching prevents `Core` from accidentally matching `CoreCodec`.

This gives local policy a proof-amenable meaning: a directory override is a
function on styles, not an imperative callback. Tightening relations can be
defined per lint axis, and patches can be checked for preservation of those
relations.

### 7.2 Exception algebra

Some safety failures are known to require identity until their syntax class is
modeled. Identity-clearance files contain exact paths and compose by set union:

```
A ∪ (B ∪ C) = (A ∪ B) ∪ C
A ∪ B = B ∪ A
A ∪ A = A
```

A clearance is consulted only after a candidate fails the semantic gate. It
cannot make a changed candidate valid; it can only turn a known warning into a
named identity result. Census accounting assigns that file zero active shipped
bytes. Unknown failures remain loud, and the production gate bounds the size of
the clearance set so exceptions may shrink but not silently grow.

## 8. The runtime safety gate

The gate is the boundary between an attractive candidate and a releasable
result. It checks:

1. the candidate reparses under the relevant environment;
2. leaf tokens are preserved;
3. comment content is preserved;
4. the syntax-kind spine is preserved;
5. the import header is preserved;
6. formatting the candidate again produces identical bytes.

On success, the candidate ships. On failure, the original source ships. A debug
artifact records the failed proof for campaign work.

The gate is deliberately redundant with construction. The document algebra and
emitter are designed to preserve meaning locally; the gate checks the complete
artifact globally. Local reasoning makes progress tractable. Global validation
makes mistakes survivable.

The token and spine checks are not a proof of Lean semantic equivalence in the
abstract. They are a strong, executable refinement appropriate to a formatter
whose authorized operation is trivia movement. The compile and corpus gates add
independent evidence at project scale.

## 9. Linting: hazards before taste

Formatting answers “where should this syntax be laid out?” Linting answers
“should this syntax have been written this way?” Keeping them distinct avoids
surprising semantic edits and permits stricter house policy without imposing it
on foreign code.

The lint system begins with mechanical hazards:

- minimum symbol length with per-length allowlists;
- separate allowlists for declarations, fields, binders, recursive helpers,
  lambdas, and local lets;
- casing policy by semantic axis;
- single-expression match arms and other screen-shape constraints;
- state-bundle and naming conventions used by systems Lean.

Allowances are scoped data, not branches in lint code. Traditional mathematical
trees may admit one-character Greek binders; systems trees may reject them.
Instance binders, indices, and other terms of art can be named explicitly by
policy. This makes disagreement cheap: change the policy, rerun to a new fixed
point, and retain the same machinery and laws.

## 10. Renaming: identity, dependency, transaction

Casing conversion is not formatting. Renaming changes tokens, can change name
resolution, and crosses file boundaries. Its unit of work is therefore a
dependency closure, not a syntax node.

### 10.1 Casing kernel

The casing kernel converts among preserved, snake, camel, and upper-camel forms.
It retains leading underscores and trailing primes, handles digit and acronym
boundaries, and is guarded for idempotence. Policy maps declaration kinds onto
four axes: namespaces/modules, types, theorems, and terms.

### 10.2 Resolution before rewrite

Textual substitution is unsound. Two identical spellings may resolve to
different constants; projections require field identity; macro expansions and
quotations may carry occurrences not recoverable from a simple token map.

The production path elaborates with info trees enabled and records source byte
ranges paired with resolved full names. Only occurrences resolving to a planned
declaration identity are rewritten. Generated constants are collision evidence
but not rename authority. Local binders also enter the collision set so a type
cannot be renamed onto a value that would shadow it.

The planner rejects keyword targets, same-namespace collisions, module hazards,
and ambiguous identities. A skip is reported and is monotone: additional
knowledge may remove candidates from a plan, never authorize an uncertain one.

### 10.3 DAG order

If module `B` imports module `A`, renaming `A` changes facts consumed by `B`.
Repository migration proceeds in topological waves over the import DAG:

```
roots / providers  ──►  internal users  ──►  leaves / applications
```

Within a wave, independent modules may be processed concurrently. Between
waves, the renamed providers are rebuilt so downstream resolution sees the new
world. A reverse or leaf-first migration would produce stale imports and false
resolution failures.

### 10.4 Transaction boundary

A rename wave is successful only when all of the following hold:

- the plan is deterministic across repeated discovery;
- every rewrite reparses;
- the selected package closure compiles;
- the formatter reaches a fixed point afterward;
- pass two proposes no new rename or skip inconsistent with pass one.

Failure aborts the wave. The build is not merely a test; it is the final oracle
for namespace, macro, and generated-code interactions that no finite planner can
claim to model completely.

## 11. Concurrency without semantic drift

Formatting files is parallelizable after their environments and policies are
resolved. The driver uses bounded workers and deterministic result ordering.
Writes occur only after each file's gate succeeds. Conflict retry is isolated so
Lean's process-global frontend state cannot leak between incompatible import
worlds.

Renaming admits less parallelism. Files in the same dependency wave may be
handled together, but wave boundaries are semantic barriers. Concurrency may
reduce latency; it may not alter policy order, dependency order, diagnostics, or
the committed result.

Determinism is a correctness property. A run that sometimes discovers fewer
declarations can accidentally authorize a collision. Accordingly, declaration
identity, occurrence resolution, and collision evidence are harvested from the
same elaboration whenever possible.

## 12. Measurement: attempted is not shipped

Coverage is evidence about the formatter's modeled surface, not a vanity score.
The census divides code bytes into:

- **active** — emitted from structural documents;
- **verbatim** — preserved at an explicit opaque boundary;
- **policy** — content intentionally outside formatting, such as literal payloads;
- **rejected** — a candidate was attempted but the runtime gate returned identity;
- **identity-cleared** — a known exact path returned identity by explicit policy.

The campaign number is shipped active bytes divided by portable bytes. Rejected
and identity-cleared files contribute zero shipped-active bytes even if their
attempted pass traversed most of the file. This distinction prevented the
project from declaring victory on output it would not actually release.

The standing production lock over Mathlib currently records:

- 8,245 files parsed;
- zero missing statistics;
- zero unclassified safety-gate rejects;
- 113 exact identity clearances;
- 81.8% active code bytes overall;
- 91.9% shipped active bytes of the portable surface.

The development gate harness makes these monotone bounds executable. The local
corpus gate independently formats twice and requires zero drift and zero errors.

## 13. How the frontier moves

The development loop is a proof-guided burn-down:

1. census a representative or complete tree;
2. rank opaque reasons by shipped byte cost, not occurrence count;
3. select one syntax family and collect focused witnesses;
4. identify the smallest complete owner and its seams;
5. implement structural emission or narrow the opaque boundary;
6. run token, comment, spine, reparse, and fixed-point gates;
7. run affected compilation and the home corpus;
8. widen the census;
9. encode the new lower bound and non-increase clearances;
10. commit only the monotone gain.

A failed experiment is useful if it sharpens a law. The campaign discovered,
among other things, that source-newline-derived decisions drift, substring
comment tests misclassify token payloads, a notation's stable owner may be its
application rather than its visible node, and an unsupported child need not
poison its siblings. Those facts belong in mechanisms and gates, not folklore.

## 14. Adding a construct

An implementation for a new syntax kind should answer these questions in order:

1. What is the node's stable syntactic shape across supported Lean versions?
2. Which child owns every delimiter and comment-bearing gap?
3. What are the flat and broken documents?
4. Which source bytes are true content rather than historical layout?
5. Where is the smallest stable opaque fallback?
6. Can a line comment make the flat form lexically unsafe?
7. Does the construct introduce or depend on parser tables?
8. Which focused fixture demonstrates each branch?
9. Which existing wide and home gates could it regress?
10. What measurable residue should decrease if the model is correct?

If these questions do not have crisp answers, the construct is not ready for
active formatting. Preserving it is the correct implementation.

## 15. Boundaries

lean4fmt does not attempt to prove arbitrary program equivalence. It does not
execute project configuration. It does not silently normalize literal payloads,
macro languages, or whitespace-sensitive notation. It does not treat a clean
parse as proof that comments survived. It does not treat a successful first pass
as proof of canonical layout. It does not rename a tree as a bag of strings.

Nor is universal active formatting the only legitimate endpoint. A syntax class
may be ceiling-only when its whitespace is content or when no stable owner exists
under the available frontend. Such a classification must be explicit, local,
measured, and reversible when the architecture improves.

## 16. The standard of completion

The tool is complete enough for a tree when:

- every file either ships a validated fixed point or a named exact identity;
- no unknown rejection is hidden;
- policy resolution is deterministic from root to leaf;
- formatting is independent of irrelevant source trivia;
- rename plans are identity-aware, collision-safe, DAG-ordered, and build-green;
- the corpus and production clearances prevent regression;
- the remaining opaque surface is quantified and intelligible.

That standard is intentionally stronger than “the output looks good.” Source
code is accumulated thought. In a proof library, it is also part of the social
machinery by which mathematics is checked, reviewed, taught, and extended. A
formatter worthy of that material must make broad change cheap without making
trust cheap.

That is lean4fmt's purpose: not to impose one final appearance, but to provide a
safe, compositional process by which a community can choose a style, reach its
fixed point, change its mind, and reach the next one without surrendering the
program in between.
