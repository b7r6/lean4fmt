# The Straylight Style

The formatter core is multi-style. Straylight is one policy: the house style
for systems programs written in Lean 4. It is intentionally different from a
mathematical-library style, and it is not imposed on Mathlib.

This chapter specifies the fixed point. It does not prescribe how every input
must be edited by hand. Formatting handles layout; linting identifies design
hazards; renaming is a separate transactional operation.

## 1. Purpose

Systems Lean is read as executable architecture. State ownership, resource
lifetime, error paths, and event demultiplexing must remain visible during
review. A proof-heavy mathematical file optimizes for different things: compact
binders, conventional one-letter variables, and frequent transitions between
tactic and term modes.

The style therefore favors:

- explicit state and ownership;
- screen-sized control flow;
- stable, reviewable diffs;
- names that survive reading without local context;
- comments that explain invariants and transitions;
- compact syntax where compactness preserves the shape of the computation.

The principle is density without concealment.

## 2. Layout

### 2.1 Width and indentation

The default line width is 100 columns. Indentation advances by two spaces.
Tabs are never emitted. Trailing whitespace is removed, and each file ends with
one newline.

A construct stays on one line when it fits and its flat form is lexically safe.
Breaking is structural: continuation indentation follows the document algebra,
not the historical whitespace of the source.

```lean
def connect (host : String) (port : UInt16) (alpn : String) : IO Connection
```

Long signatures break as one declaration, with the result type owned by the
signature rather than stranded as punctuation:

```lean
def process_header
    (header : Syntax)
    (options : Options)
    (messages : MessageLog)
    (input_context : InputContext)
    : IO (Environment × MessageLog)
```

### 2.2 Blocks

`do`, `by`, loop, and match bodies add one indentation level. Extra indentation
does not confer meaning and is not used decoratively.

```lean
def read_request : IO ByteArray := do
  let socket ← accept
  receive socket
```

Line comments make a group unflattenable. The formatter never moves code after
`--` onto the comment's physical line.

### 2.3 Vertical space

One blank line separates conceptual stanzas. Multiple blank lines do not encode
additional structure. Within a function, a blank-line break introduces a new
step and should normally be preceded by an imperative stanza comment.

```lean
  -- remove the container's reference before extending the buffer.
  let clients := state.clients.erase client_idx
  let buffer := previous ++ chunk

  -- dispatch the next complete request.
  route_request loop state buffer
```

## 3. Declarations

### 3.1 State bundles

Three or more mutable variables threaded through a loop belong in a structure.
Handlers take the state and return the next state. The loop body becomes a thin
dispatch table.

```lean
structure worker_state where
  pool    : Array upstream_slot
  clients : Std.HashMap UInt32 client_state
  waitq   : Array queued_request
```

### 3.2 Thin demultiplexers

An event loop should fit on one screen. Each branch calls a named handler. A
large branch is a missing function, not an invitation to fold more syntax into
the loop.

```lean
match event.kind with
| .meshFd  => state ← handle_mesh_fd loop state event
| .connect => state ← handle_connect loop state event
| .recv    => state ← handle_recv loop config state event
| _        => pure ()
```

Match arms contain one expression by default. Guard and extraction work belongs
inside that expression or in a named handler. This keeps the match readable as
a table of alternatives.

### 3.3 Function size

Roughly fifty lines is a useful pressure signal, not a mechanical law. When a
function no longer fits on a screen, look for a state transition, resource
boundary, or semantic phase that deserves a name.

### 3.4 Structures and inductives

Fields and constructors occupy one line each when their signatures fit. Small,
related field names may align their colons when the padding remains bounded.

```lean
structure event where
  ud    : UInt64
  res   : Int64
  flags : UInt32
  kind  : operation_kind
```

Alignment is abandoned when it creates a wide whitespace canyon. The fallback
layout is canonical and is part of the style definition.

## 4. Names

Straylight uses snake case for project-defined modules, namespaces, types,
theorems, and terms where Lean's module-resolution constraints permit it.
Renaming is performed by resolved declaration identity across the import DAG;
the formatter never changes identifier spelling as a layout side effect.

Names should state their role. `fd`, `ud`, `cfg`, and `idx` are accepted terms
of art. `p`, `w`, `n`, and `evs` usually discard information. Throwaway indices
use `idx`, `jdx`, and `kdx`. A mathematical tree may admit traditional Greek
binders through a local policy override; a systems tree does not inherit that
exception automatically.

Structure fields may remain compact when qualification supplies the missing
context: `slot.st` and `slot.acc` are readable because the owner is present.

The symbol-length floor is a lint rule with scoped, per-length allowlists. It is
not encoded as a collection of exceptions in the checker. Changing the policy
produces a new fixed point without changing the rule engine.

## 5. Comments

Comments explain facts the type or control-flow structure does not already say.
The useful categories are:

- invariant: what must remain true;
- ownership: who may mutate or release a resource;
- transition: what the next block accomplishes;
- hazard: why an apparently simpler implementation is wrong;
- evidence: which external contract or measured behavior justifies a choice.

Doc comments describe the public declaration. Module comments explain the
architecture, data path, and invariants before presenting implementation detail.
Decorative rulers may partition a long module, but they do not substitute for
headings or names.

Do not narrate syntax:

```lean
-- Bad: increment next.
next := next + 1

-- Good: advance the round-robin worker cursor.
next_worker := next_worker + 1
```

## 6. Resource-sensitive code

Lean's reference counting is part of systems performance. When an append relies
on unique ownership, remove the container's reference before appending and
state the reason at the site. Do not hide the sequence behind an abstraction
that obscures the reference-count transition.

```lean
-- RC==1: erase the map reference before append so `++` can extend in place.
let clients := state.clients.erase client_idx
let buffer := if previous.isEmpty then chunk else previous ++ chunk
```

File descriptors, registered slots, buffers, and completion identifiers should
have one visible owner at every state. Names and handler boundaries should make
that owner obvious.

## 7. Imports and namespaces

Imports are grouped by origin and kept stable within their semantic group.
Reordering imports is not presumed semantics-free: imported syntax and
initializers may affect later parsing and elaboration.

Namespaces use explicit `namespace` and `end` markers. Top-level declarations
remain flush-left. The closing marker names the namespace when that improves
navigation.

## 8. Proofs and tactics

Short proofs stay attached to their statement:

```lean
theorem normalize_idempotent : normalize (normalize value) = normalize value := by
  simp [normalize]
```

Long proofs break structurally. Tactics are not exempt from naming and layout
merely because they occur in proof mode, but the linter policy remains less
aggressive here until the cost of stricter conventions is measured on real
trees.

## 9. Policy, not scripture

Straylight is a resolved `Style` value plus tree-local overrides. It is not a
claim that all Lean should look alike. Mathlib, generated code, embedded DSLs,
and experimental trees have different rational interests.

The unifying principle is process. Preserve the composition laws, make every
exception explicit, run the gates, and let a policy change produce a new fixed
point. A house style earns authority by being cheap to revise and safe to apply.
