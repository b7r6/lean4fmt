# lean4fmt Architecture

## Core Insight

The `Syntax` tree from parsing contains EVERYTHING:
- Token values (atoms, idents)
- Leading whitespace/comments (in `SourceInfo.original.leading`)
- Trailing whitespace (in `SourceInfo.original.trailing`)
- Full tree structure with syntax kinds

We walk this tree and emit formatted text directly.

## Design

```
┌─────────────────────────────────────────────────────────────────────┐
│                           Syntax Tree                                │
│  ┌─────────────────────────────────────────────────────────────────┐│
│  │ Module                                                          ││
│  │  ├─ Header (imports)                                            ││
│  │  └─ Commands[]                                                  ││
│  │       ├─ namespace/section/end                                  ││
│  │       ├─ declaration (def/theorem/axiom/opaque/...)             ││
│  │       │    ├─ declModifiers (doc, attrs, vis, unsafe, ...)      ││
│  │       │    └─ declBody (signature + optional value)             ││
│  │       ├─ structure/class/inductive                              ││
│  │       └─ ...                                                    ││
│  └─────────────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│                         Emitter (our code)                          │
│                                                                     │
│  Walk tree, for each node:                                          │
│    1. Extract leading comments/whitespace                           │
│    2. Decide formatting based on syntax kind + style rules          │
│    3. Emit tokens with controlled spacing                           │
│    4. Optionally lint (collect diagnostics as we go)                │
│                                                                     │
│  Key decisions per syntax kind:                                     │
│    - Line breaks: where to break, how to indent continuation        │
│    - Spacing: around operators, after keywords, in parens           │
│    - Alignment: match arms, struct fields, binders                  │
│    - Preservation: keep user's breaks when "reasonable"             │
└─────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│                         Output String                               │
│  + Optional lint diagnostics                                        │
└─────────────────────────────────────────────────────────────────────┘
```

## Key Syntax Kinds to Handle

### Top-level
- `Lean.Parser.Module.module` — root
- `Lean.Parser.Module.header` — `prelude`, `import`
- `Lean.Parser.Command.namespace`, `section`, `end`

### Declarations
- `Lean.Parser.Command.declaration` — wrapper with modifiers
- `Lean.Parser.Command.declModifiers` — doc, attrs, visibility, partial/noncomputable/unsafe
- `Lean.Parser.Command.def`, `theorem`, `axiom`, `opaque`, `abbrev`, `example`
- `Lean.Parser.Command.structure`, `class`, `inductive`
- `Lean.Parser.Command.instance`

### Signatures
- `Lean.Parser.Command.declSig` — binders + return type
- `Lean.Parser.Command.declId` — name + universe params
- `Lean.Parser.Term.explicitBinder` — `(x : T)`
- `Lean.Parser.Term.implicitBinder` — `{x : T}`
- `Lean.Parser.Term.instBinder` — `[Foo x]`
- `Lean.Parser.Term.typeSpec` — `: T`

### Terms (the hard part)
- `Lean.Parser.Term.app` — function application
- `Lean.Parser.Term.fun` — lambda
- `Lean.Parser.Term.do` — do notation
- `Lean.Parser.Term.match` — pattern matching
- `Lean.Parser.Term.if` — conditionals
- `Lean.Parser.Term.let` — let bindings
- Binary ops: `term_+_`, `term_*_`, `term_=_`, `term_∧_`, etc.

### Tactics
- `Lean.Parser.Tactic.*` — tactic syntax

## Emitter State

```lean
structure EmitterState where
  output : String          -- accumulated output
  indent : Nat             -- current indentation level
  column : Nat             -- current column (for line width decisions)
  lastWasNewline : Bool    -- for blank line control
  lints : Array Diagnostic -- collected lint warnings
```

## Style Rules (configurable)

```lean
structure StyleConfig where
  lineWidth : Nat := 100
  indent : Nat := 2
  alignMatchArms : Bool := true
  alignStructFields : Bool := true
  maxBlankLines : Nat := 2
  trailingNewline : Bool := true
```

## Phases

### Phase 1: Core Infrastructure
- [ ] `Emitter` monad with state
- [ ] Basic token emission (atoms, idents)
- [ ] Whitespace/newline control
- [ ] Leading comment preservation

### Phase 2: Top-level Commands
- [ ] Module header (imports)
- [ ] namespace/section/end
- [ ] Basic declarations (def, axiom, opaque)

### Phase 3: Signatures
- [ ] Binder formatting
- [ ] Type ascriptions
- [ ] Line-breaking heuristics for long signatures

### Phase 4: Terms
- [ ] Application
- [ ] Lambdas
- [ ] Match expressions
- [ ] Do notation
- [ ] Binary operators

### Phase 5: Complex Structures
- [ ] structure/class definitions
- [ ] inductive definitions
- [ ] instance declarations

### Phase 6: Tactics
- [ ] Tactic blocks
- [ ] by proofs

### Phase 7: Linting
- [ ] Trailing whitespace
- [ ] Line width
- [ ] Naming conventions
- [ ] Import ordering

## Testing Strategy

1. **Round-trip safety**: `parse(format(parse(src))) == parse(src)`
2. **Idempotence**: `format(format(src)) == format(src)`
3. **Golden tests**: hand-formatted examples we want to match
4. **Fuzzing**: random valid Lean files should format without crashing
