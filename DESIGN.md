# lean4fmt Design Notes

A source-code formatter for Lean 4, targeting systems programming style.

> **Role now.** The production design is `DESIGN_V2.md`. This document's
> **style guide** (below) is not superseded — it is the seed for the
> **Straylight preset** (`DESIGN_V2.md §7`). Its status and phasing notes are v1
> history; the production development loop is `DESIGN_V2.md §13`.

## Status

Working! The parser pipeline now handles all standard Lean 4 syntax including
imports with complex dependencies.

**Key insight**: The lakefile needs `supportInterpreter := true` to run module
initializers when loading syntax extensions from imports.

## Architecture

```
Source → Parser.testParseModule → Syntax → ppModule → Format → pretty → String
                    ↑
            Environment with
            imported syntax
```

The Lean pretty printer does most of the work. We customize via:
1. Width hints to the layout algorithm
2. Post-processing for mechanical rules (trailing whitespace, file ending)
3. Eventually: custom syntax-aware formatters for specific constructs

## Why Not Mathlib Style

Mathlib's style is optimized for theorem-heavy, tactic-heavy code where:
- Proofs are often throwaway (generated, long, not meant to be read)
- Screen real estate goes to displaying goals
- Tactics run across many lines

Systems code is different:
- Most code is `def`, `structure`, `opaque`, FFI bindings
- Proofs are short and intentional (axiom contracts, invariants)
- Readability of the *code* matters more than fitting in a small pane
- We read and review diffs constantly

## Systems Lean 4 Style Guide

### Line Width: 100

Modern screens. Dense code. The 80-column tradition assumes a VT100.

### Horizontal Density

Keep related things together. Don't break lines just because you can.

```lean
-- YES: fits on one line, keep it there
def read (fd : Int32) (size : UInt32) (offset : Int64) : IO ByteArray

-- NO: unnecessary vertical sprawl
def read
    (fd : Int32)
    (size : UInt32)
    (offset : Int64) :
    IO ByteArray
```

### Signatures

One line when they fit. When breaking, break after `:` not before.

```lean
-- YES: one line
def connect (host : String) (port : UInt16) (alpn : String) : IO Conn

-- YES: long signature, break after colon
def processHeader (header : Syntax) (opts : Options) (msgs : MessageLog)
    (inputCtx : InputContext) (trustLevel : UInt32) : IO (Environment × MessageLog)

-- NO: break before colon
def processHeader (header : Syntax) (opts : Options) (msgs : MessageLog)
    (inputCtx : InputContext) (trustLevel : UInt32)
    : IO (Environment × MessageLog)
```

### Indentation: 2 Spaces

Matches the existing codebase. Lean's nested structures don't need 4.

### `do` Blocks: Compact

```lean
-- YES
def main : IO Unit := do
  let x ← getLine
  IO.println x

-- NO: extra indent
def main : IO Unit := do
    let x ← getLine
    IO.println x
```

### Match Arms

Align `=>` when patterns are short and similar length. Don't align when it
would create excessive whitespace.

```lean
-- YES: aligned, patterns are short
match mode with
| .format => printOutput
| .check  => checkDiff  
| .write  => writeFile

-- YES: not aligned, patterns vary too much
match result with
| .ok value => process value
| .error e => handleError e

-- NO: excessive alignment whitespace
match kind with
| .nop                    => handleNop
| .accept                 => handleAccept
| .meshDataFromPeer       => handleMeshData
```

### Structure Fields

One per line. Align colons when field names are similar length.

```lean
structure Event where
  ud    : UInt64
  res   : Int64
  flags : UInt32
  kind  : OpKind
```

### Imports

Grouped by origin. No blank lines within a group. One blank line between groups.

```lean
import Lean
import Lean.Elab
import Lean.PrettyPrinter

import StdlibEx.IOUring
import StdlibEx.TLS

import MyProject.Core
import MyProject.Utils
```

### Namespace Style

`namespace`/`end` pairs, not brace style. The `end` marker aids navigation.

```lean
-- YES
namespace StdlibEx.IOUring

def init (entries : UInt32) : IO RingHandle := ...

end StdlibEx.IOUring

-- NO (Lean doesn't even support this, but for the record)
namespace StdlibEx.IOUring {
  ...
}
```

### `where` Clauses

Inline for short helpers. Break to new line for longer ones.

```lean
-- YES: short helper
def foo := bar + baz where
  bar := 1
  baz := 2

-- YES: longer helper, own line
def processEvents (events : Array Event) := events.foldl handle init
  where
    handle acc ev := ...
    init := ...
```

### `by` Placement

Same line as signature when the proof is short. New line when multiline.

```lean
-- YES: short proof
theorem cleanup_idempotent : ... := by simp [cleanup]

-- YES: multiline proof
theorem response_valid : ... := by
  intro h
  cases h
  · simp
  · exact ih
```

### Comments

Preserve as-is. Normalize `--foo` to `-- foo` (space after `--`).

Doc comments (`/-- ... -/`) stay attached to their declaration.

### Trailing Whitespace

Never. Strip it.

### File Ending

Single newline. No trailing blank lines.

### Operators

Spaces around binary operators. No space after unary.

```lean
-- YES
let x := a + b * c
let y := -x

-- NO
let x:=a+b*c
let y := - x
```

## Open Questions

1. **Type ascription alignment**: In `let x : T := ...`, align the `:`s in a block?
   
2. **Long `if` conditions**: Break before `then` or after `if`?

3. **Tactic combinators**: `<;>` on same line or break?

4. **Attribute lists**: `@[extern "foo", inline]` or one per line?

5. **Anonymous constructor syntax**: `⟨a, b, c⟩` vs explicit constructor?

## Implementation Phases

### Phase 1: Make It Work ✓

- [x] Fix import resolution for complex files
- [x] Basic CLI: `--check`, `--write`, `--width`
- [ ] Round-trip safety: parse → format → parse ≡ original AST
- [ ] Handle all stdlib files without crashing

### Phase 2: Style Rules

- [ ] Line width enforcement (soft wrap at 100)
- [ ] Trailing whitespace removal
- [ ] File ending normalization
- [ ] Import grouping (maybe: this might be too opinionated)

### Phase 3: Syntax-Aware Formatting

- [ ] Match arm alignment heuristic
- [ ] Structure field alignment
- [ ] Signature breaking rules
- [ ] `where` clause formatting

### Phase 4: Configuration

```toml
# lean4fmt.toml
[style]
line_width = 100
indent = 2
align_match_arms = true
align_struct_fields = true
```

### Phase 5: Integration

- [ ] Pre-commit hook
- [ ] CI check (`lean4fmt --check`)
- [ ] Editor integration (format on save)

## Technical Notes

### The Pretty Printer Pipeline

Lean's `PrettyPrinter` module:
1. `ppModule : TSyntax `module → CoreM Format` — syntax to format
2. `Format.pretty : Format → Nat → String` — layout with width

The `Format` type is a tree of text, line breaks, and groups. The layout
algorithm decides which groups to break based on available width.

### Known Limitations

**Multi-file processing**: Due to Lean's module initialization semantics,
the `interpretedModInits` global tracks which modules have run their initializers.
After processing one file, subsequent files may fail because Init's initializers
won't run again. Workaround: use `xargs -n1` to invoke the formatter once per file.

```bash
find . -name '*.lean' | xargs -n1 lean4fmt --check
```

### Why Parsing Worked

The fix required two things:

1. **`enableInitializersExecution`**: Must be called before `processHeader` so
   that `[init]` attributes run when loading modules. This registers syntax
   extensions, macros, etc.

2. **`supportInterpreter := true`**: In the lakefile's `lean_exe` declaration.
   Without this, the compiled binary can't run the interpreted code that
   registers syntax extensions. The error message is:
   
   ```
   Could not find native implementation of external declaration 'IO.getRandomBytes'
   ```

The `opaque`/`@[implemented_by]` pattern lets us call `unsafe` functions like
`enableInitializersExecution` from a safe `main`.

### Alternatives Considered

1. **String manipulation**: Too fragile, loses structure
2. **Regex-based**: Can't handle nested syntax
3. **Custom parser**: Reinventing the wheel
4. **Lean's `#check_failure`**: Not a formatter

Using the real frontend is the right call — it handles all syntax extensions,
macros, notations. We just need to get the setup right.
