/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                     // LEAN4FMT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A source-code formatter for Lean 4, on the real frontend:

        Source → Parser → Syntax → PrettyPrinter → Format → String

    Dropped into the tree ahead of the stdlib straighten-out: it imports only
    Lean core today, so it slots in with no internal DAG edges. It WILL trivially
    depend UP on StdlibEx once that surface is real —

        parseArgs           → StdlibEx.CLI
        the OK:/reformat:    → StdlibEx.Logging
        the round-trip diff  → StdlibEx.Bytes

    — being the second consumer that forces those modules to be general, not
    aleph-shaped. None of that is needed to place it; see the book chapter
    "lean4fmt & a coding style".
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean

open Lean
open Lean.Elab  -- for processHeader
open Lean.PrettyPrinter

/-!
## Lean 4 cheat sheet for systems programmers:

- `def f (x : T) : U := body`        — function def
- `let x ← action`                   — monadic bind (like `x = action.await()`)
- `let mut x := val`                  — mutable local (sugar over StateT)
- `do { ... }`                        — monadic block
- `structure` ≈ struct, `inductive` ≈ enum
- `{ base with field := val }`        — struct update (braces mandatory!)
- `TSyntax` = typed syntax wrapper. `.raw` unwraps to plain `Syntax`.
- `unsafe` = needed when calling `@[implementedBy]` or C FFI
-/

-- `inductive` must be at top level (or in a `namespace`/`section`).
-- Can't go in a `where` clause — those only support `def`.
inductive Mode where
  | format  -- print to stdout
  | check   -- exit 1 if would change
  | write   -- overwrite in place

def parseArgs (args : List String) : IO (Mode × Nat × List String) := do
  let mut mode := Mode.format
  let mut width : Nat := 100
  let mut files : List String := []
  let mut rest := args
  -- `while` in `do` blocks works like you'd expect.
  -- Under the hood it's a `StateT` + termination proof (here waived by `do`).
  while !rest.isEmpty do
    match rest with
    | "--check" :: r => mode := Mode.check; rest := r
    | "--write" :: r => mode := Mode.write; rest := r
    | "-w" :: r => mode := Mode.write; rest := r
    | "--width" :: n :: r => width := n.toNat!; rest := r
    | f :: r => files := files ++ [f]; rest := r
    | [] => break
  return (mode, width, files)

/--
Format a single file. Returns the formatted source as a string.

`Parser.testParseFile` returns `TSyntax \`module` — a *typed* syntax wrapper.
We call `.raw` to get the underlying `Syntax`, which is what the pretty printer wants.
-/
def formatFile (path : String) (width : Nat) : IO String := do
  let contents ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext contents path

  -- Step 1: Parse just the header (`import` / `prelude` / `module` lines).
  -- This uses a dummy env because header syntax is always built-in.
  let (header, _, msgs) ← Parser.parseHeader inputCtx

  -- Step 2: Process the header — this resolves `import`s, loading .olean files
  -- and building an Environment with all imported syntax extensions.
  -- `processHeader` is in `Lean.Elab.Import`.
  -- Without this, the parser wouldn't know about `structure`, `instance`,
  -- `do` notation, `+` patterns, etc from imported modules.
  let (env, _) ← Elab.processHeader header {} msgs inputCtx (trustLevel := 1024)

  -- Step 3: Re-parse the *full* file with the enriched environment.
  -- The header gets parsed again (cheap), but now the command parser
  -- knows all the syntax from imports.
  -- `testParseModule` already yields a plain `Syntax` on this toolchain
  -- (v4.31.0), so there is no `TSyntax` wrapper to `.raw` off.
  let stx ← Parser.testParseModule env path contents

  -- `updateLeading`: propagates leading whitespace to syntax nodes.
  -- Without this, comments between declarations drift or vanish.
  let stx := stx.updateLeading

  -- Step 4: Pretty-print in CoreM: Syntax → Format → String
  let ctx : Core.Context := { fileName := path, fileMap := FileMap.ofString contents }
  let state : Core.State := { env }
  let (fmt, _) ← (ppModule ⟨stx⟩).toIO ctx state
  return fmt.pretty width

def main (args : List String) : IO Unit := do
  let (mode, width, files) ← parseArgs args
  if files.isEmpty then
    (← IO.getStderr).putStrLn "Usage: lean-fmt [--check | --write] [--width N] <file...>"
    IO.Process.exit 1

  initSearchPath (← findSysroot)

  let mut failed := false
  -- `for x in (list : List T)` needs the list type to be known.
  -- We annotated `files : List String` above so inference works.
  for file in files do
    try
      let output ← formatFile file width
      match mode with
      | .format =>
        IO.print output
      | .check =>
        let original ← IO.FS.readFile file
        -- `.trimAsciiEnd` returns a `String.Slice`, `.toString` reifies it.
        if output.trimAsciiEnd.toString != original.trimAsciiEnd.toString then
          (← IO.getStderr).putStrLn s!"Would reformat: {file}"
          failed := true
        else
          (← IO.getStderr).putStrLn s!"OK: {file}"
      | .write =>
        IO.FS.writeFile file output
        (← IO.getStderr).putStrLn s!"Formatted: {file}"
    catch e =>
      (← IO.getStderr).putStrLn s!"Error: {file}: {toString e}"
      failed := true

  if failed then
    IO.Process.exit 1
