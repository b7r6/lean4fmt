/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                     // LEAN4FMT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A source-code formatter for Lean 4.

        source → Frontend.parse → Syntax → Emitter → String
                                            └─ wrapped in the runtime SAFETY GATE
                                               (token-preserving, idempotent, or
                                                degrade to identity)

    The gate (Frontend.formatSafe) guarantees the output is never worse than the
    input: a file whose formatting would change meaning — or that we cannot parse
    — is emitted unchanged. So `lean4fmt` is safe to run across a whole tree.

    Requires `supportInterpreter := true` in the lakefile to run module
    initializers when loading syntax extensions from imports.

    LIMITATION: Lean's module initialization runs once per process, so formatting
    multiple files in one invocation can fail on the second. Use `xargs -n1` or
    call once per file.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import Lean4Fmt.Emitter
import Lean4Fmt.Frontend

open Lean

inductive Mode where
  | format  -- print to stdout (default)
  | check   -- exit 1 if would change
  | write   -- overwrite in place

def parseArgs (args : List String) : IO (Mode × Nat × List String) := do
  let mut mode := Mode.format
  let mut width : Nat := 100
  let mut files : List String := []
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--check" :: r => mode := Mode.check; rest := r
    | "--write" :: r => mode := Mode.write; rest := r
    | "-w" :: r => mode := Mode.write; rest := r
    | "--width" :: n :: r => width := n.toNat!; rest := r
    | f :: r => files := files ++ [f]; rest := r
    | [] => break
  return (mode, width, files)

unsafe def initEnvImpl : IO Unit := do
  initSearchPath (← findSysroot)
  -- required before importing modules with syntax extensions
  enableInitializersExecution

@[implemented_by initEnvImpl]
opaque initEnv : IO Unit

unsafe def formatFileImpl (path : String) (width : Nat) : IO String := do
  let contents ← IO.FS.readFile path
  Lean4Fmt.Frontend.formatFile path contents { lineWidth := width }

@[implemented_by formatFileImpl]
opaque formatFile (path : String) (width : Nat) : IO String

def main (args : List String) : IO Unit := do
  let (mode, width, files) ← parseArgs args
  if files.isEmpty then
    (← IO.getStderr).putStrLn "Usage: lean4fmt [--check | --write] [--width N] <file...>"
    (← IO.getStderr).putStrLn ""
    (← IO.getStderr).putStrLn "Note: Due to Lean module initialization semantics, formatting"
    (← IO.getStderr).putStrLn "multiple files may fail. Use: find . -name '*.lean' | xargs -n1 lean4fmt"
    IO.Process.exit 1

  initEnv

  let mut failed := false
  for file in files do
    try
      let output ← formatFile file width
      match mode with
      | .format => IO.print output
      | .check =>
        let original ← IO.FS.readFile file
        if output != original then
          (← IO.getStderr).putStrLn s!"Would reformat: {file}"
          failed := true
        else
          (← IO.getStderr).putStrLn s!"OK: {file}"
      | .write =>
        let original ← IO.FS.readFile file
        if output != original then
          IO.FS.writeFile file output
          (← IO.getStderr).putStrLn s!"Formatted: {file}"
        else
          (← IO.getStderr).putStrLn s!"Unchanged: {file}"
    catch e =>
      (← IO.getStderr).putStrLn s!"Error: {file}: {toString e}"
      failed := true

  if failed then IO.Process.exit 1
