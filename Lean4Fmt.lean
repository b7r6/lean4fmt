/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                     // LEAN4FMT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A source-code formatter for Lean 4, on the real frontend:

        Source → Parser → Syntax → PrettyPrinter → Format → String

    Uses `enableInitializersExecution` to load syntax extensions from imports,
    so it handles all standard Lean syntax including notation, macros, etc.

    Requires `supportInterpreter := true` in lakefile to run module initializers.

    LIMITATION: Due to Lean's module initialization semantics (initializers run
    once per process), formatting multiple files in one invocation may fail.
    Use `xargs -n1` or call once per file.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean

open Lean
open Lean.Elab
open Lean.PrettyPrinter

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

/-- Format a single file. Returns the formatted source as a string. -/
unsafe def formatFileImpl (path : String) (width : Nat) : IO String := do
  let contents ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext contents path

  -- Parse header to find imports
  let (header, _, msgs) ← Parser.parseHeader inputCtx

  -- Process header — loads .olean files, builds Environment with syntax extensions
  let (env, _) ← processHeader header {} msgs inputCtx (trustLevel := 1024)

  -- Re-parse full file with enriched environment
  let stx ← Parser.testParseModule env path contents

  -- Propagate leading whitespace to syntax nodes (preserves comments)
  let stx := stx.updateLeading

  -- Pretty-print: Syntax → Format → String
  let ctx : Core.Context := { fileName := path, fileMap := FileMap.ofString contents }
  let state : Core.State := { env }
  let (fmt, _) ← (ppModule ⟨stx⟩).toIO ctx state
  return fmt.pretty width

@[implemented_by formatFileImpl]
opaque formatFile (path : String) (width : Nat) : IO String

unsafe def initEnvImpl : IO Unit := do
  initSearchPath (← findSysroot)
  -- Required before importing modules with syntax extensions
  enableInitializersExecution

@[implemented_by initEnvImpl]
opaque initEnv : IO Unit

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

  if failed then IO.Process.exit 1
