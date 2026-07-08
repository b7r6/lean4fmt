/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                            // LEAN4FMT // MAIN
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The executable. Thin: Cli → Driver, everything formatted through the runtime
    safety gate (Frontend). Never worse than input.

    Requires `supportInterpreter := true` (lakefile) to run module initializers
    when loading syntax extensions from imports.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import Lean4Fmt.Cli
import Lean4Fmt.Driver

open Lean
open Lean4Fmt

unsafe def initEnvImpl : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution   -- required before importing modules with syntax extensions

@[implemented_by initEnvImpl]
opaque initEnv : IO Unit

unsafe def formatFileImpl (path : String) (width : Nat) : IO String :=
  Lean4Fmt.Driver.formatFile path width

@[implemented_by formatFileImpl]
opaque formatFile (path : String) (width : Nat) : IO String

def main (argv : List String) : IO Unit := do
  let o := Cli.parse argv
  if o.files.isEmpty then
    (← IO.getStderr).putStrLn Cli.usage
    IO.Process.exit 1

  initEnv

  let mut failed := false
  for file in o.files do
    try
      let output ← formatFile file o.width
      match o.mode with
      | .format => IO.print output
      | .check =>
        let original ← IO.FS.readFile file
        if output != original then
          (← IO.getStderr).putStrLn s!"Would reformat: {file}"; failed := true
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
      (← IO.getStderr).putStrLn s!"Error: {file}: {toString e}"; failed := true

  if failed then IO.Process.exit 1
