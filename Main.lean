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

unsafe def initEnvImpl
           : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution   -- required before importing modules with syntax extensions

@[implemented_by initEnvImpl]
opaque initEnv : IO Unit

/-- Resolve style, expand inputs (files/dirs) to the file set, and run all jobs
    through the scheduler seam (`Driver.runAll`). Behind an opaque boundary so the
    non-`unsafe` `main` can invoke the unsafe frontend. -/
unsafe def runJobsImpl
           (files : List String)
           (width : Nat)
           (preset : String)
           : IO (Array Driver.Result) := do
  let base := (Style.byName? preset).getD Style.straylight
  let style := { base with layout := { base.layout with lineWidth := width } }
  let expanded ← Driver.expand (files.toArray.map System.FilePath.mk)
  Driver.runAll style expanded

@[implemented_by runJobsImpl]
opaque runJobs (files : List String) (width : Nat) (preset : String) : IO (Array Driver.Result)

def main
    (argv : List String)
    : IO Unit := do
  let o := Cli.parse argv
  if o.files.isEmpty then
    (← IO.getStderr).putStrLn Cli.usage
    IO.Process.exit 1

  initEnv
  let err ← IO.getStderr
  let results ← runJobs o.files o.width o.preset

  let mut failed := false
  for r in results do
    for d in r.diagnostics do
      err.putStrLn s!"{r.path}:{d.render}"
      if d.severity == .error then failed := true
    match o.mode with
    | .format => IO.print r.output
    | .check =>
      if r.changed then
        err.putStrLn s!"Would reformat: {r.path}"; failed := true
      else
        err.putStrLn s!"OK: {r.path}"
    | .write =>
      if r.changed then
        IO.FS.writeFile r.path r.output
        err.putStrLn s!"Formatted: {r.path}"
      else
        err.putStrLn s!"Unchanged: {r.path}"

  if failed then IO.Process.exit 1
