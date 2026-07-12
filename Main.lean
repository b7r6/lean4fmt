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
import StdlibEx.Logging
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
           (elabFallback : Bool)
           (retry : Bool)
           (logLevel : String)
           : IO (Array Driver.Result) := do
  let base := (Style.byName? preset).getD Style.straylight
  let style := { base with layout := { base.layout with lineWidth := width } }
  let expanded ← Driver.expand (files.toArray.map System.FilePath.mk)
  let retryCfg ← do
    if retry then
      let exe ← IO.appPath
      pure (some (exe.toString,
        #["--width", toString width, "--style", preset, "--log-level", logLevel]
          ++ (if elabFallback then #[] else #["--elab", "off"])))
    else pure none
  Driver.runAll style expanded elabFallback retryCfg

@[implemented_by runJobsImpl]
opaque runJobs
    (files : List String) (width : Nat) (preset : String) (elabFallback : Bool) (retry : Bool)
    (logLevel : String)
    : IO (Array Driver.Result)

/-- Coverage accounting (`--stats`, DESIGN_V2 §15): per-file
    active/verbatim/trivia byte rows plus the aggregate. Files the shared env
    cannot parse retry as one-file `--stats` subprocesses (own env); a file
    nothing can parse counts fully verbatim — passthrough is what it gets. -/
unsafe def runStatsImpl
           (files : List String)
           (width : Nat)
           (preset : String)
           (elabFallback : Bool)
           (retry : Bool)
           : IO (Array (Nat × Nat × Nat × String)) := do
  let base := (Style.byName? preset).getD Style.straylight
  let style := { base with layout := { base.layout with lineWidth := width } }
  let expanded ← Driver.expand (files.toArray.map System.FilePath.mk)
  let env ← Frontend.batchEnv expanded
  let exe ← IO.appPath
  let mut rows : Array (Nat × Nat × Nat × String) := #[]
  for p in expanded do
    let contents ← IO.FS.readFile p
    let style ← Driver.styleFor style p
    match ← Frontend.statsFor env p.toString contents style elabFallback with
    | some (a, v, t) => rows := rows.push (a, v, t, p.toString)
    | none =>
      let sub? ← do
        if !retry then pure none else
        let r ← IO.Process.output
          { cmd := exe.toString,
            args := #["--stats", "--no-retry", "--width", toString width,
                      "--style", preset, p.toString] }
        match ((r.stdout.splitOn "\n").headD "").splitOn " " with
        | [a, v, t, _] =>
          pure (match a.toNat?, v.toNat?, t.toNat? with
                | some a, some v, some t => some (a, v, t)
                | _, _, _ => none)
        | _ => pure none
      match sub? with
      | some (a, v, t) => rows := rows.push (a, v, t, p.toString)
      | none => rows := rows.push (0, contents.utf8ByteSize, 0, p.toString)
  return rows

@[implemented_by runStatsImpl]
opaque runStats
    (files : List String) (width : Nat) (preset : String) (elabFallback : Bool) (retry : Bool)
    : IO (Array (Nat × Nat × Nat × String))

def main
    (argv : List String)
    : IO Unit := do
  let o := Cli.parse argv
  if o.files.isEmpty then
    (← IO.getStderr).putStrLn Cli.usage
    IO.Process.exit 1

  initEnv
  let lvl : StdlibEx.Logging.Level := match o.logLevel with
    | "trace" => .trace
    | "debug" => .debug
    | "info" => .info
    | "warn" => .warn
    | "error" => .error
    | _ => .warn
  StdlibEx.Logging.initConsole lvl
  let err ← IO.getStderr

  if o.mode == .stats then
    let rows ← runStats o.files o.width o.preset o.elabFallback o.retry
    let mut ta := 0
    let mut tv := 0
    let mut tt := 0
    for row in rows do
      let a := row.1; let v := row.2.1; let t := row.2.2.1; let p := row.2.2.2
      IO.println s!"{a} {v} {t} {p}"
      ta := ta + a; tv := tv + v; tt := tt + t
    let code := ta + tv
    let pct (n d : Nat) : String :=
      if d == 0 then "-" else s!"{(n * 1000 / d) / 10}.{(n * 1000 / d) % 10}%"
    IO.println s!"// files {rows.size}  bytes active={ta} verbatim={tv} trivia={tt}"
    IO.println s!"// coverage: code-active {pct ta code}  (of all output: active {pct ta (code + tt)}, trivia {pct tt (code + tt)})"
    return

  let results ← runJobs o.files o.width o.preset o.elabFallback o.retry o.logLevel

  let mut failed := false
  for r in results do
    for d in r.diagnostics do
      let lvl : StdlibEx.Logging.Level := match d.severity with
        | .debug => .debug
        | .info => .info
        | .warning => .warn
        | .error => .error
      StdlibEx.Logging.log lvl s!"{r.path}:{d.render}"
      if d.severity == .error then failed := true
    match o.mode with
    | .stats => pure ()   -- unreachable: stats returns above
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
