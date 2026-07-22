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
import Lean4Fmt.Log
import Lean4Fmt.Cli
import Lean4Fmt.Driver

open Lean
open Lean4Fmt

unsafe def initEnvImpl
           : IO Unit := do

  initSearchPath (← findSysroot)
  enableInitializersExecution -- required before importing modules with syntax extensions

@[implemented_by initEnvImpl]
opaque initEnv : IO Unit

/-- Lake workspace discovery (milestone 2): walk up from each input to a
    lakefile; one `lake env printenv LEAN_PATH` per distinct workspace root
    supplies the olean search path for that workspace's imports — no
    hand-built symlink farm. Additive and failure-tolerant: entries APPEND
    to the search path (an explicit LEAN_PATH keeps first-match priority),
    and a missing or failing `lake` is a silent skip, never an error. -/
unsafe def addLakePathsImpl
           (files : List String)
           : IO Unit := do

  -- an explicit LEAN_PATH is the caller taking control (corpus-gate's farm,
  -- batch loops): skip the ~1.6s/root lake startup — discovery is the
  -- ZERO-CONFIG path, not an override
  if ((← IO.getEnv "LEAN_PATH").getD "") != "" then return
  let mut roots : Array System.FilePath := #[]
  for f in files do
    -- absolute first: a bare relative path's parent chain ends BEFORE the
    -- cwd (parent "Lithe" = none), so the workspace root is never seen
    let p ← try IO.FS.realPath ⟨f⟩ catch _ => pure ⟨f⟩
    let mut dir? := if (← p.isDir) then some p else p.parent
    let mut steps := 0
    while h : dir?.isSome ∧ steps < 64 do
      let dir := dir?.get h.1
      if (← (dir / "lakefile.lean").pathExists) || (← (dir / "lakefile.toml").pathExists) then
        if !roots.contains dir then roots := roots.push dir
        dir? := none
      else dir? := dir.parent
      steps := steps + 1
  for root in roots do
    try
      let r ← IO.Process.output
        { cmd := "lake", args := #["env", "printenv", "LEAN_PATH"], cwd := root }
      if r.exitCode == 0 then
        let entries := ((r.stdout.splitOn "\n").headD "").splitOn ":"
          |>.filter (fun s => !s.isEmpty) |>.map System.FilePath.mk
        if !entries.isEmpty then
          Lean.searchPathRef.modify (· ++ entries)
          Lean4Fmt.Log.log .debug s!"lake env: {root} → {entries.length} search paths"
      else
        Lean4Fmt.Log.log .debug s!"lake env failed at {root} (exit {r.exitCode})"
    catch e =>
      Lean4Fmt.Log.log .debug s!"lake env unavailable at {root}: {e}"

@[implemented_by addLakePathsImpl]
opaque addLakePaths (files : List String) : IO Unit

/-- Resolve style, expand inputs (files/dirs) to the file set, and run all jobs
    through the scheduler seam (`Driver.runAll`). Behind an opaque boundary so the
    non-`unsafe` `main` can invoke the unsafe frontend. -/
unsafe def runJobsImpl
           (files : List String)
           (width : Option Nat)
           (preset : String)
           (elabFallback : Bool)
           (retry : Bool)
           (logLevel : String)
           (lakeEnv : Bool)
           : IO (Array Driver.Result) := do

  let base := (Style.byName? preset).getD Style.straylight
  let style :=
    match width with
    | some w => { base with layout := { base.layout with lineWidth := w } }
    | none   => base
  let expanded ← Driver.expand (files.toArray.map System.FilePath.mk)
  let retryCfg ← do
    if retry then
      let exe ← IO.appPath
      pure (some (exe.toString,
        (match width with | some w => #["--width", toString w] | none => #[])
          ++ #["--style", preset, "--log-level", logLevel]
          ++ (if elabFallback then #[] else #["--elab", "off"])
          -- the augmented search path is in-process; the child re-discovers
          -- (or matches an explicit --lake off)
          ++ (if lakeEnv then #[] else #["--lake", "off"])))
    else pure none
  Driver.runAll style expanded elabFallback retryCfg

@[implemented_by runJobsImpl]
opaque runJobs (files : List String) (width : Option Nat) (preset : String) (elabFallback : Bool) (retry : Bool) (logLevel : String) (lakeEnv : Bool) :
    IO (Array Driver.Result)

/-- Coverage accounting (`--stats`, DESIGN_V2 §15): per-file
    active/verbatim/trivia byte rows plus the aggregate. Files the shared env
    cannot parse retry as one-file `--stats` subprocesses (own env); a file
    nothing can parse counts fully verbatim — passthrough is what it gets. -/
unsafe def runStatsImpl
           (files : List String)
           (width : Option Nat)
           (preset : String)
           (elabFallback : Bool)
           (retry : Bool)
           : IO (Array (Nat × Nat × Nat × Nat × String)) := do

  let base := (Style.byName? preset).getD Style.straylight
  let style :=
    match width with
    | some w => { base with layout := { base.layout with lineWidth := w } }
    | none   => base
  let expanded ← Driver.expand (files.toArray.map System.FilePath.mk)
  let env ← Frontend.batchEnv expanded
  let exe ← IO.appPath
  let mut rows : Array (Nat × Nat × Nat × Nat × String) := #[]
  for p in expanded do
    let contents ← IO.FS.readFile p
    let style ← Driver.styleFor style p
    match ← Frontend.statsFor env p.toString contents style elabFallback with
    | some (a, v, t, pol) => rows := rows.push (a, v, t, pol, p.toString)
    | none =>
      let sub? ← do
        if !retry then pure none else
        let r ← IO.Process.output
          { cmd := exe.toString,
            args := #["--stats", "--no-retry"]
              ++ (match width with | some w => #["--width", toString w] | none => #[])
              ++ #["--style", preset, p.toString] }
        match ((r.stdout.splitOn "\n").headD "").splitOn " " with
        | [a, v, t, pol, _] =>
          pure (match a.toNat?, v.toNat?, t.toNat?, pol.toNat? with
                | some a, some v, some t, some pol => some (a, v, t, pol)
                | _, _, _, _ => none)
        | _ => pure none
      match sub? with
      | some (a, v, t, pol) => rows := rows.push (a, v, t, pol, p.toString)
      | none => rows := rows.push (0, contents.utf8ByteSize, 0, 0, p.toString)
  return rows

@[implemented_by runStatsImpl]
opaque runStats (files : List String) (width : Option Nat) (preset : String) (elabFallback : Bool) (retry : Bool) :
    IO (Array (Nat × Nat × Nat × Nat × String))

def main
    (argv : List String)
    : IO Unit := do

  let o := Cli.parse argv
  if o.files.isEmpty then
    (← IO.getStderr).putStrLn Cli.usage
    IO.Process.exit 1

  initEnv
  Lean4Fmt.Log.setLevel (Lean4Fmt.Log.Level.ofString o.logLevel)
  if o.lakeEnv then addLakePaths o.files
  let err ← IO.getStderr

  if o.mode == .stats then
    let rows ← runStats o.files o.width o.preset o.elabFallback o.retry
    let mut ta := 0
    let mut tv := 0
    let mut tt := 0
    let mut tp := 0
    for row in rows do
      let a := row.1; let v := row.2.1; let t := row.2.2.1
      let pol := row.2.2.2.1; let p := row.2.2.2.2
      IO.println s!"{a} {v} {t} {pol} {p}"
      ta := ta + a; tv := tv + v; tt := tt + t; tp := tp + pol
    let code := ta + tv
    -- policy content (moduleDoc/header/quotation commands) is permanently
    -- verbatim by design: the PORTABLE code — the honest denominator for
    -- "how much could active formatting ever cover" — excludes it
    let portable := code - Nat.min tp code
    let pct (n d : Nat) : String :=
      if d == 0 then "-" else s!"{(n * 1000 / d) / 10}.{(n * 1000 / d) % 10}%"
    IO.println s!"// files {rows.size}  bytes active={ta} verbatim={tv} trivia={tt} policy={tp}"
    IO.println
      s!"// coverage: code-active {pct ta code}  (of all output: active {pct ta (code + tt)}, trivia {pct tt (code + tt)})"
    IO.println
      s!"// ceiling: portable {pct portable code} of code; active-of-portable {pct ta portable}"
    return

  let results ← runJobs o.files o.width o.preset o.elabFallback o.retry o.logLevel o.lakeEnv

  let mut failed := false
  for r in results do
    for d in r.diagnostics do
      let lvl : Lean4Fmt.Log.Level :=
        match d.severity with
        | .debug   => .debug
        | .info    => .info
        | .warning => .warn
        | .error   => .error
      Lean4Fmt.Log.log lvl s!"{r.path}:{d.render}"
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
