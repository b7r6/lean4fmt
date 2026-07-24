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
import Lean4Fmt.Rename
import Lean4Fmt.Emit.Tokens
import Lean4Fmt.Style.Preset

open Lean
open Lean4Fmt

unsafe
def init_env_impl : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution -- required before importing modules with syntax extensions

@[implemented_by init_env_impl]
opaque init_env : IO Unit

/-- Lake workspace discovery (milestone 2): walk up from each input to a
    lakefile; one `lake env printenv LEAN_PATH` per distinct workspace root
    supplies the olean search path for that workspace's imports — no
    hand-built symlink farm. Additive and failure-tolerant: entries APPEND
    to the search path (an explicit LEAN_PATH keeps first-match priority),
    and a missing or failing `lake` is a silent skip, never an error. -/
unsafe
def add_lake_paths_impl (files : List String) : IO Unit := do

  -- an explicit LEAN_PATH is the caller taking control (corpus-gate's farm,
  -- batch loops): skip the ~1.6s/root lake startup — discovery is the
  -- ZERO-CONFIG path, not an override
  if ((← IO.getEnv "LEAN_PATH").getD "") != "" then
    return
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

@[implemented_by add_lake_paths_impl]
opaque add_lake_paths (files : List String) : IO Unit

/-- Resolve style, expand inputs (files/dirs) to the file set, and run all jobs
    through the scheduler seam (`Driver.runAll`). Behind an opaque boundary so the
    non-`unsafe` `main` can invoke the unsafe frontend. -/
unsafe
def run_jobs_impl
    (files : List String)
    (width : Option Nat)
    (preset : String)
    (elabFallback : Bool)
    (retry : Bool)
    (logLevel : String)
    (lakeEnv : Bool)
    : IO (Array Driver.result) := do
  let base := (Style.by_name? preset).getD Style.straylight
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
  Driver.run_all style expanded elabFallback retryCfg

@[implemented_by run_jobs_impl]
opaque run_jobs (files : List String) (width : Option Nat) (preset : String) (elabFallback : Bool) (retry : Bool) (logLevel : String) (lakeEnv : Bool) :
    IO (Array Driver.result)

/-- Coverage accounting (`--stats`, DESIGN_V2 §15): per-file
    active/verbatim/trivia byte rows plus the aggregate. Files the shared env
    cannot parse retry as one-file `--stats` subprocesses (own env); a file
    nothing can parse counts fully verbatim — passthrough is what it gets. -/
unsafe
def run_stats_impl
    (files : List String)
    (width : Option Nat)
    (preset : String)
    (elabFallback : Bool)
    (retry : Bool)
    : IO (Array (Nat × Nat × Nat × Nat × String)) := do
  let base := (Style.by_name? preset).getD Style.straylight
  let style :=
    match width with
    | some w => { base with layout := { base.layout with lineWidth := w } }
    | none   => base
  let expanded ← Driver.expand (files.toArray.map System.FilePath.mk)
  let env ← Frontend.batch_env expanded
  let exe ← IO.appPath
  let mut rows : Array (Nat × Nat × Nat × Nat × String) := #[]
  for p in expanded do
    let contents ← IO.FS.readFile p
    let style ← Driver.style_for style p
    match ← Frontend.stats_for env p.toString contents style elabFallback with
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

@[implemented_by run_stats_impl]
opaque run_stats (files : List String) (width : Option Nat) (preset : String) (elabFallback : Bool) (retry : Bool) :
    IO (Array (Nat × Nat × Nat × Nat × String))

-- ── the rename apply (G-L7.1): parse-based, token-aware identifier rewrite ────

/-- Last dotted component of a name (`Foo.bar` → `bar`). -/
def last_comp (s : String) : String := (s.splitOn ".").getLastD s

/-- The naming axis a declaration node's KIND falls on, or `none` (example, or a
    command that declares no renamable name). -/
def axis_of_kind (k : Lean.Name) : Option Lean4Fmt.Rename.axis :=
  if k == ``Lean.Parser.Command.definition || k == ``Lean.Parser.Command.abbrev
      || k == ``Lean.Parser.Command.opaque
      || k == ``Lean.Parser.Command.instance then
    some .term
  else if k == ``Lean.Parser.Command.theorem || k == ``Lean.Parser.Command.axiom then
    some .thm
  else if k == ``Lean.Parser.Command.structure || k == ``Lean.Parser.Command.inductive then
    some .typ
  else
    none

/-- The declared simple-name of a definition node: the first ident of its
    `declId` child, last dotted component. `none` for anonymous decls (an
    unnamed instance) or a node with no declId. -/
def decl_name_of? (defn : Lean.Syntax) : Option String := do
  let declId ← defn.getArgs.find? (·.getKind == ``Lean.Parser.Command.declId)
  let idTok ← (Lean4Fmt.Emit.leaf_tokens declId).find? (·.isIdent)
  let src := Lean4Fmt.Emit.bare_src idTok
  if src.isEmpty then none
  else some (last_comp src)

/-- Every renamable top-level declaration of a parsed module as `(simple-name,
    axis)`. Namespaced decls are siblings (namespace/end are their own
    commands), so a flat command walk sees them all. -/
def decls_of (stx : Lean.Syntax) : List (String × Lean4Fmt.Rename.axis) :=
  let cmds := ((stx.getArgs[1]?).map (·.getArgs)).getD #[]
  cmds.toList.filterMap
    (fun c =>
      if c.getKind == ``Lean.Parser.Command.declaration then
        c.getArgs.findSome?
          (fun defn => match axis_of_kind defn.getKind with
            | some ax => (decl_name_of? defn).map (fun nm => (nm, ax))
            | none    => none)
      else
        none)

/-- G-L7.1 apply: parse every file under one batch env, collect the decl set
    across the WHOLE input (so collisions are global), build the plan (preset
    naming + the module-basename exemption), then rewrite each file token-aware —
    only `.ident` leaves whose text moves under the map are spliced, end-to-start
    over the UTF-8 bytes (strings/comments/docstrings are never leaf idents, so
    they ride byte-exact). The build is the floor; a bad rename is a failed
    make, not corrupted source. -/
unsafe
def run_rename_apply_impl
    (files : List String)
    (preset : String)
    (elabFallback : Bool)
    : IO Unit := do
  let paths := files.toArray.map System.FilePath.mk
  let env ← Frontend.batch_env paths
  let naming := ((Lean4Fmt.Style.by_name? preset).getD Lean4Fmt.Style.straylight).naming
  let modules := files.filterMap (fun f => (System.FilePath.mk f).fileStem)
  let err ← IO.getStderr
  let mut allDecls : List (String × Lean4Fmt.Rename.axis) := []
  let mut parsed : Array (System.FilePath × String × Lean.Syntax) := #[]
  for p in paths do
    let contents ← IO.FS.readFile p
    match ← Frontend.parse_full? env p.toString contents elabFallback with
    | some stx =>
      allDecls := allDecls ++ decls_of stx
      parsed := parsed.push (p, contents, stx)
    | none => err.putStrLn s!"rename: SKIP (no parse) {p}"
  let plan := Lean4Fmt.Rename.build_plan naming modules allDecls
  let map := plan.renames
  err.putStrLn
    s!"// rename apply (preset {preset}): {map.length} renames, {plan.skipped.length} skipped over {parsed.size} files"
  for (nm, tgt) in plan.skipped do
    err.putStrLn s!"//   SKIP {nm} → {tgt}  (collision / keyword / module-basename)"
  for (p, contents, stx) in parsed do
    let idents := (Lean4Fmt.Emit.leaf_tokens stx).filter (·.isIdent)
    let mut edits : Array (Nat × Nat × String) := #[]
    for id in idents do
      match id.getSubstring? false false with
      | some ss =>
        match Lean4Fmt.Rename.ident_replacement map ss.toString with
        | some newText => edits := edits.push (ss.startPos.byteIdx, ss.stopPos.byteIdx, newText)
        | none => pure ()
      | none => pure ()
    if edits.isEmpty then continue
    -- end-to-start: applying larger offsets first keeps smaller ones valid
    let sorted := edits.qsort (fun a b => a.1 > b.1)
    let mut ba := contents.toUTF8
    for (s, e, new) in sorted do
      ba := (ba.extract 0 s) ++ new.toUTF8 ++ (ba.extract e ba.size)
    IO.FS.writeFile p (String.fromUTF8! ba)
    err.putStrLn s!"rename: {p} ({edits.size} idents)"

@[implemented_by run_rename_apply_impl]
opaque run_rename_apply (files : List String) (preset : String) (elabFallback : Bool) : IO Unit

def main (argv : List String) : IO Unit := do
  let o := Cli.parse argv
  if o.mode == .renamePlan then
    -- read `NAME AXIS` lines on stdin (AXIS ∈ ns|typ|thm|term), apply the preset's
    -- naming policy through the verified plan builder, print renames + skips.
    let naming := ((Lean4Fmt.Style.by_name? o.preset).getD Lean4Fmt.Style.straylight).naming
    let input ← (← IO.getStdin).readToEnd
    let decls : List (String × Lean4Fmt.Rename.axis) :=
      input.splitOn "\n"
        |>.filterMap
          (fun line =>
            match (line.trimAscii.toString.splitOn " ").filter (· ≠ "") with
            | [nm, ax] =>
              match ax with
              | "ns" => some (nm, .ns)
              | "typ" => some (nm, .typ)
              | "thm" => some (nm, .thm)
              | "term" => some (nm, .term)
              | _ => none
            | _ => none)
    let plan := Lean4Fmt.Rename.build_plan naming [] decls
    IO.println
      s!"// rename plan (preset {o.preset}): {plan.renames.length} rename, {plan.skipped.length} skip"
    for (nm, tgt) in plan.renames do
      IO.println s!"  {nm} → {tgt}"
    for (nm, tgt) in plan.skipped do
      IO.println s!"  SKIP {nm} → {tgt}"
    return
  if o.files.isEmpty then
    (← IO.getStderr).putStrLn Cli.usage
    IO.Process.exit 1

  init_env
  Lean4Fmt.Log.set_level (Lean4Fmt.Log.level.of_string o.logLevel)
  if o.lakeEnv then add_lake_paths o.files
  let err ← IO.getStderr

  if o.mode == .renameApply then
    run_rename_apply o.files o.preset o.elabFallback
    return

  if o.mode == .stats then
    let rows ← run_stats o.files o.width o.preset o.elabFallback o.retry
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

  let results ← run_jobs o.files o.width o.preset o.elabFallback o.retry o.logLevel o.lakeEnv

  let mut failed := false
  for r in results do
    for d in r.diagnostics do
      let lvl : Lean4Fmt.Log.level :=
        match d.severity with
        | .debug   => .debug
        | .info    => .info
        | .warning => .warn
        | .error   => .error
      Lean4Fmt.Log.log lvl s!"{r.path}:{d.render}"
      if d.severity == .error then failed := true
    match o.mode with
    | .stats => pure ()   -- unreachable: stats returns above
    | .renamePlan => pure ()   -- unreachable: renamePlan returns above
    | .renameApply => pure ()   -- unreachable: renameApply returns above
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
