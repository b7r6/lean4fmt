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

/-- The field names of a structure declaration (first ident of each
    `structSimpleBinder`). Fields are the `terms` axis (schema: "def / abbrev /
    instance / fields"); collecting them lets the plan SEE a type↔field
    collision — a `Lang` type snaking to `lang` when a `lang` field exists must
    be blocked, not applied (the break the floor caught on core/build). -/
partial
def struct_field_names : Lean.Syntax → List String
  | .node _ k args =>
    let here : List String :=
      if k == ``Lean.Parser.Command.structSimpleBinder then
        match (Lean4Fmt.Emit.leaf_tokens (.node .none k args)).find? (·.isIdent) with
        | some id => [last_comp (Lean4Fmt.Emit.bare_src id)]
        | none    => []
      else
        []
    here ++ args.toList.flatMap struct_field_names
  | _ => []

/-- Every renamable top-level declaration of a parsed module as `(simple-name,
    axis)`, plus structure FIELDS (term axis). Namespaced decls are siblings
    (namespace/end are their own commands), so a flat command walk sees them. -/
def decls_of (stx : Lean.Syntax) : List (String × Lean4Fmt.Rename.axis) :=
  let cmds := ((stx.getArgs[1]?).map (·.getArgs)).getD #[]
  cmds.toList.flatMap
    (fun c =>
      if c.getKind == ``Lean.Parser.Command.declaration then
        match c.getArgs.findSome?
            (fun defn => (axis_of_kind defn.getKind).map (fun ax => (defn, ax))) with
        | some (defn, ax) =>
          let head := ((decl_name_of? defn).map (fun nm => (nm, ax))).toList
          let fields := if ax == .typ then (struct_field_names defn).map (·, .term) else []
          head ++ fields
        | none => []
      else [])

/-- The FULL declId text (`Foo.bar` for `def Foo.bar`, dropping `.{univs}`) — the
    whole name, not just the last component, so the namespace-qualified full name
    is exact. -/
def decl_full_of? (defn : Lean.Syntax) : Option String := do
  let declId ← defn.getArgs.find? (·.getKind == ``Lean.Parser.Command.declId)
  let idTok ← (Lean4Fmt.Emit.leaf_tokens declId).find? (·.isIdent)
  let src := (Lean4Fmt.Emit.bare_src idTok).trimAscii.toString
  if src.isEmpty then none
  else some src

/-- Every renamable declaration as `(FULL-name, axis)` — namespace/section
    context tracked so full names match the elaborator (`Continuity.Build.Cache.
    foo`), plus structure fields (`…Struct.field`, term axis). This is the set
    the resolution rename keys on. A `section` pushes an empty marker (no name
    contribution); `end` pops one; a nested `namespace A.B` pushes one element. -/
def decls_of_full (stx : Lean.Syntax) : List (String × Lean4Fmt.Rename.axis) :=
  let cmds := ((stx.getArgs[1]?).map (·.getArgs)).getD #[]
  let join :=
    fun (ns : List String) (nm : String) => String.intercalate "." ((ns.filter (· != "")) ++ [nm])
  let step :=
    fun (acc : List String × List (String × Lean4Fmt.Rename.axis)) (c : Lean.Syntax) =>
      let (ns, out) := acc
      let k := c.getKind
      if k == ``Lean.Parser.Command.namespace then
        (
          ns
              ++ [
                ((c.getArgs[1]?).map (fun s => (Lean4Fmt.Emit.bare_src s).trimAscii.toString)).getD
                  ""
              ],
          out
        )
      else if k == ``Lean.Parser.Command.section then
        (ns ++ [""], out)
      else if k == ``Lean.Parser.Command.end then
        (ns.dropLast, out)
      else if k == ``Lean.Parser.Command.declaration then
        match c.getArgs.findSome? (fun defn => (axis_of_kind defn.getKind).map (fun ax => (defn, ax))) with
        | some (defn, ax) =>
          match decl_full_of? defn with
          | some declName =>
            let full := join ns declName
            let fields :=
              if ax == .typ then
                (struct_field_names defn).map
                  (fun f => (full ++ "." ++ f, Lean4Fmt.Rename.axis.term))
              else
                []
            (ns, out ++ [(full, ax)] ++ fields)
          | none => (ns, out)
        | none => (ns, out)
      else
        (ns, out)
  (cmds.foldl step ([], [])).2

def axis_tag : Lean4Fmt.Rename.axis → String
  | .ns   => "ns"
  | .typ  => "typ"
  | .thm  => "thm"
  | .term => "term"

def axis_of_tag : String → Option Lean4Fmt.Rename.axis
  | "ns"   => some .ns
  | "typ"  => some .typ
  | "thm"  => some .thm
  | "term" => some .term
  | _      => none

/-- Prepend a prebuilt farm dir to the search path — the orchestrator builds the
    farm ONCE and hands each worker its path via `--farm`, so no per-subprocess
    rebuild. -/
def apply_farm (farm : Option String) : IO Unit :=
  match farm with
  | some f => Lean.searchPathRef.modify (fun sp => (⟨f⟩ : System.FilePath) :: sp)
  | none   => pure ()

/-- Worker (`--rename-decls`): parse the file under its OWN env and print
    `NAME<TAB>AXIS` for every renamable declaration to stdout. The orchestrator
    spawns one process per file, so each gets a clean single `importModules` —
    the multi-workspace-safe substitute for one union `batchEnv` (which throws
    when a cross-package olean resolves to the wrong build dir). -/
unsafe
def run_rename_decls_impl
    (files : List String)
    (resolve : Bool)
    (farmDir : Option String)
    (elabFallback : Bool)
    : IO Unit := do
  apply_farm farmDir
  let paths := files.toArray.map System.FilePath.mk
  let env ← Frontend.batch_env paths
  let out ← IO.getStdout
  let err ← IO.getStderr
  for p in paths do
    let contents ← IO.FS.readFile p
    if resolve then
      -- RESOLVED occurrences `lastComp<TAB>fullName<TAB>D|U` — the hybrid's input
      for (_, _, nm, isDef) in ← Frontend.Session.resolve_idents env p.toString contents do
        let full := nm.toString
        let lastC := (full.splitOn ".").getLastD full
        let d := if isDef then "D" else "U"
        out.putStrLn s!"{lastC}\t{full}\t{d}"
    else
      match ← Frontend.parse_full? env p.toString contents elabFallback with
      | some stx =>
        for (nm, ax) in decls_of stx do
          out.putStrLn s!"{nm}\t{axis_tag ax}"
      | none => err.putStrLn s!"rename-decls: SKIP (no parse) {p}"

@[implemented_by run_rename_decls_impl]
opaque run_rename_decls (files : List String) (resolve : Bool) (farmDir : Option String) (elabFallback : Bool) : IO Unit

/-- Token-aware rewrite of one parsed module by a precomputed map: splice only
    the `.ident` leaves whose text moves, end-to-start over the UTF-8 bytes
    (strings/comments/docstrings are never leaf idents, so they ride byte-exact). -/
unsafe
def rewrite_file
    (env : Lean.Environment)
    (map : List (String × String))
    (elabFallback : Bool)
    (p : System.FilePath)
    : IO Unit := do
  let err ← IO.getStderr
  let contents ← IO.FS.readFile p
  match ← Frontend.parse_full? env p.toString contents elabFallback with
  | none => err.putStrLn s!"rename-rewrite: SKIP (no parse) {p}"
  | some stx =>
    let idents := (Lean4Fmt.Emit.leaf_tokens stx).filter (·.isIdent)
    let mut edits : Array (Nat × Nat × String) := #[]
    for id in idents do
      match id.getSubstring? false false with
      | some ss =>
        match Lean4Fmt.Rename.ident_replacement map ss.toString with
        | some newText => edits := edits.push (ss.startPos.byteIdx, ss.stopPos.byteIdx, newText)
        | none => pure ()
      | none => pure ()
    if edits.isEmpty then
      return
    -- end-to-start: applying larger offsets first keeps smaller ones valid
    let sorted := edits.qsort (fun a b => a.1 > b.1)
    let mut ba := contents.toUTF8
    for (s, e, new) in sorted do
      ba := (ba.extract 0 s) ++ new.toUTF8 ++ (ba.extract e ba.size)
    IO.FS.writeFile p (String.fromUTF8! ba)
    err.putStrLn s!"rewrite: {p} ({edits.size} idents)"

/-- G-L7.4d resolution rewrite of one file: elaborate, then for each RESOLVED
    occurrence `(range, fullName)` rewrite the token iff `fullName` (or a prefix)
    is in the identity `map` — the last-K-components rule preserves qualification.
    Overlap-safe splice: descending by start, skip any range overlapping the
    already-applied one (the elaborator's rare same-start-different-stop dups). -/
unsafe
def resolve_rewrite_file
    (env : Lean.Environment)
    (map : List (String × String))
    (p : System.FilePath)
    : IO Unit := do
  let err ← IO.getStderr
  let contents ← IO.FS.readFile p
  let bytes := contents.toUTF8
  let occs ← Frontend.Session.resolve_idents env p.toString contents
  let mut edits : Array (Nat × Nat × String) := #[]
  for (s, e, nm, _) in occs do
    let tokenText := String.fromUTF8! (bytes.extract s e)
    match Lean4Fmt.Rename.resolved_rewrite map tokenText nm.toString with
    | some newText => edits := edits.push (s, e, newText)
    | none => pure ()
  if edits.isEmpty then
    return
  let sorted := edits.qsort (fun a b => a.1 > b.1)
  let mut ba := bytes
  let mut lastStart := ba.size + 1
  let mut n := 0
  for (s, e, new) in sorted do
    if e <= lastStart then
      ba := (ba.extract 0 s) ++ new.toUTF8 ++ (ba.extract e ba.size)
      lastStart := s
      n := n + 1
  IO.FS.writeFile p (String.fromUTF8! ba)
  err.putStrLn s!"rewrite: {p} ({n} idents, resolved)"

/-- Worker (`--rename-rewrite --map F`): read the map, rewrite the file in place
    under its own env — token spelling, or RESOLVED identity under `--resolve`. -/
unsafe
def run_rename_rewrite_impl
    (files : List String)
    (mapFile : Option String)
    (resolve : Bool)
    (farmDir : Option String)
    (elabFallback : Bool)
    : IO Unit := do
  apply_farm farmDir
  let err ← IO.getStderr
  match mapFile with
  | none => err.putStrLn "rename-rewrite: --map <file> required"
  | some mf =>
    let mapText ← IO.FS.readFile ⟨mf⟩
    let map : List (String × String) := mapText.splitOn "\n" |>.filterMap (fun line =>
      match line.splitOn "\t" with
      | [s, t] => if s.isEmpty then none else some (s, t)
      | _ => none)
    let paths := files.toArray.map System.FilePath.mk
    let env ← Frontend.batch_env paths
    -- pass 2 is always the TOKEN rewrite; under --resolve the MAP was already
    -- filtered to unambiguous+defined simple names by the hybrid plan, so the
    -- token rewrite is both safe (no cross-package over-match) and COMPLETE
    -- (catches binder-type spellings the InfoTree doesn't record)
    for p in paths do
      rewrite_file env map elabFallback p

@[implemented_by run_rename_rewrite_impl]
opaque run_rename_rewrite (files : List String) (mapFile : Option String) (resolve : Bool) (farmDir : Option String) (elabFallback : Bool) : IO Unit

/-- The module symbol table (G-L7.4): a MERGED SYMLINK FARM of every package's
    built oleans, put FIRST on the search path. `findOLean` resolves a module by
    its ROOT namespace (`Continuity`) to the first search dir that has that root,
    and does NOT check the full olean exists — so a multi-dir path can't
    disambiguate a root split across packages (codec's `Continuity/` wins for
    `Continuity.Trust.Discharge`, whose olean it doesn't own → `imports_env`
    silently drops it, and the parse batch threw on Box). Merging all lib dirs
    into ONE `Continuity/` root (via `cp -rsn` recursive symlinks — the trick
    corpus-gate.sh / lean4fmt.sh use) makes every module resolve to its true
    owner. Repo root = nearest `.git` ancestor of the first input. -/
unsafe
def make_olean_farm (files : List String) : IO (Option String) := do
  let some f0 := files.head? | return none
  let p0 ← try IO.FS.realPath ⟨f0⟩ catch _ => pure ⟨f0⟩
  let mut dir? := p0.parent
  let mut root? : Option System.FilePath := none
  let mut steps := 0
  while h : dir?.isSome ∧ steps < 64 do
    let dir := dir?.get h.1
    if ← (dir / ".git").pathExists then
      root? := some dir
      dir? := none
    else dir? := dir.parent
    steps := steps + 1
  let some root := root? | return none
  let dirs ← try
      let r ← IO.Process.output
        { cmd := "find",
          args := #[root.toString, "-type", "d", "-path", "*/.lake/build/lib/lean", "-prune"] }
      pure ((r.stdout.splitOn "\n").filter (fun s => !s.isEmpty))
    catch _ => pure ([] : List String)
  if dirs.isEmpty then
    return none
  let farm := (← IO.Process.run { cmd := "mktemp", args := #["-d"] }).trim
  for d in dirs do
    try let _ ← IO.Process.output { cmd := "cp", args := #["-rsn", s!"{d}/.", s!"{farm}/"] }
    catch _ => pure ()
  Lean4Fmt.Log.log .debug s!"olean farm: {farm} ({dirs.length} lib dirs merged)"
  return some farm

/-- G-L7.4 probe (`--resolve-dump`): elaborate the file(s) and print each resolved
    ident occurrence as `start-stop<TAB>fullName`. Validates that the InfoTree
    disambiguation works before the token map is swapped for it. -/
unsafe
def run_resolve_dump_impl (files : List String) : IO Unit := do
  let paths := files.toArray.map System.FilePath.mk
  apply_farm (← make_olean_farm files)
  let env ← Frontend.batch_env paths
  let out ← IO.getStdout
  for p in paths do
    let contents ← IO.FS.readFile p
    for (s, e, nm, isDef) in ← Frontend.Session.resolve_idents env p.toString contents do
      let tag := if isDef then "DEF" else "use"
      out.putStrLn s!"{s}-{e}\t{nm}\t{tag}"

@[implemented_by run_resolve_dump_impl]
opaque run_resolve_dump (files : List String) : IO Unit

/-- G-L7.3 orchestrator (`--rename-apply`): the multi-workspace-safe driver.
    `importModules` is one-shot per process, so instead of one union `batchEnv`,
    spawn a worker subprocess PER FILE — each with its own clean env. Pass 1
    collects the decl set GLOBALLY (collisions are cross-file); pass 2 rewrites
    each file by the shared plan. Bounded concurrent waves (`LEAN4FMT_JOBS`,
    default 8). The build is the floor; a bad rename is a failed make. -/
unsafe
def run_rename_apply_impl
    (files : List String)
    (preset : String)
    (resolve : Bool)
    (elabFallback : Bool)
    : IO Unit := do
  let err ← IO.getStderr
  let exe := (← IO.appPath).toString
  let paths := files.toArray.map System.FilePath.mk
  let naming := ((Lean4Fmt.Style.by_name? preset).getD Lean4Fmt.Style.straylight).naming
  let modules := files.filterMap (fun f => (System.FilePath.mk f).fileStem)
  let jobs := (((← IO.getEnv "LEAN4FMT_JOBS").bind (·.toNat?)).getD 8).max 1
  -- resolution: build the olean farm ONCE, hand each worker its path via --farm
  let farm ← if resolve then make_olean_farm files else pure none
  let extra :=
    (if elabFallback then #[] else #["--elab", "off"])
        ++ (if resolve then
          #["--resolve", "--lake", "off"]
              ++ (match farm with
              | some f => #["--farm", f]
              | none   => #[])
        else
          #[])
  -- PASS 1: extract decls, one subprocess per file (own env), bounded waves.
  -- resolve mode emits FULL names (one/line); token mode emits NAME<TAB>AXIS.
  let spawn1 (p : System.FilePath) : IO (IO.Process.Child ⟨.null, .piped, .piped⟩) :=
    IO.Process.spawn
      { cmd    := exe,
        args   := #["--rename-decls", "--no-retry"] ++ extra ++ #[p.toString],
        stdin  := .null,
        stdout := .piped,
        stderr := .piped }
  let mut allDecls : List (String × Lean4Fmt.Rename.axis) := []
  let mut occs : List (String × String) := [] -- (lastComp, fullName) resolved occurrences
  let mut defs : List String := [] -- full names DEFINED in the set
  let mut i := 0
  while i < paths.size do
    let wave := paths.extract i (Nat.min (i + jobs) paths.size)
    let mut children : Array (IO.Process.Child ⟨.null, .piped, .piped⟩) := #[]
    for p in wave do
      children := children.push (← spawn1 p)
    for child in children do
      let out ← child.stdout.readToEnd
      let _ ← child.stderr.readToEnd
      let _ ← child.wait
      for line in out.splitOn "\n" do
        if resolve then
          match line.splitOn "\t" with
          | [lastC, full, d] =>
            occs := occs ++ [(lastC, full)]
            if d == "D" then defs := defs ++ [full]
          | _ => pure ()
        else
          match line.splitOn "\t" with
          | [nm, tag] =>
            match axis_of_tag tag with
            | some ax => allDecls := allDecls ++ [(nm, ax)]
            | none => pure ()
          | _ => pure ()
    i := i + jobs
  -- the plan: HYBRID under --resolve (resolution decides, token acts), else token
  let (renames, skipped) :=
    if resolve then
      Lean4Fmt.Rename.plan_hybrid .snake modules occs defs
    else
      let p := Lean4Fmt.Rename.build_plan naming modules allDecls; (p.renames, p.skipped)
  let tag := if resolve then "resolve" else preset
  err.putStrLn
    s!"// rename apply ({tag}): {renames.length} renames, {skipped.length} skipped over {paths.size} files"
  for (nm, tgt) in skipped do
    err.putStrLn s!"//   SKIP {nm} → {tgt}"
  if renames.isEmpty then
    return
  -- hand the map to the rewrite workers via a temp file (SRC<TAB>TGT; SRC is the
  -- FULL name and TGT the new last-component under --resolve)
  let mapPath := s!"{((← IO.getEnv "TMPDIR").getD "/tmp")}/lean4fmt-rename.map"
  IO.FS.writeFile ⟨mapPath⟩ (String.intercalate "\n" (renames.map (fun (s, t) => s!"{s}\t{t}")))
  -- PASS 2: rewrite each file, one subprocess per file, bounded waves
  let spawn2 (p : System.FilePath) : IO (IO.Process.Child ⟨.null, .piped, .piped⟩) :=
    IO.Process.spawn
      { cmd    := exe,
        args   := #["--rename-rewrite", "--map", mapPath, "--no-retry"] ++ extra ++ #[p.toString],
        stdin  := .null,
        stdout := .piped,
        stderr := .piped }
  let mut renamed := 0
  let mut j := 0
  while j < paths.size do
    let wave := paths.extract j (Nat.min (j + jobs) paths.size)
    let mut children : Array (IO.Process.Child ⟨.null, .piped, .piped⟩) := #[]
    for p in wave do
      children := children.push (← spawn2 p)
    for child in children do
      let _ ← child.stdout.readToEnd
      let e2 ← child.stderr.readToEnd
      let _ ← child.wait
      for line in e2.splitOn "\n" do
        if line.startsWith "rewrite: " then
          renamed := renamed + 1
          err.putStrLn s!"//   {line}"
    j := j + jobs
  err.putStrLn s!"// rewrote {renamed} files"

@[implemented_by run_rename_apply_impl]
opaque run_rename_apply (files : List String) (preset : String) (resolve : Bool) (elabFallback : Bool) : IO Unit

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
    run_rename_apply o.files o.preset o.resolve o.elabFallback
    return
  if o.mode == .renameDecls then
    run_rename_decls o.files o.resolve o.farmDir o.elabFallback
    return
  if o.mode == .renameRewrite then
    run_rename_rewrite o.files o.mapFile o.resolve o.farmDir o.elabFallback
    return
  if o.mode == .resolveDump then
    run_resolve_dump o.files
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
    | .renameDecls => pure ()   -- unreachable: renameDecls returns above
    | .renameRewrite => pure ()   -- unreachable: renameRewrite returns above
    | .resolveDump => pure ()   -- unreachable: resolveDump returns above
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
