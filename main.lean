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
import lean_4_fmt.log
import lean_4_fmt.cli
import lean_4_fmt.driver
import lean_4_fmt.rename
import lean_4_fmt.emit.tokens
import lean_4_fmt.style.preset

open Lean
open Lean4Fmt

/-- Version of the `lean` in PATH, parsed from `lean --version`
    ("Lean (version 4.31.0, target, commit, Release)"). `none` when no
    `lean` is runnable at all. -/
private
def path_lean_version : IO (Option String) := do
  try
    let out ← IO.Process.run { cmd := "lean", args := #["--version"] }
    match out.trimAscii.copy.splitOn " " |>.dropWhile (fun token => !(token.endsWith "version")) with
    | _ :: version :: _ =>
      return some (if version.endsWith "," then version.dropRight 1 else version)
    | _ => return none
  catch _ => return none

/-- Error text for a PATH `lean` whose version disagrees with the binary. -/
private
def mismatch_msg (version : String) : String :=
  s!"lean4fmt was built against Lean {Lean.versionString}, but the `lean` in PATH reports {version}. "
      ++ "A sysroot taken from it would hold oleans this binary cannot read. "
      ++ s!"Set LEAN_SYSROOT to a Lean {Lean.versionString} toolchain prefix, or run where `lean` is {Lean.versionString}."

/-- Error text when no usable `lean` is found at all. -/
private
def no_lean_msg : String :=
  s!"no `lean` found in PATH and no elan toolchain for Lean {Lean.versionString}. "
      ++ s!"Set LEAN_SYSROOT to a Lean {Lean.versionString} toolchain prefix."

/-- Sysroot resolution that cannot disagree with the binary. `findSysroot`
    asks `lean` in PATH; under elan that shim dispatches on the CALLER'S
    directory (`lean-toolchain`, else the elan default), so a formatter built
    against one toolchain but run inside a project pinned to another reads
    foreign oleans and dies with `incompatible header`. Resolution order:

    1. `LEAN_SYSROOT` — explicit caller control, as with `LEAN_PATH` below.
    2. The elan toolchain matching THIS BINARY's compile-time
       `Lean.versionString` — zero spawns, always names oleans this binary
       can read.
    3. `lean --print-prefix` from PATH, accepted only if `lean --version`
       reports the same version; otherwise a clear error naming both
       versions and the `LEAN_SYSROOT` remedy, instead of the olean header
       failure. -/
private
def find_own_sysroot : IO System.FilePath := do
  if let some root ← IO.getEnv "LEAN_SYSROOT" then
    return ⟨root⟩
  let elanHome ← match ← IO.getEnv "ELAN_HOME" with
  | some explicit => pure explicit
  | none =>
    match ← IO.getEnv "HOME" with
    | some home => pure (home ++ "/.elan")
    | none => pure ""
  if elanHome != "" then
    let own : System.FilePath :=
      ⟨s!"{elanHome}/toolchains/leanprover--lean4---v{Lean.versionString}"⟩
    if (← (own / "bin" / "lean").pathExists) then
      return own
  match ← path_lean_version with
  | some version =>
    if version == Lean.versionString then
      let out ← IO.Process.run { cmd := "lean", args := #["--print-prefix"] }
      return ⟨out.trimAscii.copy⟩
    else
      throw (IO.userError (mismatch_msg version))
  | none => throw (IO.userError no_lean_msg)

unsafe
def init_env_impl : IO Unit := do
  initSearchPath (← find_own_sysroot)
  enableInitializersExecution -- required before importing modules with syntax extensions

@[implemented_by init_env_impl]
opaque init_env : IO Unit

private
def find_lake_root (file : String) : IO (Option System.FilePath) := do
  let path ← try IO.FS.realPath ⟨file⟩ catch _ => pure ⟨file⟩
  let mut directory? := if (← path.isDir) then some path else path.parent
  let mut steps := 0
  while h : directory?.isSome ∧ steps < 64 do
    let directory := directory?.get h.1
    if (← (directory / "lakefile.lean").pathExists)
        || (← (directory / "lakefile.toml").pathExists) then
      return some directory
    directory? := directory.parent
    steps := steps + 1
  return none

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
  for file in files do
    let some root ← find_lake_root file | continue
    if !roots.contains root then roots := roots.push root
  for root in roots do
    try
      let result ← IO.Process.output
        { cmd := "lake", args := #["env", "printenv", "LEAN_PATH"], cwd := root }
      if result.exitCode == 0 then
        let entries := ((result.stdout.splitOn "\n").headD "").splitOn ":"
          |>.filter (fun entry => !entry.isEmpty) |>.map System.FilePath.mk
        if !entries.isEmpty then
          Lean.searchPathRef.modify (· ++ entries)
          Lean4Fmt.Log.log .debug s!"lake env: {root} → {entries.length} search paths"
      else
        Lean4Fmt.Log.log .debug s!"lake env failed at {root} (exit {result.exitCode})"
    catch element =>
      Lean4Fmt.Log.log .debug s!"lake env unavailable at {root}: {element}"

@[implemented_by add_lake_paths_impl]
opaque add_lake_paths (files : List String) : IO Unit

/-- Resolve style, expand inputs (files/dirs) to the file set, and run all jobs
    through the scheduler seam (`Driver.runAll`). Behind an opaque boundary so the
    non-`unsafe` `main` can invoke the unsafe frontend. -/
structure job_config where
  files        : List String
  width        : Option Nat
  preset       : String
  elabFallback : Bool
  retry        : Bool
  logLevel     : String
  lakeEnv      : Bool

unsafe
def run_jobs_impl (cfg : job_config) : IO (Array Driver.result) := do
  let base := (Style.by_name? cfg.preset).getD Style.straylight
  let style :=
    match cfg.width with
    | some width => { base with layout := { base.layout with lineWidth := width } }
    | none       => base
  let expanded ← Driver.expand (cfg.files.toArray.map System.FilePath.mk)
  let retryCfg ← do
    if cfg.retry then
      let exe ← IO.appPath
      pure (some (exe.toString,
        (match cfg.width with | some widthBinding => #["--width", toString widthBinding] | none => #[])
          ++ #["--style", cfg.preset, "--log-level", cfg.logLevel]
          ++ (if cfg.elabFallback then #[] else #["--elab", "off"])
          -- the augmented search path is in-process; the child re-discovers
          -- (or matches an explicit --lake off)
          ++ (if cfg.lakeEnv then #[] else #["--lake", "off"])))
    else pure none
  Driver.run_all style expanded cfg.elabFallback retryCfg

@[implemented_by run_jobs_impl]
opaque run_jobs (cfg : job_config) : IO (Array Driver.result)

private unsafe
def retry_stats
    (exe : System.FilePath)
    (retry : Bool)
    (width : Option Nat)
    (preset : String)
    (path : System.FilePath)
    : IO (Option (Nat × Nat × Nat × Nat)) := do
  if !retry then
    return none
  let result ← IO.Process.output
    {
      cmd := exe.toString
      args := #["--stats", "--no-retry"]
          ++ (
            match width with
            | some width => #["--width", toString width]
            | none       => #[]
          )
          ++ #["--style", preset, path.toString]
    }
  let [active, verbatim, trivia, policy, _] := ((result.stdout.splitOn "\n").headD "").splitOn " "
      | return none
  let (some active, some verbatim, some trivia, some policy) :=
    (active.toNat?, verbatim.toNat?, trivia.toNat?, policy.toNat?)
      | return none
  return some (active, verbatim, trivia, policy)

private unsafe
def fallback_stats_row
    (exe : System.FilePath)
    (retry : Bool)
    (width : Option Nat)
    (preset : String)
    (path : System.FilePath)
    (verbatimBytes : Nat)
    : IO (Nat × Nat × Nat × Nat × String) := do
  let some (active, verbatim, trivia, policy) ← retry_stats exe retry width preset path
    | return (0, verbatimBytes, 0, 0, path.toString)
  return (active, verbatim, trivia, policy, path.toString)

/-- Coverage accounting (`--stats`, doc/design.md §12): per-file
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
    | some width => { base with layout := { base.layout with lineWidth := width } }
    | none       => base
  let expanded ← Driver.expand (files.toArray.map System.FilePath.mk)
  let env ← Frontend.batch_env expanded
  let exe ← IO.appPath
  let mut rows : Array (Nat × Nat × Nat × Nat × String) := #[]
  for path in expanded do
    let contents ← IO.FS.readFile path
    let style ← Driver.style_for style path
    match ← Frontend.stats_for env path.toString contents style elabFallback with
    | some (leftValue, value, trailing, pol) =>
      rows := rows.push (leftValue, value, trailing, pol, path.toString)
    | none =>
      rows := rows.push (← fallback_stats_row exe retry width preset path contents.utf8ByteSize)
  return rows

@[implemented_by run_stats_impl]
opaque run_stats (files : List String) (width : Option Nat) (preset : String) (elabFallback : Bool) (retry : Bool) :
    IO (Array (Nat × Nat × Nat × Nat × String))

-- ── the rename apply (G-L7.1): parse-based, token-aware identifier rewrite ────

/-- The naming axis a declaration node's KIND falls on, or `none` (example, or a
    command that declares no renamable name). -/
def axis_of_kind (keyValue : Lean.Name) : Option Lean4Fmt.Rename.axis :=
  if keyValue == ``Lean.Parser.Command.definition || keyValue == ``Lean.Parser.Command.abbrev
      || keyValue == ``Lean.Parser.Command.opaque
      || keyValue == ``Lean.Parser.Command.instance then
    some .term
  else if keyValue == ``Lean.Parser.Command.theorem || keyValue == ``Lean.Parser.Command.axiom then
    some .thm
  else if keyValue == ``Lean.Parser.Command.structure || keyValue == ``Lean.Parser.Command.inductive then
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
  else some (Rename.last_comp src)

/-- The field names of a structure declaration (first ident of each
    `structSimpleBinder`). Fields are the `terms` axis (schema: "def / abbrev /
    instance / fields"); collecting them lets the plan SEE a type↔field
    collision — a `Lang` type snaking to `lang` when a `lang` field exists must
    be blocked, not applied (the break the floor caught on core/build). -/
partial
def struct_field_names : Lean.Syntax → List String
  | .node _ kind args =>
    let here : List String :=
      if kind == ``Lean.Parser.Command.structSimpleBinder then
        match (Lean4Fmt.Emit.leaf_tokens (.node .none kind args)).find? (·.isIdent) with
        | some identifier => [Rename.last_comp (Lean4Fmt.Emit.bare_src identifier)]
        | none            => []
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
    (
      fun command =>
        if command.getKind == ``Lean.Parser.Command.declaration then
          match command.getArgs.findSome?
              (fun defn => (axis_of_kind defn.getKind).map
                (fun renameAxis => (defn, renameAxis))) with
          | some (defn, axioms) =>
            let head :=
              ((decl_name_of? defn).map (fun name => (name, axioms))).toList
            let fields := if axioms == .typ then (struct_field_names defn).map (·, .term) else []
            head ++ fields
          | none => []
        else
          []
    )

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
    fun (namespaces : List String) (name : String) =>
      String.intercalate "." ((namespaces.filter (· != "")) ++ [name])
  let step :=
    fun (state : List String × List (String × Lean4Fmt.Rename.axis)) (command : Lean.Syntax) =>
      let (namespaces, out) := state
      let kind := command.getKind
      if kind == ``Lean.Parser.Command.namespace then
        (
          namespaces
              ++ [
                (
                  (command.getArgs[1]?).map
                    (fun namespaceNode => (Lean4Fmt.Emit.bare_src namespaceNode).trimAscii.toString)
                ).getD
                  ""
              ],
          out
        )
      else if kind == ``Lean.Parser.Command.section then
        (namespaces ++ [""], out)
      else if kind == ``Lean.Parser.Command.end then
        (namespaces.dropLast, out)
      else if kind == ``Lean.Parser.Command.declaration then
        match command.getArgs.findSome?
            (fun defn => (axis_of_kind defn.getKind).map
              (fun renameAxis => (defn, renameAxis))) with
        | some (defn, axioms) =>
          match decl_full_of? defn with
          | some declName =>
            let full := join namespaces declName
            let fields :=
              if axioms == .typ then
                (struct_field_names defn).map
                  (fun field => (full ++ "." ++ field, Lean4Fmt.Rename.axis.term))
              else
                []
            (namespaces, out ++ [(full, axioms)] ++ fields)
          | none => (namespaces, out)
        | none => (namespaces, out)
      else
        (namespaces, out)
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
  Frontend.apply_farm farmDir
  let paths := files.toArray.map System.FilePath.mk
  let env ← Frontend.batch_env paths
  let out ← IO.getStdout
  let err ← IO.getStderr
  for path in paths do
    let contents ← IO.FS.readFile path
    if resolve then
      -- RESOLVED occurrences `lastComp<TAB>fullName<TAB>D|U` (the hybrid's input),
      -- plus every locally-DEFINED const as `F` def-only (fields/constructors/decls
      -- — the collision+taken guards' input) — BOTH from one elaboration.
      let (occ, locals) ← Frontend.Session.resolve_idents env path.toString contents
      for (_, _, name, isDef) in occ do
        let full := name.toString
        let disposition := if isDef then "D" else "U"
        out.putStrLn s!"{Rename.last_comp full}\t{full}\t{disposition}"
      for name in locals do
        let full := name.toString
        out.putStrLn s!"{Rename.last_comp full}\t{full}\tF"
    else
      match ← Frontend.parse_full? env path.toString contents elabFallback with
      | some stx =>
        for (name, isAxiom) in decls_of stx do
          out.putStrLn s!"{name}\t{axis_tag isAxiom}"
      | none => err.putStrLn s!"rename-decls: SKIP (no parse) {path}"

@[implemented_by run_rename_decls_impl]
opaque run_rename_decls (files : List String) (resolve : Bool) (farmDir : Option String) (elabFallback : Bool) : IO Unit

private
def rewrite_parsed
    (err : IO.FS.Stream)
    (contents : String)
    (map : List (String × String))
    (path : System.FilePath)
    (stx : Lean.Syntax)
    : IO Unit := do
  let idents := (Lean4Fmt.Emit.leaf_tokens stx).filter (·.isIdent)
  let mut edits : Array (Nat × Nat × String) := #[]
  for ident in idents do
    let some substring := ident.getSubstring? false false | continue
    let some replacement := Lean4Fmt.Rename.ident_replacement map substring.toString | continue
    edits := edits.push (substring.startPos.byteIdx, substring.stopPos.byteIdx, replacement)
  if edits.isEmpty then
    return
  -- Apply larger offsets first to preserve every remaining byte position.
  let sorted := edits.qsort (fun left right => left.1 > right.1)
  let mut bytes := contents.toUTF8
  for (start, stop, replacement) in sorted do
    bytes := (bytes.extract 0 start) ++ replacement.toUTF8 ++ (bytes.extract stop bytes.size)
  IO.FS.writeFile path (String.fromUTF8! bytes)
  err.putStrLn s!"rewrite: {path} ({edits.size} idents)"

/-- Token-aware rewrite of one parsed module by a precomputed map: splice only
    the `.ident` leaves whose text moves, end-to-start over the UTF-8 bytes
    (strings/comments/docstrings are never leaf idents, so they ride byte-exact). -/
unsafe
def rewrite_file
    (env : Lean.Environment)
    (map : List (String × String))
    (elabFallback : Bool)
    (predicate : System.FilePath)
    : IO Unit := do
  let err ← IO.getStderr
  let contents ← IO.FS.readFile predicate
  match ← Frontend.parse_full? env predicate.toString contents elabFallback with
  | none => err.putStrLn s!"rename-rewrite: SKIP (no parse) {predicate}"
  | some stx => rewrite_parsed err contents map predicate stx

private unsafe
def rewrite_from_map (files : List String) (mapFile : String) (elabFallback : Bool) : IO Unit := do
  let mapText ← IO.FS.readFile ⟨mapFile⟩
  let map : List (String × String) := mapText.splitOn "\n" |>.filterMap fun line =>
    match line.splitOn "\t" with
    | [source, target] => if source.isEmpty then none else some (source, target)
    | _ => none
  let paths := files.toArray.map System.FilePath.mk
  let env ← Frontend.batch_env paths
  -- The resolved plan is already filtered; the token pass also catches binder types.
  for path in paths do
    rewrite_file env map elabFallback path

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
  Frontend.apply_farm farmDir
  let err ← IO.getStderr
  match mapFile with
  | none => err.putStrLn "rename-rewrite: --map <file> required"
  | some mapFile => rewrite_from_map files mapFile elabFallback

@[implemented_by run_rename_rewrite_impl]
opaque run_rename_rewrite (files : List String) (mapFile : Option String) (resolve : Bool) (farmDir : Option String) (elabFallback : Bool) : IO Unit

/-- G-L7.4 probe (`--resolve-dump`): elaborate the file(s) and print each resolved
    ident occurrence as `start-stop<TAB>fullName`. Validates that the InfoTree
    disambiguation works before the token map is swapped for it. -/
unsafe
def run_resolve_dump_impl (files : List String) : IO Unit := do
  let paths := files.toArray.map System.FilePath.mk
  Frontend.apply_farm (← Frontend.make_olean_farm files)
  let env ← Frontend.batch_env paths
  let out ← IO.getStdout
  for path in paths do
    let contents ← IO.FS.readFile path
    let (occ, _) ← Frontend.Session.resolve_idents env path.toString contents
    for (startOffset, endOffset, name, isDef) in occ do
      let tag := if isDef then "DEF" else "use"
      out.putStrLn s!"{startOffset}-{endOffset}\t{name}\t{tag}"

@[implemented_by run_resolve_dump_impl]
opaque run_resolve_dump (files : List String) : IO Unit

private
structure rename_worker_context where
  err     : IO.FS.Stream
  exe     : String
  paths   : Array System.FilePath
  jobs    : Nat
  resolve : Bool
  extra   : Array String
  protect : List String

private
structure rename_discovery where
  allDecls : List (String × Lean4Fmt.Rename.axis) := []
  occs     : List (String × String) := []
  defs     : List String := []
  existing : List String := []
  idx      : Nat := 0

private
structure rename_rewrite_stats where
  renamed : Nat := 0
  skips   : Nat := 0
  idx     : Nat := 0

private
def spawnRenameCollect
    (context : rename_worker_context)
    (path : System.FilePath)
    : IO (IO.Process.Child ⟨.null, .piped, .piped⟩) :=
  IO.Process.spawn
    { cmd    := context.exe,
      args   := #["--rename-decls", "--no-retry"] ++ context.extra ++ #[path.toString],
      stdin  := .null,
      stdout := .piped,
      stderr := .piped }

private
def collectRenameLine
    (resolve : Bool)
    (state : rename_discovery)
    (line : String)
    : rename_discovery :=
  if resolve then
    match line.splitOn "\t" with
    | [lastComponent, fullName, disposition] =>
      if disposition == "F" then
        { state with existing := state.existing ++ [fullName] }
      else
        { state with
          occs := state.occs ++ [(lastComponent, fullName)]
          defs := if disposition == "D" then state.defs ++ [fullName] else state.defs
        }
    | _ => state
  else
    match line.splitOn "\t" with
    | [name, tag] =>
      match axis_of_tag tag with
      | some axis => { state with allDecls := state.allDecls ++ [(name, axis)] }
      | none      => state
    | _ => state

private
def collectRenameChild
    (resolve : Bool)
    (initial : rename_discovery)
    (child : IO.Process.Child ⟨.null, .piped, .piped⟩)
    : IO rename_discovery := do
  let output ← child.stdout.readToEnd
  let _ ← child.stderr.readToEnd
  let _ ← child.wait
  return output.splitOn "\n" |>.foldl (collectRenameLine resolve) initial

private
def collectRenameDeclarations (context : rename_worker_context) : IO rename_discovery := do
  let mut state : rename_discovery := {}
  while state.idx < context.paths.size do
    let wave :=
      context.paths.extract state.idx (Nat.min (state.idx + context.jobs) context.paths.size)
    let mut children : Array (IO.Process.Child ⟨.null, .piped, .piped⟩) := #[]
    for path in wave do
      children := children.push (← spawnRenameCollect context path)
    for child in children do
      state ← collectRenameChild context.resolve state child
    state := { state with idx := state.idx + context.jobs }
  return state

private
def collectProtectedNames (context : rename_worker_context) : IO (List String) := do
  if !context.resolve then
    return []
  let mut protectedNames : List String := []
  for protectedPath in context.protect do
    let child ← spawnRenameCollect context (System.FilePath.mk protectedPath)
    let output ← child.stdout.readToEnd
    let _ ← child.stderr.readToEnd
    let _ ← child.wait
    for line in output.splitOn "\n" do
      match line.splitOn "\t" with
      | [_, fullName, _] => protectedNames := protectedNames ++ [fullName]
      | _ => pure ()
  if !context.protect.isEmpty then
    context.err.putStrLn
      s!"// protecting {protectedNames.eraseDups.length} names from {context.protect.length} closure file(s)"
  return protectedNames

private
def spawnRenameRewrite
    (context : rename_worker_context)
    (mapPath : String)
    (path : System.FilePath)
    : IO (IO.Process.Child ⟨.null, .piped, .piped⟩) :=
  IO.Process.spawn
    { cmd := context.exe,
      args := #["--rename-rewrite", "--map", mapPath, "--no-retry"] ++ context.extra
          ++ #[path.toString],
      stdin := .null,
      stdout := .piped,
      stderr := .piped }

private
def collectRewriteLine
    (err : IO.FS.Stream)
    (state : rename_rewrite_stats)
    (line : String)
    : IO rename_rewrite_stats := do
  if line.startsWith "rewrite: " then
    err.putStrLn s!"//   {line}"
    return { state with renamed := state.renamed + 1 }
  if line.startsWith "rename-rewrite: SKIP" then
    err.putStrLn s!"//   {line}"
    return { state with skips := state.skips + 1 }
  return state

private
def collectRewriteChild
    (err : IO.FS.Stream)
    (initial : rename_rewrite_stats)
    (child : IO.Process.Child ⟨.null, .piped, .piped⟩)
    : IO rename_rewrite_stats := do
  let _ ← child.stdout.readToEnd
  let errors ← child.stderr.readToEnd
  let _ ← child.wait
  let mut state := initial
  for line in errors.splitOn "\n" do
    state ← collectRewriteLine err state line
  return state

private
def rewriteRenameFiles
    (context : rename_worker_context)
    (mapPath : String)
    : IO rename_rewrite_stats := do
  let mut state : rename_rewrite_stats := {}
  while state.idx < context.paths.size do
    let wave :=
      context.paths.extract state.idx (Nat.min (state.idx + context.jobs) context.paths.size)
    let mut children : Array (IO.Process.Child ⟨.null, .piped, .piped⟩) := #[]
    for path in wave do
      children := children.push (← spawnRenameRewrite context mapPath path)
    for child in children do
      state ← collectRewriteChild context.err state child
    state := { state with idx := state.idx + context.jobs }
  return state

private
def reportRenamePlan
    (err : IO.FS.Stream)
    (tag : String)
    (fileCount : Nat)
    (renames skipped : List (String × String))
    : IO Unit := do
  err.putStrLn
    s!"// rename apply ({tag}): {renames.length} renames, {skipped.length} skipped over {fileCount} files"
  for (name, target) in skipped do
    err.putStrLn s!"//   SKIP {name} → {target}"

private
def writeRenameMap (renames : List (String × String)) : IO String := do
  let mapPath := s!"{((← IO.getEnv "TMPDIR").getD "/tmp")}/lean4fmt-rename.map"
  IO.FS.writeFile
    ⟨mapPath⟩
    (String.intercalate "\n" (renames.map (fun (source, target) => s!"{source}\t{target}")))
  return mapPath

private
def enforceRewriteConsistency
    (err : IO.FS.Stream)
    (resolve : Bool)
    (stats : rename_rewrite_stats)
    : IO Unit := do
  if resolve && stats.skips > 0 then
    err.putStrLn
      s!"// ABORT: {stats.skips} file(s) failed to rewrite in pass 2 — rename is INCONSISTENT; revert the set"
    IO.Process.exit 1

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
    (targetCase : Lean4Fmt.Casing.Case)
    (resolve : Bool)
    (elabFallback : Bool)
    (protect : List String)
    : IO Unit := do
  let err ← IO.getStderr
  let exe := (← IO.appPath).toString
  let paths := files.toArray.map System.FilePath.mk
  let naming := ((Lean4Fmt.Style.by_name? preset).getD Lean4Fmt.Style.straylight).naming
  let modules := files.filterMap (fun file => (System.FilePath.mk file).fileStem)
  let jobs := (((← IO.getEnv "LEAN4FMT_JOBS").bind (·.toNat?)).getD 8).max 1
  -- resolution: build the olean farm ONCE (over the whole set incl. protected
  -- files, so they resolve), hand each worker its path via --farm
  let farm ← if resolve then Frontend.make_olean_farm (files ++ protect)
  else pure none
  let extra :=
    (if elabFallback then #[] else #["--elab", "off"])
        ++ (
          if resolve then
            #["--resolve", "--lake", "off"]
                ++ (
                  match farm with
                  | some filePath => #["--farm", filePath]
                  | none          => #[]
                )
          else
            #[]
        )
  let context : rename_worker_context := { err, exe, paths, jobs, resolve, extra, protect }
  let discovery ← collectRenameDeclarations context
  let protectedFulls ← collectProtectedNames context
  -- the plan: HYBRID under --resolve (resolution decides, token acts), else token
  let (renames, skipped) :=
    if resolve then
      Lean4Fmt.Rename.plan_hybrid
        targetCase
        modules
        discovery.occs
        discovery.defs
        discovery.existing
        protectedFulls
    else
      let plan := Lean4Fmt.Rename.build_plan naming modules discovery.allDecls
      (plan.renames, plan.skipped)
  let tag := if resolve then s!"resolve/{repr targetCase}" else preset
  reportRenamePlan err tag paths.size renames skipped
  if renames.isEmpty then
    return
  let mapPath ← writeRenameMap renames
  let rewriteStats ← rewriteRenameFiles context mapPath
  err.putStrLn s!"// rewrote {rewriteStats.renamed} files"
  -- G-L7.4g pass-2 consistency: pass 1 RESOLVED every file (it elaborated). A
  -- pass-2 SKIP means a file could not be rewritten while its DEPS were — a
  -- half-rename. Exit nonzero so the driver reverts the whole set, rather than
  -- leaning on the next build to notice. (core/build hits 0 skips; this is the
  -- fail-safe for the rollout.)
  enforceRewriteConsistency err resolve rewriteStats

@[implemented_by run_rename_apply_impl]
opaque run_rename_apply (files : List String) (preset : String) (targetCase : Lean4Fmt.Casing.Case) (resolve : Bool) (elabFallback : Bool) (protect : List String) :
    IO Unit

private
def severity_name : Lean4Fmt.Rules.severity → String
  | .debug   => "debug"
  | .info    => "info"
  | .warning => "warning"
  | .error   => "error"

private
def diagnostic_json (diagnostic : Lean4Fmt.Rules.Diagnostic) : Lean.Json :=
  Lean.Json.mkObj
    [
      ("severity", .str (severity_name diagnostic.severity)),
      ("pos", Lean.toJson diagnostic.pos),
      ("rule", .str diagnostic.rule),
      ("role", .str diagnostic.role),
      ("message", .str diagnostic.message)
    ]

private
def result_json (result : Lean4Fmt.Driver.result) : Lean.Json :=
  Lean.Json.mkObj
    [
      ("path", .str result.path.toString),
      ("changed", Lean.toJson result.changed),
      ("diagnostics", .arr (result.diagnostics.map diagnostic_json))
    ]

private
def parse_rename_decl (line : String) : Option (String × Lean4Fmt.Rename.axis) := do
  let [name, axis] := (line.trimAscii.toString.splitOn " ").filter (· ≠ "") | none
  let axis ← axis_of_tag axis
  return (name, axis)

private
def run_rename_plan_mode (options : Cli.Options) : IO Unit := do
  let naming := ((Lean4Fmt.Style.by_name? options.preset).getD Lean4Fmt.Style.straylight).naming
  let input ← (← IO.getStdin).readToEnd
  let plan :=
    Lean4Fmt.Rename.build_plan naming [] (input.splitOn "\n" |>.filterMap parse_rename_decl)
  IO.println
    s!"// rename plan (preset {options.preset}): {plan.renames.length} rename, {plan.skipped.length} skip"
  for (name, target) in plan.renames do
    IO.println s!"  {name} → {target}"
  for (name, target) in plan.skipped do
    IO.println s!"  SKIP {name} → {target}"

private
def coverage_pct (numerator denominator : Nat) : String :=
  if denominator == 0 then
    "-"
  else
    s!"{(numerator * 1000 / denominator) / 10}.{(numerator * 1000 / denominator) % 10}%"

private
def run_stats_mode (options : Cli.Options) : IO Unit := do
  let rows ← run_stats options.files options.width options.preset options.elabFallback options.retry
  for row in rows do
    let (active, verbatim, trivia, policy, path) := row
    IO.println s!"{active} {verbatim} {trivia} {policy} {path}"
  let totals :=
    rows.foldl
      (
        fun (active, verbatim, trivia, policy) row =>
          (active + row.1, verbatim + row.2.1, trivia + row.2.2.1, policy + row.2.2.2.1)
      )
      (0, 0, 0, 0)
  let (active, verbatim, trivia, policy) := totals
  let code := active + verbatim
  let portable := code - Nat.min policy code
  IO.println
    s!"// files {rows.size}  bytes active={active} verbatim={verbatim} trivia={trivia} policy={policy}"
  IO.println
    s!"// coverage: code-active {coverage_pct active code}  (of all output: active {coverage_pct active (code + trivia)}, trivia {coverage_pct trivia (code + trivia)})"
  IO.println
    s!"// ceiling: portable {coverage_pct portable code} of code; active-of-portable {coverage_pct active portable}"

private
def run_special_mode (options : Cli.Options) : IO Bool :=
  match options.mode with
  | .renamePlan => run_rename_plan_mode options *> pure true
  | .renameApply => do
    let some targetCase := Lean4Fmt.Casing.Case.of_string? options.renameCase
        | do
          (← IO.getStderr).putStrLn
            s!"invalid --rename-case `{options.renameCase}`; expected snake|camel|upperCamel|preserve"
          IO.Process.exit 2
    run_rename_apply
      options.files
      options.preset
      targetCase
      options.resolve
      options.elabFallback
      options.protect
    pure true
  | .renameDecls =>
    run_rename_decls options.files options.resolve options.farmDir options.elabFallback *> pure true
  | .renameRewrite =>
    run_rename_rewrite
      options.files
      options.mapFile
      options.resolve
      options.farmDir
      options.elabFallback
        *> pure true
  | .resolveDump => run_resolve_dump options.files *> pure true
  | .stats => run_stats_mode options *> pure true
  | _ => pure false

private
def emit_result
    (options : Cli.Options)
    (err : IO.FS.Stream)
    (result : Driver.result)
    : IO Bool := do
  if options.mode == .lint && options.json then
    IO.println (Lean.Json.compress (result_json result))
    return result.diagnostics.any (·.severity == .error)
  let mut failed := false
  for diagnostic in result.diagnostics do
    let level : Lean4Fmt.Log.level :=
      match diagnostic.severity with
      | .debug   => .debug
      | .info    => .info
      | .warning => .warn
      | .error   => .error
    Lean4Fmt.Log.log level s!"{result.path}:{diagnostic.render}"
    if diagnostic.severity == .error then failed := true
  match options.mode with
  | .format => IO.print result.output
  | .check =>
    if result.changed then
      err.putStrLn s!"Would reformat: {result.path}"
      failed := true
    else err.putStrLn s!"OK: {result.path}"
  | .write =>
    if result.changed then
      IO.FS.writeFile result.path result.output
      err.putStrLn s!"Formatted: {result.path}"
    else err.putStrLn s!"Unchanged: {result.path}"
  | _ => pure ()
  return failed

def main (argv : List String) : IO Unit := do
  let options := Cli.parse argv
  if options.mode != .renamePlan && options.files.isEmpty then
    (← IO.getStderr).putStrLn Cli.usage
    IO.Process.exit 1
  init_env
  Lean4Fmt.Log.set_level (Lean4Fmt.Log.level.of_string options.logLevel)
  if options.mode == .lint && options.json then Lean4Fmt.Log.set_level .error
  else if options.mode == .lint && options.logLevel == "warn" then Lean4Fmt.Log.set_level .info
  if options.lakeEnv then add_lake_paths options.files
  if ← run_special_mode options then
    return
  let results ← run_jobs
    {
      files := options.files
      width := options.width
      preset := options.preset
      elabFallback := options.elabFallback
      retry := options.retry
      logLevel := options.logLevel
      lakeEnv := options.lakeEnv
    }
  let err ← IO.getStderr
  let failures ← results.mapM (emit_result options err)
  if failures.any id then IO.Process.exit 1
