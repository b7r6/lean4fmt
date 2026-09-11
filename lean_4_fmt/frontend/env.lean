/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // LEAN4FMT // FRONTEND // ENV
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The batch environment (doc/design.md §4/§11, superset-env strategy): ONE import per
    invocation, shared by every job. Imported olean regions are compacted and
    persistent — immutable by construction — so the env is freeze-free and (later)
    thread-share-safe; per-file syntax extensions layer on top functionally
    (`Session`), invisible to other jobs.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import lean_4_fmt.frontend.gate
import lean_4_fmt.log

namespace Lean4Fmt.Frontend

open Lean

/-- The imports of one file's header (`#[]` when the file is unreadable or the
    header doesn't parse — the caller's job will diagnose). Header parsing is
    cheap text work; no environment is needed. -/
unsafe
def file_imports (path : System.FilePath) : IO (Array Import) := do
  try
    let contents ← IO.FS.readFile path
    let ictx := Parser.mkInputContext contents path.toString
    let (hdr, _, _) ← Parser.parseHeader ictx
    pure (Elab.headerToImports hdr)
  catch _ => pure #[]

/-- Import an environment for exactly these imports, dropping modules the search
    path can't resolve (their files fail to parse and skip with the loud
    diagnostic). `loadExts` is what registers imported parser extensions
    (notation/macros) — without it nothing nontrivial parses; `leakEnv` skips
    end-of-process teardown of a region that lives for the whole invocation
    anyway. -/
unsafe
def imports_env (imports : Array Import) : IO Environment := do
  let mut seen : NameSet := {}
  let mut resolved : Array Import := #[]
  for imp in imports do
    if !seen.contains imp.module then
      seen := seen.insert imp.module
      let ok ←
        try
          let olean ← findOLean imp.module
          olean.pathExists
        catch _ => pure false
      if ok then resolved := resolved.push imp
  importModules resolved {} (trustLevel := 1024) (leakEnv := true) (loadExts := true)

/-- A stable cache key for an import set (sorted, deduped module names). -/
def imports_key (imports : Array Import) : String :=
  String.intercalate ";" (((imports.map (·.module.toString)).qsort (· < ·)).toList)

private
def syntax_stats (style : Lean4Fmt.Style.Style) (stx : Lean.Syntax) : Nat × Nat × Nat × Nat :=
  let (doc, _) := Lean4Fmt.Emit.run style stx.updateLeading
  let (active, verbatim, trivia) := Lean4Fmt.Doc.stats doc
  (active, verbatim, trivia, Lean4Fmt.Syntax.policy_content_bytes stx)

/-- One environment for a whole batch: union every file's header imports and
    import ONCE per invocation. Parsing a file against a SUPERSET env is safe for
    the gate's guarantees — source and output are token-compared under the SAME
    env, and the kept output is token-identical to the input — but it is not
    always POSSIBLE: co-imported syntax extensions can conflict (two DSLs'
    notations colliding), making a file unparseable under the union that parses
    fine under its own imports. The driver handles that with a retry against the
    file's own import set (`importsEnv`, cached by `importsKey`), so the union
    stays the fast path and conflicts cost only their own files. -/
unsafe
def batch_env (paths : Array System.FilePath) : IO Environment := do
  let mut all : Array Import := #[]
  for path in paths do
    all := all ++ (← file_imports path)
  imports_env all

/-- Prepend a prebuilt farm dir to the search path. Built ONCE per invocation and
    shared (in-process, or handed to a worker via `--farm`), so no rebuild. -/
def apply_farm (farm : Option String) : IO Unit :=
  match farm with
  | some filePath =>
    Lean.searchPathRef.modify (fun searchPath => (⟨filePath⟩ : System.FilePath) :: searchPath)
  | none => pure ()

private
structure root_search_state where
  directory : Option System.FilePath
  root      : Option System.FilePath := none
  steps     : Nat := 0

/-- The module symbol table: a MERGED SYMLINK FARM of every package's built
    oleans, put FIRST on the search path — the correct multi-workspace resolution
    that both the rename and (the zero-config) formatting want. `findOLean`
    resolves a module by its ROOT namespace (`Continuity`) to the first search dir
    that has that root, and does NOT check the full olean exists — so a multi-dir
    path can't disambiguate a root split across packages (codec's `Continuity/`
    wins for `Continuity.Trust.Discharge`, whose olean it doesn't own →
    `imports_env` silently drops it, and the parse batch threw on Box). Merging all
    lib dirs into ONE `Continuity/` root (`cp -rsn` recursive symlinks — the trick
    corpus-gate.sh / lean4fmt.sh use) makes every module resolve to its true owner.
    Repo root = nearest `.git` ancestor of the first input. -/
unsafe
def make_olean_farm (files : List String) : IO (Option String) := do
  let some f0 := files.head? | return none
  let p0 ← try IO.FS.realPath ⟨f0⟩ catch _ => pure ⟨f0⟩
  let mut search : root_search_state := { directory := p0.parent }
  while h : search.directory.isSome ∧ search.steps < 64 do
    let dir := search.directory.get h.1
    if ← (dir / ".git").pathExists then
      search := { search with root := some dir, directory := none }
    else search := { search with directory := dir.parent }
    search := { search with steps := search.steps + 1 }
  let some root := search.root | return none
  let dirs ← try
      let result ← IO.Process.output
        { cmd := "find",
          args := #[root.toString, "-type", "d", "-path", "*/.lake/build/lib/lean", "-prune"] }
      pure ((result.stdout.splitOn "\n").filter (fun line => !line.isEmpty))
    catch _ => pure ([] : List String)
  if dirs.isEmpty then
    return none
  let farm := (← IO.Process.run { cmd := "mktemp", args := #["-d"] }).trim
  for directory in dirs do
    try let _ ← IO.Process.output { cmd := "cp", args := #["-rsn", s!"{directory}/.", s!"{farm}/"] }
    catch _ => pure ()
  Lean4Fmt.Log.log .debug s!"olean farm: {farm} ({dirs.length} lib dirs merged)"
  return some farm

/-- Coverage stats for one file under `env` (doc/design.md §12): the
    active/verbatim/trivia byte attribution of its produced doc plus the
    CONTENT-BY-POLICY bytes (moduleDoc/header/quotation commands — permanently
    verbatim, so `verbatim - policy` is the honest porting tail), or `none`
    when the file doesn't parse under this env (caller decides: count it fully
    verbatim, or retry under the file's own env in a subprocess). -/
unsafe
def stats_for
    (env : Environment)
    (path contents : String)
    (style : Lean4Fmt.Style.Style)
    (elabFallback : Bool := true)
    : IO (Option (Nat × Nat × Nat × Nat)) := do
  match ← parse_full? env path contents elabFallback with
  | none => pure none
  | some stx => pure (some (syntax_stats style stx))

end Lean4Fmt.Frontend
