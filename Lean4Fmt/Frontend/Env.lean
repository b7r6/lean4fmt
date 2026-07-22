/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // LEAN4FMT // FRONTEND // ENV
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The batch environment (DESIGN_V2 §12, superset-env strategy): ONE import per
    invocation, shared by every job. Imported olean regions are compacted and
    persistent — immutable by construction — so the env is freeze-free and (later)
    thread-share-safe; per-file syntax extensions layer on top functionally
    (`Session`), invisible to other jobs.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import Lean4Fmt.Frontend.Gate

namespace Lean4Fmt.Frontend

open Lean

/-- The imports of one file's header (`#[]` when the file is unreadable or the
    header doesn't parse — the caller's job will diagnose). Header parsing is
    cheap text work; no environment is needed. -/
unsafe def fileImports
           (path : System.FilePath)
           : IO (Array Import) := do

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
unsafe def importsEnv
           (imports : Array Import)
           : IO Environment := do

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
def importsKey
    (imports : Array Import)
    : String :=

  String.intercalate ";" (((imports.map (·.module.toString)).qsort (· < ·)).toList)

/-- One environment for a whole batch: union every file's header imports and
    import ONCE per invocation. Parsing a file against a SUPERSET env is safe for
    the gate's guarantees — source and output are token-compared under the SAME
    env, and the kept output is token-identical to the input — but it is not
    always POSSIBLE: co-imported syntax extensions can conflict (two DSLs'
    notations colliding), making a file unparseable under the union that parses
    fine under its own imports. The driver handles that with a retry against the
    file's own import set (`importsEnv`, cached by `importsKey`), so the union
    stays the fast path and conflicts cost only their own files. -/
unsafe def batchEnv
           (paths : Array System.FilePath)
           : IO Environment := do

  let mut all : Array Import := #[]
  for p in paths do
    all := all ++ (← fileImports p)
  importsEnv all

/-- Coverage stats for one file under `env` (DESIGN_V2 §15): the
    active/verbatim/trivia byte attribution of its produced doc, or `none` when
    the file doesn't parse under this env (caller decides: count it fully
    verbatim, or retry under the file's own env in a subprocess). -/
unsafe def statsFor
           (env : Environment)
           (path contents : String)
           (style : Lean4Fmt.Style.Style)
           (elabFallback : Bool := true)
           : IO (Option (Nat × Nat × Nat)) := do

  match ← parseFull? env path contents elabFallback with
  | none => pure none
  | some stx =>
    let (doc, _) := Lean4Fmt.Emit.run style stx.updateLeading
    pure (some (Lean4Fmt.Doc.stats doc))

end Lean4Fmt.Frontend
