/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                         // LEAN4FMT // DRIVER // JOB
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The scheduling seam. A `Job` is a shared-nothing unit of work — one file,
    read → parse → lint → format → gate → `Result` — that touches no mutable
    global state beyond the one-time process init. `runJob` is the CPU-heavy stage
    (parsing and, later, elaboration in Frontend.Session); `runAll` is the ONE
    place that decides HOW those units run.

    Today `runAll` maps sequentially. Because a job is shared-nothing and the
    formatting core (Emit → Doc → Render) is pure, the parallel future — a
    core-pinned worker pool (Driver.Pool) or a batched io_uring loop (Driver.Io) —
    slots in here alone, without touching the core or `runJob`. That is the whole
    point of this boundary: go multicore/uring later without thrashing the rest.

    `expand` turns file/dir inputs into the deterministic file set (a directory is
    walked — the "format the tree / project" entry, ahead of a lakefile-aware
    module enumerator).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Frontend
import Lean4Fmt.Driver.Walk
import Lean4Fmt.Style
import Lean4Fmt.Rules

namespace Lean4Fmt.Driver

open Lean4Fmt

/-- The outcome of one job: the gated output, the original (for change/check), and
    the lint diagnostics. `output` is guaranteed never worse than `original` (the
    gate falls back to identity), so downstream modes are trivial. -/
structure Result where
  path        : System.FilePath
  original    : String
  output      : String
  diagnostics : Array Rules.Diagnostic := #[]
  deriving Inhabited

/-- Whether formatting would change the file. -/
def Result.changed (r : Result) : Bool := r.output != r.original

/-- The shared-nothing per-file work unit (read → parse → lint → format → gate).
    Self-contained: everything it needs is its arguments and the filesystem read;
    it returns a value. Catches its own errors (falling back to identity output +
    an error diagnostic) so a batch never aborts — this is what a worker pool
    dispatches. -/
unsafe def runJob
           (env : Lean.Environment)
           (style : Style.Style)
           (path : System.FilePath)
           (elabFallback : Bool := true)
           (retry : Option (String × Array String) := none)
           : IO Result := do
  let original ← IO.FS.readFile path
  try
    let (output, diagnostics) ←
      Frontend.formatSafe env path.toString original style elabFallback
    -- Retry ladder: a parse failure under the shared SUPERSET env can be a
    -- syntax-extension conflict between co-imported DSLs, not a broken file.
    -- The runtime's import model is one-shot (ImportingFlag: the first
    -- `importModules` disables initializer execution for the process), so a
    -- second in-process `loadExts` import is off the table — the retry is a
    -- SUBPROCESS: this exe, one file, its own env (`--no-retry` stops
    -- recursion; a genuinely broken file fails there too and keeps its loud
    -- diagnostic via stderr).
    if output == original && diagnostics.any (·.rule == "parse") then
      if let some (exe, extraArgs) := retry then
        let r ← IO.Process.output
          { cmd := exe, args := #["--no-retry"] ++ extraArgs ++ #[path.toString] }
        if r.exitCode == 0 && !r.stdout.isEmpty then
          let stillUnparsed := (r.stderr.splitOn "not formatted:").length > 1
          return { path, original, output := r.stdout,
                   diagnostics := if stillUnparsed then diagnostics else #[] }
    return { path, original, output, diagnostics }
  catch e =>
    return { path, original, output := original,
             diagnostics := #[{ severity := .error, rule := "io", message := toString e }] }

/-- The scheduler seam. SEQUENTIAL today — the single place a core-pinned worker
    pool (Driver.Pool) or batched uring loop (Driver.Io) will slot in, leaving the
    pure core and `runJob` untouched. Every job shares ONE batch env
    (`Frontend.batchEnv` — imported once per invocation, immutable thereafter);
    per-file syntax extensions layer on top functionally inside `Session`, and
    superset-conflicted files retry in a one-file subprocess. -/
unsafe def runAll
           (style : Style.Style)
           (paths : Array System.FilePath)
           (elabFallback : Bool := true)
           (retry : Option (String × Array String) := none)
           : IO (Array Result) := do
  let env ← Frontend.batchEnv paths
  paths.mapM (runJob env style · elabFallback retry)

/-- Expand file/dir inputs into the `.lean` file set to process (directories are
    walked, `.lake` build trees skipped), deduplicated and in a deterministic
    (sorted) order so runs are reproducible. -/
def expand
    (inputs : Array System.FilePath)
    : IO (Array System.FilePath) := do
  let mut acc : Array System.FilePath := #[]
  for p in inputs do
    if ← p.isDir then acc := acc ++ (← findLean p)
    else acc := acc.push p
  let sorted := acc.qsort (fun a b => a.toString < b.toString)
  -- dedup (adjacent, since sorted)
  let mut out : Array System.FilePath := #[]
  for p in sorted do
    if out.back?.map (· == p) != some true then out := out.push p
  return out

end Lean4Fmt.Driver
