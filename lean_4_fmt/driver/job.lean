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

import lean_4_fmt.frontend
import lean_4_fmt.driver.walk
import lean_4_fmt.style
import lean_4_fmt.driver.config
import lean_4_fmt.rules

namespace Lean4Fmt.Driver

open Lean4Fmt

/-- The outcome of one job: the gated output, the original (for change/check), and
    the lint diagnostics. `output` is guaranteed never worse than `original` (the
    gate falls back to identity), so downstream modes are trivial. -/
structure result where
  path        : System.FilePath
  original    : String
  output      : String
  diagnostics : Array Rules.Diagnostic := #[]
  deriving Inhabited

/-- Whether formatting would change the file. -/
def result.changed (jobResult : result) : Bool := jobResult.output != jobResult.original

/-- The shared-nothing per-file work unit (read → parse → lint → format → gate).
    Self-contained: everything it needs is its arguments and the filesystem read;
    it returns a value. Catches its own errors (falling back to identity output +
    an error diagnostic) so a batch never aborts — this is what a worker pool
    dispatches. -/
unsafe
def run_job
    (env : Lean.Environment)
    (style : Style.Style)
    (path : System.FilePath)
    (elabFallback : Bool := true)
    (retry : Option (String × Array String) := none)
    : IO result := do
  let original ← IO.FS.readFile path
  try
    -- per-file config: `style` is the CLI base; fmt.lean chain overrides
    let style ← style_for style path
    let (output, diagnostics) ←
      Frontend.format_safe env path.toString original style elabFallback
    -- Retry ladder: a parse failure under the shared SUPERSET env can be a
    -- syntax-extension conflict between co-imported DSLs, not a broken file.
    -- The runtime's import model is one-shot (ImportingFlag: the first
    -- `importModules` disables initializer execution for the process), so a
    -- second in-process `loadExts` import is off the table — the retry is a
    -- SUBPROCESS: this exe, one file, its own env (`--no-retry` stops
    -- recursion; a genuinely broken file fails there too and keeps its loud
    -- diagnostic via stderr).
    let _ := retry   -- retries are batched by runAll (waves), not per-job
    return { path, original, output, diagnostics }
  catch element =>
    return { path, original, output := original,
             diagnostics := #[{ severity := .error, rule := "io", message := toString element }] }

/-- Whether a result is a candidate for the subprocess retry: unchanged output
    with a parse diagnostic (a superset-env conflict, an own-notation file the
    union could not help, or a genuinely broken file — the retry sorts them). -/
private
def result.retryable (jobResult : result) : Bool :=
  jobResult.output == jobResult.original && jobResult.diagnostics.any (·.rule == "parse")

private
structure retry_state where
  results  : Array result
  cursor   : Nat := 0
  children : Array (IO.Process.Child ⟨.null, .piped, .piped⟩) := #[]

/-- Retry parse-conflicted jobs as bounded waves of isolated processes. -/
private unsafe
def run_retries
    (initialResults : Array result)
    (exe : String)
    (extraArgs : Array String)
    : IO (Array result) := do
  let conflicted :=
    (Array.range initialResults.size).filter (fun idx => initialResults[idx]!.retryable)
  if conflicted.isEmpty then
    return initialResults
  let jobs := (((← IO.getEnv "LEAN4FMT_JOBS").bind (·.toNat?)).getD 8).max 1
  let spawnRetry (path : System.FilePath) : IO (IO.Process.Child ⟨.null, .piped, .piped⟩) :=
    IO.Process.spawn
      { cmd    := exe,
        args   := #["--no-retry"] ++ extraArgs ++ #[path.toString],
        stdin  := .null,
        stdout := .piped,
        stderr := .piped }
  let mut state : retry_state := { results := initialResults }
  while state.cursor < conflicted.size do
    let wave := conflicted.extract state.cursor (Nat.min (state.cursor + jobs) conflicted.size)
    state := { state with children := #[] }
    for resultIndex in wave do
      state :=
        { state with
          children := state.children.push (← spawnRetry state.results[resultIndex]!.path) }
    for (resultIndex, child) in wave.zip state.children do
      let out ← child.stdout.readToEnd
      let errOut ← child.stderr.readToEnd
      let exitCode ← child.wait
      if exitCode == 0 && !out.isEmpty then
        let jobResult := state.results[resultIndex]!
        let stillUnparsed := (errOut.splitOn "not formatted:").length > 1
        state :=
          { state with
            results := state.results.set!
              resultIndex
              { jobResult with
                output := out
                diagnostics := if stillUnparsed then jobResult.diagnostics else #[]
              } }
    state := { state with cursor := state.cursor + jobs }
  return state.results

/-- The scheduler seam. The main pass is SEQUENTIAL today — the single place a
    core-pinned worker pool (Driver.Pool) or batched uring loop (Driver.Io) will
    slot in, leaving the pure core and `runJob` untouched. Every job shares ONE
    batch env (`Frontend.batchEnv` — imported once per invocation, immutable
    thereafter); per-file syntax extensions layer on top functionally inside
    `Session`.

    Files the union env cannot parse (co-imported DSL syntax conflicts; the
    runtime's one-shot import model forbids a second in-process loadExts import)
    retry as ONE-FILE SUBPROCESSES, spawned in bounded concurrent waves — they
    are independent processes, each importing its own (subset) env, so the only
    coupling is transient memory: `LEAN4FMT_JOBS` bounds the wave (default 8). -/
unsafe
def run_all
    (style : Style.Style)
    (paths : Array System.FilePath)
    (elabFallback : Bool := true)
    (retry : Option (String × Array String) := none)
    : IO (Array result) := do
  let env ← Frontend.batch_env paths
  -- main pass: IO tasks over the shared frozen env (default task priority = the
  -- runtime's core-sized pool; the env is `leakEnv`-persistent, shared
  -- read-only — the LSP sharing model). `runJob` catches its own errors, so a
  -- task failure here is a runtime fault, reported per file rather than thrown.
  let tasks ← paths.mapM (fun path => IO.asTask (run_job env style path elabFallback none))
  let mut results : Array result := #[]
  for path in paths, task in tasks do
    match task.get with
    | .ok jobResult => results := results.push jobResult
    | .error message =>
      results :=
        results.push
          { path,
            original := "",
            output := "",
            diagnostics := #[{ severity := .error, rule := "io", message := toString message }] }
  let some (exe, extraArgs) := retry | return results
  run_retries results exe extraArgs

/-- Expand file/dir inputs into the `.lean` file set to process (directories are
    walked, `.lake` build trees skipped), deduplicated and in a deterministic
    (sorted) order so runs are reproducible. -/
def expand (inputs : Array System.FilePath) : IO (Array System.FilePath) := do
  let mut files : Array System.FilePath := #[]
  for inputPath in inputs do
    if ← inputPath.isDir then files := files ++ (← find_lean inputPath)
    else files := files.push inputPath
  let sorted := files.qsort (fun left right => left.toString < right.toString)
  -- dedup (adjacent, since sorted)
  let mut out : Array System.FilePath := #[]
  for path in sorted do
    if out.back?.map (· == path) != some true then out := out.push path
  return out

end Lean4Fmt.Driver
