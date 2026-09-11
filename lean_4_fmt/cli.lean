/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                              // LEAN4FMT // CLI
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Command-line surface (doc/design.md §11). Hand-rolled for now; the schema-as-data
    version on `StdlibEx.CLI` is §11.1 stage 1 (a `require` edge, added when we
    wire lean4fmt into the StdlibEx-bearing tree).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.casing

namespace Lean4Fmt.Cli

inductive mode
  | format        -- print to stdout (default)
  | check         -- exit 1 if any file would change
  | write         -- overwrite in place
  | stats         -- coverage accounting: active/verbatim/trivia bytes per file + total
  | lint          -- report diagnostic-only house-style hazards
  | renamePlan    -- read `NAME AXIS` lines on stdin, print the casing rename plan
  | renameApply   -- orchestrate the rename over the given files (subprocess/file)
  | renameDecls   -- worker: print `NAME<TAB>AXIS` for one file's declarations
  | renameRewrite -- worker: apply a precomputed `--map` to one file, in place
  | resolveDump   -- probe: elaborate one file, print resolved `range<TAB>fullName`
  deriving Repr, Inhabited, BEq

structure Options where
  mode   : mode := .format
  preset : String := "straylight"
  width  : Option Nat := none     -- explicit --width overrides the preset
  /-- Fall back to the interleaved elaborating frontend when the cheap parse
      can't handle a file (same-file notation/macros). Measured warm marginal
      cost is 5–20ms/file on the continuity corpus — hence the default; `--elab
      off` keeps strict passthrough (such files skip, with a diagnostic). -/
  elabFallback : Bool := true
  /-- Retry superset-env parse conflicts in a one-file subprocess (see
      Driver.runJob). `--no-retry` is set on those subprocesses themselves —
      the recursion guard. -/
  retry : Bool := true
  /-- Diagnostic log threshold: trace|debug|info|warn|error. `debug` shows
      every verbatim opt-out (the coverage trail). -/
  logLevel : String := "warn"
  /-- Emit one canonical JSON object per file in lint mode. Intended for
      manifests/shards; suppresses human diagnostic logging. -/
  json : Bool := false
  /-- Discover each input's lake workspace (nearest lakefile up the tree) and
      append its `lake env` LEAN_PATH to the olean search path. `--lake off`
      keeps the explicit-LEAN_PATH-only behavior. -/
  lakeEnv : Bool := true
  /-- Precomputed rename map file for the `renameRewrite` worker: lines
      `SRC<TAB>TGT`, the plan the orchestrator built over the whole file set. -/
  mapFile : Option String := none
  /-- Rewrite by RESOLVED decl identity (G-L7.4) instead of token spelling:
      the set is full names, the plan keys by identity, and each occurrence is
      rewritten iff it RESOLVES to a renamed decl. Needs elaboration + the farm. -/
  resolve : Bool := false
  /-- Target case for resolver-backed declaration renames. Kept separate from
      the style preset because a migration is a tree transaction, not a
      formatting preference. The systems-tree recommendation is `snake`. -/
  renameCase : String := "snake"
  /-- Prebuilt olean farm dir the orchestrator hands each `--resolve` worker
      (`--farm <path>`), so cross-package modules resolve without a per-worker
      rebuild. -/
  farmDir : Option String := none
  /-- Files whose CLOSURE is off-limits (`--protect <file>`, repeatable): they
      are resolved read-only for the names they DEFINE or REFERENCE, and every
      such name is dropped from the rename plan — so a whole-tree pass never
      renames a decl these files depend on. They are NEVER rewritten. This is how
      the protected formatting-study files (ServeFd, GradedMonad, ReeseAlgebra)
      keep the frozen packages mostly snakeable without being touched. -/
  protect : List String := []
  files : List String := []
  deriving Repr, Inhabited

/-- Parse argv into `Options`. -/
def parse (args : List String) : Options :=
  parseArgs {} args
  where
    parseArgs (options : Options) : List String → Options
      | "--check" :: rest => parseArgs { options with mode := .check } rest
      | "--stats" :: rest => parseArgs { options with mode := .stats } rest
      | "--lint" :: rest => parseArgs { options with mode := .lint } rest
      | "--rename-plan" :: rest => parseArgs { options with mode := .renamePlan } rest
      | "--rename-apply" :: rest => parseArgs { options with mode := .renameApply } rest
      | "--rename-decls" :: rest => parseArgs { options with mode := .renameDecls } rest
      | "--rename-rewrite" :: rest => parseArgs { options with mode := .renameRewrite } rest
      | "--resolve-dump" :: rest => parseArgs { options with mode := .resolveDump } rest
      | "--map" :: file :: rest => parseArgs { options with mapFile := some file } rest
      | "--resolve" :: rest => parseArgs { options with resolve := true } rest
      | "--rename-case" :: target :: rest =>
        parseArgs { options with renameCase := target } rest
      | "--farm" :: dir :: rest => parseArgs { options with farmDir := some dir } rest
      | "--protect" :: file :: rest =>
        parseArgs { options with protect := options.protect ++ [file] } rest
      | "--write" :: rest => parseArgs { options with mode := .write } rest
      | "-w" :: rest => parseArgs { options with mode := .write } rest
      | "--width" :: width :: rest =>
        parseArgs { options with width := some width.toNat! } rest
      | "--style" :: preset :: rest => parseArgs { options with preset } rest
      | "--log-level" :: level :: rest => parseArgs { options with logLevel := level } rest
      | "--json" :: rest => parseArgs { options with json := true } rest
      | "--elab" :: value :: rest =>
        parseArgs { options with elabFallback := value != "off" } rest
      | "--no-retry" :: rest => parseArgs { options with retry := false } rest
      | "--lake" :: value :: rest => parseArgs { options with lakeEnv := value != "off" } rest
      | file :: rest => parseArgs { options with files := options.files ++ [file] } rest
      | [] => options

def usage : String :=
  "Usage: lean4fmt [--check | --write | --stats | --lint] [--json] [--width N] [--style NAME] [--rename-case snake|camel|upperCamel|preserve] [--elab auto|off] [--lake auto|off] <file...>\n\n"
      ++ "Multiple files in one invocation are supported (each is parsed against its own\n"
      ++ "imports). If a file's syntax-extension initializers ever conflict in-process,\n"
      ++ "fall back to one file per process: find . -name '*.lean' | xargs -n1 lean4fmt"

end Lean4Fmt.Cli
