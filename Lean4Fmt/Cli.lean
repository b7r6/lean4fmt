/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                              // LEAN4FMT // CLI
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Command-line surface (DESIGN_V2 §11). Hand-rolled for now; the schema-as-data
    version on `StdlibEx.CLI` is §11.1 stage 1 (a `require` edge, added when we
    wire lean4fmt into the StdlibEx-bearing tree).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Lean4Fmt.Cli

inductive Mode
  | format     -- print to stdout (default)
  | check      -- exit 1 if any file would change
  | write      -- overwrite in place
  | stats      -- coverage accounting: active/verbatim/trivia bytes per file + total
  | renamePlan -- read `NAME AXIS` lines on stdin, print the casing rename plan
  deriving Repr, Inhabited, BEq

structure Options where
  mode   : Mode := .format
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
  /-- Discover each input's lake workspace (nearest lakefile up the tree) and
      append its `lake env` LEAN_PATH to the olean search path. `--lake off`
      keeps the explicit-LEAN_PATH-only behavior. -/
  lakeEnv : Bool := true
  files : List String := []
  deriving Repr, Inhabited

/-- Parse argv into `Options`. -/
def parse (args : List String) : Options :=
  Id.run do
    let mut o : Options := {}
    let mut rest := args
    repeat
      match rest with
      | "--check" :: r => o := { o with mode := .check }; rest := r
      | "--stats" :: r => o := { o with mode := .stats }; rest := r
      | "--rename-plan" :: r => o := { o with mode := .renamePlan }; rest := r
      | "--write" :: r => o := { o with mode := .write }; rest := r
      | "-w" :: r => o := { o with mode := .write }; rest := r
      | "--width" :: n :: r => o := { o with width := some n.toNat! }; rest := r
      | "--style" :: s :: r => o := { o with preset := s }; rest := r
      | "--log-level" :: l :: r => o := { o with logLevel := l }; rest := r
      | "--elab" :: v :: r => o := { o with elabFallback := v != "off" }; rest := r
      | "--no-retry" :: r => o := { o with retry := false }; rest := r
      | "--lake" :: v :: r => o := { o with lakeEnv := v != "off" }; rest := r
      | f :: r => o := { o with files := o.files ++ [f] }; rest := r
      | [] => break
    return o

def usage : String :=
  "Usage: lean4fmt [--check | --write | --stats] [--width N] [--style NAME] [--elab auto|off] [--lake auto|off] <file...>\n\n"
      ++ "Multiple files in one invocation are supported (each is parsed against its own\n"
      ++ "imports). If a file's syntax-extension initializers ever conflict in-process,\n"
      ++ "fall back to one file per process: find . -name '*.lean' | xargs -n1 lean4fmt"

end Lean4Fmt.Cli
