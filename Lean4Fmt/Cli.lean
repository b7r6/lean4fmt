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
  | format   -- print to stdout (default)
  | check    -- exit 1 if any file would change
  | write    -- overwrite in place
  deriving Repr, Inhabited, BEq

structure Options where
  mode   : Mode := .format
  preset : String := "straylight"
  width  : Nat := 100
  files  : List String := []
  deriving Repr, Inhabited

/-- Parse argv into `Options`. -/
def parse (args : List String) : Options := Id.run do
  let mut o : Options := {}
  let mut rest := args
  repeat
    match rest with
    | "--check" :: r => o := { o with mode := .check }; rest := r
    | "--write" :: r => o := { o with mode := .write }; rest := r
    | "-w" :: r => o := { o with mode := .write }; rest := r
    | "--width" :: n :: r => o := { o with width := n.toNat! }; rest := r
    | "--style" :: s :: r => o := { o with preset := s }; rest := r
    | f :: r => o := { o with files := o.files ++ [f] }; rest := r
    | [] => break
  return o

def usage : String :=
  "Usage: lean4fmt [--check | --write] [--width N] [--style NAME] <file...>\n\n" ++
  "Note: Lean module initialization runs once per process, so formatting\n" ++
  "multiple files in one call may fail. Use: find . -name '*.lean' | xargs -n1 lean4fmt"

end Lean4Fmt.Cli
