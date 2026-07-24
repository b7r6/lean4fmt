/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // LEAN4FMT // DRIVER // CONFIG
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    fmt.lean discovery (DESIGN_V2 §5): walk from the file's directory to the
    filesystem root, collect every `fmt.lean`, and apply them ROOT → LEAF onto
    the CLI base style (nearest file wins field-wise; `preset` resets). A
    malformed fmt.lean is thrown as an IO error — runJob converts it into a
    loud per-file diagnostic with identity output, never a silent misformat.

    IO (filesystem walk). The parse/apply core is pure (Style.Config).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Style

namespace Lean4Fmt.Driver

open Lean4Fmt.Style

/-- The chain of fmt.lean files governing `path`, outermost first. -/
partial
def config_chain (path : System.FilePath) : IO (List System.FilePath) := do
  let rec up (dir : System.FilePath) (acc : List System.FilePath) : IO (List System.FilePath) := do
    let acc ← do
      let f := dir / "fmt.lean"
      if (← f.pathExists) then pure (f :: acc) else pure acc
    match dir.parent with
    | some p => if p == dir then pure acc else up p acc
    | none => pure acc
  match (← IO.FS.realPath path).parent with
  | some dir => up dir []
  | none => pure []

/-- Resolve the effective style for one file: CLI base, then each fmt.lean on
    the chain applied outermost → innermost. -/
def style_for (base : Style) (path : System.FilePath) : IO Style := do
  let mut s := base
  for cfg in (← config_chain path) do
    match apply_config_text s (← IO.FS.readFile cfg) with
    | .ok s' => s := s'
    | .error e => throw (IO.userError s!"{cfg}: {e}")
  return s

end Lean4Fmt.Driver
