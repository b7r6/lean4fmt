/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // LEAN4FMT // DRIVER // CONFIG
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    fmt.lean discovery (doc/design.md §5): walk from the file's directory to the
    filesystem root, collect every `fmt.lean`, and apply them ROOT → LEAF onto
    the CLI base style (nearest file wins field-wise; `preset` resets). A
    malformed fmt.lean is thrown as an IO error — runJob converts it into a
    loud per-file diagnostic with identity output, never a silent misformat.

    IO (filesystem walk). The parse/apply core is pure (Style.Config).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.style

namespace Lean4Fmt.Driver

open Lean4Fmt.Style

/-- The chain of fmt.lean files governing `path`, outermost first. -/
partial
def config_chain (path : System.FilePath) : IO (List System.FilePath) := do
  let rec ascend
      (dir : System.FilePath)
      (configs : List System.FilePath)
      : IO (List System.FilePath) := do
    let configs ← do
      let config := dir / "fmt.lean"
      if (← config.pathExists) then pure (config :: configs) else pure configs
    match dir.parent with
    | some parent => if parent == dir then pure configs else ascend parent configs
    | none => pure configs
  match (← IO.FS.realPath path).parent with
  | some dir => ascend dir []
  | none => pure []

/-- Resolve the effective style for one file: CLI base, then each fmt.lean on
    the chain applied outermost → innermost. -/
def style_for (base : Style) (path : System.FilePath) : IO Style := do
  let mut resolved := base
  for cfg in (← config_chain path) do
    match apply_config_text resolved (← IO.FS.readFile cfg) with
    | .ok nextStyle => resolved := nextStyle
    | .error message => throw (IO.userError s!"{cfg}: {message}")
  return resolved

end Lean4Fmt.Driver
