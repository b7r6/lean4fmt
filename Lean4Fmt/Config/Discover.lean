/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                  // LEAN4FMT // CONFIG // DISCOVER
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Walk up the directory tree for `.lean4fmt.lean` (like `.clang-format`).
    DESIGN_V2 §5/§11.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean

namespace Lean4Fmt.Config

/-- Find the nearest `.lean4fmt.lean` at or above `start`. -/
partial
def discover (start : System.FilePath) : IO (Option System.FilePath) := do
  let cand := start / ".lean4fmt.lean"
  if ← cand.pathExists then
    return some cand
  match start.parent with
  | some p =>
    if p == start then
      return none
    else discover p
  | none => return none

end Lean4Fmt.Config
