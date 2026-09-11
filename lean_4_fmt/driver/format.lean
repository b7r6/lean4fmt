/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // DRIVER // FORMAT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Single-file orchestration: parse → format → gate → text. Delegates to the
    Frontend safety gate (doc/design.md §8). This is the seam that will switch from
    the v1 emitter to the v2 Emit→Render spine with no change to callers.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.frontend
import lean_4_fmt.style
import lean_4_fmt.driver.config

namespace Lean4Fmt.Driver

/-- Format one file, returning the gated output (never worse than input) and the
    lint diagnostics. Resolves the `--style` preset via `Style.byName?` (falling
    back to straylight) and overrides the line width from `--width`. -/
unsafe
def format_file
    (path : String)
    (width : Nat := 100)
    (preset : String := "straylight")
    (elabFallback : Bool := true)
    : IO (String × Array Lean4Fmt.Rules.Diagnostic) := do
  let contents ← IO.FS.readFile path
  let base := (Lean4Fmt.Style.by_name? preset).getD Lean4Fmt.Style.straylight
  let base := { base with layout := { base.layout with lineWidth := width } }
  let style ← style_for base path
  Lean4Fmt.Frontend.format_file path contents style elabFallback

end Lean4Fmt.Driver
