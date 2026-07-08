/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // DRIVER // FORMAT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Single-file orchestration: parse → format → gate → text. Delegates to the
    Frontend safety gate (DESIGN_V2 §11). This is the seam that will switch from
    the v1 emitter to the v2 Emit→Render spine with no change to callers.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Frontend
import Lean4Fmt.Emitter

namespace Lean4Fmt.Driver

/-- Format one file, returning the gated output (never worse than input). -/
unsafe def formatFile (path : String) (width : Nat := 100) : IO String := do
  let contents ← IO.FS.readFile path
  Lean4Fmt.Frontend.formatFile path contents { lineWidth := width }

end Lean4Fmt.Driver
