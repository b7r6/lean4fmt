/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                // LEAN4FMT // RULES
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Barrel + lint-pass aggregator. The pass is wired into the format pipeline
    (`Frontend.formatSafe`) so diagnostics flow through `Result`. Rules observe
    syntax/source and never rewrite; layout stays with the Emit walk.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import Lean4Fmt.Rules.Diagnostic
import Lean4Fmt.Rules.Trivia
import Lean4Fmt.Rules.Naming
import Lean4Fmt.Rules.House

namespace Lean4Fmt.Rules

/-- Run every diagnostic-only lint rule over a source module. -/
def lint (style : Lean4Fmt.Style.Style) (stx : Lean.Syntax) (src : String) : Array Diagnostic :=
  Naming.lint style stx ++ Trivia.lint src ++ House.lint style stx
