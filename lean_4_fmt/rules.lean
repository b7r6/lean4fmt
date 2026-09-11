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
import lean_4_fmt.rules.diagnostic
import lean_4_fmt.rules.trivia
import lean_4_fmt.rules.naming
import lean_4_fmt.rules.house

namespace Lean4Fmt.Rules

/-- Run every diagnostic-only lint rule over a source module. -/
def lint (style : Lean4Fmt.Style.Style) (stx : Lean.Syntax) (src : String) : Array Diagnostic :=
  Naming.lint style stx ++ Trivia.lint src ++ House.lint style stx
