/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                // LEAN4FMT // RULES
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Barrel + the lint-pass aggregator. `lint` is the slot the future `ruff4lean`
    rule set lands in: today it composes the per-category rule passes (Naming,
    Trivia, …), each of which is currently a no-op. The pass is wired into the
    format pipeline (Frontend.formatSafe) so diagnostics flow through `Result`
    without any caller change when the rules go live. Rules are pure functions of
    the module `Syntax`; they never rewrite (that stays with the Emit walk) — a
    lint pass only observes and reports (§ ruff4lean).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import Lean4Fmt.Rules.Diagnostic
import Lean4Fmt.Rules.Trivia
import Lean4Fmt.Rules.Naming

namespace Lean4Fmt.Rules

/-- Run every lint rule over a module and collect diagnostics. No-op today (each
    rule returns `#[]`); this is the single composition point for the rule set. -/
def lint (stx : Lean.Syntax) : Array Diagnostic := Naming.lint stx
