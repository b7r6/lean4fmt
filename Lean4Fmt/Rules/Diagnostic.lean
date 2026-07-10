/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                  // LEAN4FMT // RULES // DIAGNOSTIC
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Diagnostics collected by the lint pass (`Rules`), kept separate from the
    emitter. Pure.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Lean4Fmt.Rules

inductive Severity where
  | info | warning | error
  deriving Repr, Inhabited, BEq

structure Diagnostic where
  severity : Severity
  pos      : Nat := 0
  rule     : String := ""
  message  : String
  deriving Repr, Inhabited

def Diagnostic.render
    (d : Diagnostic)
    : String :=

  let sev := match d.severity with | .info => "info" | .warning => "warning" | .error => "error"
  let tag := if d.rule.isEmpty then "" else s!" [{d.rule}]"
  s!"{d.pos}: {sev}{tag}: {d.message}"

end Lean4Fmt.Rules
