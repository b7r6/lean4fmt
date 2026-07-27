/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                  // LEAN4FMT // RULES // DIAGNOSTIC
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Diagnostics collected by the lint pass (`Rules`), kept separate from the
    emitter. Pure.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Lean4Fmt.Rules

inductive severity where
  | debug
  | info
  | warning
  | error
  deriving Repr, Inhabited, BEq

structure Diagnostic where
  severity : severity
  pos      : Nat := 0
  rule     : String := ""
  role     : String := ""
  message  : String
  deriving Repr, Inhabited

def Diagnostic.render (d : Diagnostic) : String :=
  let sev :=
    match d.severity with
    | .debug   => "debug"
    | .info    => "info"
    | .warning => "warning"
    | .error   => "error"
  let tag := if d.rule.isEmpty then "" else s!" [{d.rule}]"
  let role := if d.role.isEmpty then "" else s!" ({d.role})"
  s!"{d.pos}: {sev}{tag}{role}: {d.message}"

end Lean4Fmt.Rules
