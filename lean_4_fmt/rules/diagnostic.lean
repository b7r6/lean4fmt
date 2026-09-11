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

def Diagnostic.render (document : Diagnostic) : String :=
  let sev :=
    match document.severity with
    | .debug   => "debug"
    | .info    => "info"
    | .warning => "warning"
    | .error   => "error"
  let tag := if document.rule.isEmpty then "" else s!" [{document.rule}]"
  let role := if document.role.isEmpty then "" else s!" ({document.role})"
  s!"{document.pos}: {sev}{tag}{role}: {document.message}"

end Lean4Fmt.Rules
