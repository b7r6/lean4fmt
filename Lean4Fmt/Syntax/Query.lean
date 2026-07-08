/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // SYNTAX // QUERY
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Role-based child access and safe indexing over `Syntax`, plus the token
    stream used by the correctness gate (§0.1).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean

namespace Lean4Fmt.Syntax

open Lean

/-- The token stream (atoms + idents), ignoring whitespace/trivia and empty EOI
    atoms. A meaning-preserving formatter keeps this exactly (§0.1). -/
partial def leafToks : Lean.Syntax → Array String
  | .atom _ v => if v.isEmpty then #[] else #[v]
  | .ident _ _ n _ => #[n.toString]
  | .missing => #[]
  | .node _ _ args => args.foldl (fun acc x => acc ++ leafToks x) #[]

/-- First identifier appearing in a subtree (the target of `namespace`/`open`). -/
partial def firstIdent : Lean.Syntax → Name
  | .ident _ _ n _ => n
  | .node _ _ args => args.foldl (fun acc x => if acc.isAnonymous then firstIdent x else acc) .anonymous
  | _ => .anonymous

/-- Safe child access. -/
def child? (stx : Lean.Syntax) (i : Nat) : Option Lean.Syntax := stx.getArgs[i]?

end Lean4Fmt.Syntax
