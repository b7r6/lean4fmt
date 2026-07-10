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

/-- The trivia (leading+trailing) of a leaf's `SourceInfo`, as raw text. -/
private def triviaOfInfo : Lean.SourceInfo → String
  | .original leading _ trailing _ => leading.toString ++ trailing.toString
  | _ => ""

/-- All trivia text across the tree (leaves carry the trivia). -/
partial def triviaText : Lean.Syntax → String
  | .atom info _ => triviaOfInfo info
  | .ident info _ _ _ => triviaOfInfo info
  | .node _ _ args => args.foldl (fun acc x => acc ++ triviaText x) ""
  | .missing => ""

/-- Non-whitespace content of ALL trivia — i.e. the comment characters (trivia is
    only whitespace + comments). Comments are not tokens, so `leafToks` alone does
    not catch a DROPPED comment; the gate compares this too. Whitespace is stripped
    so that reflowed/re-indented (but content-identical) comments still match. -/
def commentContent (stx : Lean.Syntax) : String :=
  String.ofList ((triviaText stx).toList.filter (fun c => !c.isWhitespace))

/-- First identifier appearing in a subtree (the target of `namespace`/`open`). -/
partial def firstIdent : Lean.Syntax → Name
  | .ident _ _ n _ => n
  | .node _ _ args => args.foldl (fun acc x => if acc.isAnonymous then firstIdent x else acc) .anonymous
  | _ => .anonymous

/-- Safe child access. -/
def child? (stx : Lean.Syntax) (i : Nat) : Option Lean.Syntax := stx.getArgs[i]?

end Lean4Fmt.Syntax
