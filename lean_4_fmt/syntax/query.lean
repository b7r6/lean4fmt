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
partial
def leaf_toks : Lean.Syntax → Array String
  | .atom _ value      => if value.isEmpty then #[] else #[value]
  | .ident _ _ count _ => #[count.toString]
  | .missing           => #[]
  | .node _ _ args     => args.foldl (fun tokens child => tokens ++ leaf_toks child) #[]

/-- The trivia (leading+trailing) of a leaf's `SourceInfo`, as raw text. -/
private
def trivia_of_info : Lean.SourceInfo → String
  | .original leading _ trailing _ => leading.toString ++ trailing.toString
  | _ => ""

/-- All trivia text across the tree (leaves carry the trivia). -/
partial
def trivia_text : Lean.Syntax → String
  | .atom info _      => trivia_of_info info
  | .ident info _ _ _ => trivia_of_info info
  | .node _ _ args    => args.foldl (fun text child => text ++ trivia_text child) ""
  | .missing          => ""

/-- Non-whitespace content of ALL trivia — i.e. the comment characters (trivia is
    only whitespace + comments). Comments are not tokens, so `leafToks` alone does
    not catch a DROPPED comment; the gate compares this too. Whitespace is stripped
    so that reflowed/re-indented (but content-identical) comments still match. -/
def comment_content (stx : Lean.Syntax) : String :=
  String.ofList ((trivia_text stx).toList.filter (fun char => !char.isWhitespace))

/-- The kind SPINE: every node kind in preorder. Token equality alone
    under-specifies meaning in whitespace-sensitive regions — dedenting a tactic
    out of a `·` bullet (or a statement out of a branch) moves it to a different
    scope with an IDENTICAL token stream. Tree-shape equality closes that class:
    a meaning-preserving formatter keeps the token stream AND the kind spine. -/
partial
def kind_spine (stx : Lean.Syntax) : Array Name :=
  match stx with
  | .node _ kind args => args.foldl (fun kinds child => kinds ++ kind_spine child) #[kind]
  | _                 => #[]

/-- First identifier appearing in a subtree (the target of `namespace`/`open`). -/
partial
def first_ident : Lean.Syntax → Name
  | .ident _ _ count _ => count
  | .node _ _ args =>
    args.foldl
      (fun found child => if found.isAnonymous then first_ident child else found)
      .anonymous
  | _ => .anonymous

/-- Safe child access. -/
def child? (stx : Lean.Syntax) (childIndex : Nat) : Option Lean.Syntax := stx.getArgs[childIndex]?

end Lean4Fmt.Syntax
