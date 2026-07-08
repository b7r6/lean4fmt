/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // LEAN4FMT // EMIT // TERM
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Expression constructs. Ported to real `Doc`: applications, binary operators,
    parens/projections, anonymous constructors, list literals, literals — the
    flat, single-line-friendly terms. Recurses via `walk`. Anything carrying a
    line comment (§0.4) or not yet handled falls back to opaque reproduction, so
    it stays token-preserving and idempotent (the gate confirms).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Emit.Monad
import Lean4Fmt.Syntax.Kinds
import Lean4Fmt.Syntax.Trivia

namespace Lean4Fmt.Emit.Term

open Lean Lean4Fmt.Doc Lean4Fmt.Emit

/-- Comma-separated children (skipping the parser's comma atoms), each walked. -/
private def commaSep (walk : Walk) (children : Array Lean.Syntax) : EmitM Doc := do
  let mut d : Doc := .nil
  let mut first := true
  for c in children do
    if c.isAtom then continue      -- skip existing "," separators
    d := d ++ (if first then .nil else .text ", ") ++ (← walk c)
    first := false
  return d

/-- Emit an expression construct, recursing via `walk`. Produces flat Doc for the
    handled kinds; everything else (and anything with a line comment) reproduces
    verbatim. -/
partial def emit (walk : Walk) (stx : Lean.Syntax) : EmitM Doc := do
  -- comment hazard (§0.4): never restructure a subtree carrying a line comment
  if Lean4Fmt.Syntax.subtreeHasLineComment stx then return (← verbatim stx)
  match stx with
  | .atom _ v => return .text v
  | .ident _ _ n _ => return .text n.toString
  | .node _ kind args =>
    -- binary operator: lhs ␣ op ␣ rhs
    if Lean4Fmt.Syntax.isBinOp kind && args.size == 3 then
      return (← walk args[0]!) ++ .space ++ (← walk args[1]!) ++ .space ++ (← walk args[2]!)
    else if kind == ``Lean.Parser.Term.app then
      let fn := args[0]!
      let argList := (args[1]?.map (·.getArgs)).getD #[]
      let mut d ← walk fn
      for a in argList do d := d ++ .space ++ (← walk a)
      return d
    else if kind == ``Lean.Parser.Term.paren then
      -- "(" content ")" — content is args[1] (may be empty for unit)
      match args[1]? with
      | some c => return .text "(" ++ (← walk c) ++ .text ")"
      | none => return .text "()"
    else if kind == ``Lean.Parser.Term.proj then
      -- obj "." field   (args[0]=obj, args[1]=".", args[2]=field)
      return (← walk args[0]!) ++ .text "." ++ (← walk (args[2]?.getD .missing))
    else if kind == ``Lean.Parser.Term.dotIdent then
      return .text "." ++ (← walk (args[1]?.getD .missing))
    else if kind == ``Lean.Parser.Term.anonymousCtor then
      return .text "⟨" ++ (← commaSep walk ((args[1]?.map (·.getArgs)).getD #[])) ++ .text "⟩"
    else if kind.toString == "«term[_]»" then
      return .text "[" ++ (← commaSep walk ((args[1]?.map (·.getArgs)).getD #[])) ++ .text "]"
    else if kind.toString == "termIfThenElse" then
      -- [if, cond, then, thenBranch, else, elseBranch]; a width-aware group:
      -- flat `if c then a else b`, or broken with 2-space branches, `else` at
      -- the if's base column (§ active layout). Branches recurse via `walk`.
      let cond ← walk (args[1]?.getD .missing)
      let thenB ← walk (args[3]?.getD .missing)
      let elseB ← walk (args[5]?.getD .missing)
      return .group (
        .text "if " ++ cond ++ .text " then"
          ++ .nest 2 (.line ++ thenB)
          ++ .line ++ .text "else"
          ++ .nest 2 (.line ++ elseB))
    else if kind == ``Lean.Parser.Term.hole then
      return .text "_"
    else if kind == `str || kind == `num || kind == `scientific || kind == `char then
      return (← verbatim stx)      -- literal: reproduce exactly
    else
      return (← verbatim stx)      -- not yet ported (let/match/do/if/…): opaque
  | .missing => return .nil

end Lean4Fmt.Emit.Term
