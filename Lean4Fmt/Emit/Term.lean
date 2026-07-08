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

/-- Width-aware bracketed comma list `l e₁, e₂, … r`: flat if it fits, else one
    element per line indented by 2 with `l`/`r` on their own lines (the standard
    all-or-nothing `commaList` group). Skips the parser's comma atoms. -/
private def commaGroup (walk : Walk) (l r : String) (children : Array Lean.Syntax) : EmitM Doc := do
  let mut ds : Array Doc := #[]
  for c in children do
    if c.isAtom then continue
    ds := ds.push (← walk c)
  return Lean4Fmt.Doc.commaList l r ds

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
      -- `fn a b c` — width-aware: flat if it fits, else `fn` on its line with each
      -- argument on a continuation line indented by `layout.indent`. All-or-
      -- nothing (a `group`): the source did not dictate this, the width does.
      let fn := args[0]!
      let argList := (args[1]?.map (·.getArgs)).getD #[]
      let ind := (← read).layout.indent
      let fnDoc ← walk fn
      let mut argsDoc : Doc := .nil
      for a in argList do argsDoc := argsDoc ++ .line ++ (← walk a)
      return .group (fnDoc ++ .nest ind argsDoc)
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
      return (← commaGroup walk "⟨" "⟩" ((args[1]?.map (·.getArgs)).getD #[]))
    else if kind.toString == "«term[_]»" then
      return (← commaGroup walk "[" "]" ((args[1]?.map (·.getArgs)).getD #[]))
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
    else if kind == ``Lean.Parser.Term.let then
      -- [let, letConfig, letDecl, sep(`;`?), body]. The binding head (config +
      -- decl + optional `;`) is reproduced token-for-token; the body — usually a
      -- nested `let` (a chain) or the final expression — is walked and placed on
      -- the next line at the SAME indent (Lean let-chains don't nest). The
      -- hardline makes flatWidth=none, so the value always drops to its own line.
      let cfgT := (((args[1]?.map bareSrc).getD "").trimAscii.toString)
      let declDoc ← walk (args[2]?.getD .missing)
      let sepT := (((args[3]?.map bareSrc).getD "").trimAscii.toString)
      let bodyDoc ← walk (args[args.size-1]?.getD .missing)
      let cfgDoc : Doc := if cfgT.isEmpty then .nil else .text cfgT ++ .space
      return .text "let " ++ cfgDoc ++ declDoc ++ .text sepT ++ .hardline ++ bodyDoc
    else if kind == ``Lean.Parser.Term.hole then
      return .text "_"
    else if kind == `str || kind == `num || kind == `scientific || kind == `char then
      return (← verbatim stx)      -- literal: reproduce exactly
    else
      return (← verbatim stx)      -- not yet ported (let/match/do/if/…): opaque
  | .missing => return .nil

end Lean4Fmt.Emit.Term
