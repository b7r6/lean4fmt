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
private def commaGroup
            (walk : Walk)
            (l r : String)
            (children : Array Lean.Syntax)
            : EmitM Doc := do
  let mut ds : Array Doc := #[]
  for c in children do
    if c.isAtom then continue
    ds := ds.push (← walk c)
  return Lean4Fmt.Doc.commaList l r ds

/-- A single `structInstField` = [structInstLVal, «rest»]. The LVal (field name /
    path) is reproduced verbatim; the value (the term after `:=`, found inside the
    `structInstFieldDef` in «rest») is walked so it lays out actively. A shorthand
    field `{ x }` (no `:=`) is just its LVal. -/
private partial def structFieldDoc
            (walk : Walk)
            (field : Lean.Syntax)
            : EmitM Doc := do
  let fa := field.getArgs
  let lval ← verbatim (fa[0]?.getD .missing)
  let rest := (fa[1]?.getD Lean.Syntax.missing).getArgs
  let fd? := rest.find? (·.getKind == ``Lean.Parser.Term.structInstFieldDef)
  match fd? with
  | some fd =>
    let da := fd.getArgs
    let v := da[da.size - 1]?.getD Lean.Syntax.missing        -- [":=", null?, value]
    return lval ++ .text " := " ++ (← walk v)
  | none => return lval

/-- Emit an expression construct, recursing via `walk`. Produces flat Doc for the
    handled kinds; everything else (and anything with a line comment) reproduces
    verbatim. -/
partial def emit
            (walk : Walk)
            (stx : Lean.Syntax)
            : EmitM Doc := do
  -- comment hazard (§0.4): never restructure a subtree carrying a line comment.
  -- The tail token's TRAILING is exempt: it belongs to the enclosing seam
  -- (whoever places this form also places its trailing — Module for commands,
  -- the do-statement loop for statements), so it survives without our help.
  if Lean4Fmt.Syntax.hasOwnedLineComment stx then return (← verbatim stx)
  match stx with
  | .atom _ v => return .text v
  | .ident _ _ n _ => return .text n.toString
  | .node _ kind args =>
    -- binary operator: lhs ␣ op ␣ rhs. `Term.arrow` is the same 3-slot shape
    -- (the atom carries the source spelling — `→` or `->` — and the token gate
    -- cares, so it rides through the walk as-is).
    if (Lean4Fmt.Syntax.isBinOp kind || kind == ``Lean.Parser.Term.arrow) && args.size == 3 then
      -- `lhs op rhs` — width-aware: flat if it fits, else break BEFORE the operator
      -- (the operator leads the continuation line, indented by continuationIndent).
      let lhs ← walk args[0]!
      let op ← walk args[1]!
      let rhs ← walk args[2]!
      let cont := (← read).layout.continuationIndent
      return .group (lhs ++ .nest cont (.line ++ op ++ .space ++ rhs))
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
    else if kind == ``Lean.Parser.Term.structInst then
      -- `{ f₁ := v₁, f₂ := v₂ }` — width-aware: flat if it fits, else one field
      -- per line, aligned under the first (which sits on the `{ ` line). Guarded:
      -- a `with`-source (`{ s with … }`), a `..` ellipsis, or an empty/odd body
      -- reproduces verbatim (their layout is subtler / not worth the risk yet).
      -- Also: only when the fields are COMMA-separated in source (or a single
      -- field). Lean also allows newline-separated fields (no comma tokens); since
      -- our output uses commas, reformatting a newline-separated instance would add
      -- `,` tokens the source lacked and trip the token gate — so those stay
      -- verbatim.
      let srcEmpty := ((args[1]?.map bareSrc).getD "").trimAscii.toString.isEmpty
      let ellipsisEmpty := ((args[3]?.map bareSrc).getD "").trimAscii.toString.isEmpty
      if !srcEmpty || !ellipsisEmpty then return (← verbatim stx)
      let mut fields : Array Lean.Syntax := #[]
      let mut commas := 0
      for g in ((args[2]?.map (·.getArgs)).getD #[]) do
        for c in g.getArgs do
          if c.getKind == ``Lean.Parser.Term.structInstField then fields := fields.push c
          else if c.isAtom && bareSrc c == "," then commas := commas + 1
      if fields.isEmpty then return (← verbatim stx)
      if fields.size > 1 && commas + 1 != fields.size then return (← verbatim stx)  -- newline-separated
      let mut ds : Array Doc := #[]
      for f in fields do ds := ds.push (← structFieldDoc walk f)
      return .group (.text "{ " ++ .nest 2 (Lean4Fmt.Doc.sepBy (.text "," ++ .line) ds) ++ .text " }")
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
    else if kind == ``Lean.Parser.Term.letDecl then
      -- 1-child wrapper around letIdDecl/letPatDecl/letEqnsDecl — unwrap so the
      -- inner decl dispatches (letEqnsDecl falls through `walk` to verbatim, the
      -- same source span this node would have reproduced).
      match args[0]? with
      | some inner => return (← walk inner)
      | none => return (← verbatim stx)
    else if kind == ``Lean.Parser.Term.letIdDecl || kind == ``Lean.Parser.Term.letPatDecl
         || kind == ``Lean.Parser.Term.letIdDeclNoBinders then
      -- The 5-slot binding shape [lhs, binders, type?, ":=", value] shared by
      -- plain lets (`x (y : Nat) : τ := v`), pattern lets (`⟨a, b⟩ := v`), and
      -- `do`-reassigns (`x := v`). The head left of `:=` is reproduced
      -- token-for-token (single-spaced between slots); the VALUE is walked so it
      -- lays out actively — flat on the `:=` line when it fits, else on the next
      -- line at +2 (the match-arm shape); a `do` value glues to the `:=` (its
      -- body brings its own hardline). Guards fall back to verbatim: a structural
      -- surprise, a multi-line head, or a value carrying a multi-line opaque
      -- block (re-anchoring one mid-layout drifts).
      if args.size != 5 then return (← verbatim stx)
      if (bareSrc args[3]!).trimAscii.toString != ":=" then return (← verbatim stx)
      let headParts := ((args.extract 0 3).map (fun s => (bareSrc s).trimAscii.toString)).filter
        (fun s => !s.isEmpty)
      let head := String.intercalate " " headParts.toList
      if head.isEmpty || head.any (· == '\n') then return (← verbatim stx)
      let v := args[4]!
      let vdoc ← walk v
      if Lean4Fmt.Doc.hasMultilineVerbatim vdoc then return (← verbatim stx)
      if v.getKind == ``Lean.Parser.Term.do then
        return .text head ++ .text " := " ++ vdoc
      return .text head ++ .text " :=" ++ .group (.nest 2 (.line ++ vdoc))
    else if kind == ``Lean.Parser.Term.match then
      -- [match, motive?, motive?, discrs, "with", matchAlts]. Reproduce the head
      -- `match <discrs> with` token-for-token; lay each arm `| pat => body` on its
      -- own line at the match's indent, the body width-aware after `=>`. Patterns
      -- are walked (opaque, so a multi-line pattern trips the valDoc gate to the
      -- safe span). Guarded: any structural surprise falls back to verbatim.
      let midParts := (#[args[1]?, args[2]?, args[3]?].filterMap id).toList.filterMap
        (fun s => let t := (bareSrc s).trimAscii.toString; if t.isEmpty then none else some t)
      let head := "match " ++ String.intercalate " " midParts ++ " with"
      let some altsNode := args[5]? | return (← verbatim stx)
      let mut alts : Array Lean.Syntax := #[]
      for g in altsNode.getArgs do
        for c in g.getArgs do
          if c.getKind == ``Lean.Parser.Term.matchAlt then alts := alts.push c
      if alts.isEmpty || head.any (· == '\n') then return (← verbatim stx)
      let mut armsDoc : Doc := .nil
      let mut first := true
      for alt in alts do
        let aa := alt.getArgs
        let patDoc ← walk (aa[1]?.getD .missing)
        let body := aa[aa.size-1]?.getD .missing
        let bodyDoc ← walk body
        -- a `do` body glues to the `=>` (its statements bring their own hardline);
        -- anything else is width-aware after the `=>`
        let bodyPart : Doc := if body.getKind == ``Lean.Parser.Term.do
          then .text " " ++ bodyDoc
          else .group (.nest 2 (.line ++ bodyDoc))
        let armDoc := .text "| " ++ patDoc ++ .text " =>" ++ bodyPart
        armsDoc := armsDoc ++ (if first then .nil else .hardline) ++ armDoc
        first := false
      return .text head ++ .hardline ++ armsDoc
    else if kind.toString == "termDepIfThenElse" then
      -- [if, binderIdent, :, cond, then, thenBranch, else, elseBranch] — the
      -- dependent `if h : c then … else …`; same layout as termIfThenElse.
      let binder ← walk (args[1]?.getD .missing)
      let cond ← walk (args[3]?.getD .missing)
      let thenB ← walk (args[5]?.getD .missing)
      let elseB ← walk (args[args.size-1]?.getD .missing)
      return .group (
        .text "if " ++ binder ++ .text " : " ++ cond ++ .text " then"
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
