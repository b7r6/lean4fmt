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

/-- Comment-bearing comma list, FORCED broken (a line comment cannot flatten,
    §0.4): one element per line at +2, each element's leading comment/blank
    lines placed structurally, the same-line comment after each COMMA (its
    trailing) re-appended, the last element's same-line trailing kept before
    the closer. `none` (caller verbatims) when the closer's leading carries
    content, a trailing spans lines, or a seam has no home. -/
private def seamCommaList?
            (walk : Walk)
            (l r : String)
            (pairs : Array (Lean.Syntax × Option Lean.Syntax))
            (closer : Lean.Syntax)
            : EmitM (Option Doc) := do
  if pairs.isEmpty then return none
  -- comments directly before the closer have no seam yet
  let isWs (t : String) : Bool := t.all (fun c => c == ' ' || c == '\t')
  let closerLead := (Lean4Fmt.Syntax.leading? closer).getD ""
  if !(((closerLead.splitOn "\n").drop 1).dropLast.all isWs) then return none
  if !isWs ((closerLead.splitOn "\n").headD "") then return none
  let mut body : Doc := .nil
  for h : i in [0:pairs.size] do
    let (e, comma?) := pairs[i]
    let last := i + 1 == pairs.size
    let some sep := Lean4Fmt.Emit.leadingSep? ((Lean4Fmt.Syntax.leading? e).getD "")
      | return none
    let eDoc ← walk e
    -- the same-line comment can trail the ELEMENT (comma-leading style:
    -- `e  -- note` with `, e₂` on the next line) or the COMMA (`e, -- note`);
    -- own both zones. Content in a comma's own LEADING has no seam — bail.
    let eTrail := ((Lean4Fmt.Syntax.trailing? e).getD "").trimAscii.toString
    let cTrail ← do
      match comma? with
      | some c =>
        let isWsC (t : String) : Bool := t.all (fun ch => ch == ' ' || ch == '\t')
        let cl := (Lean4Fmt.Syntax.leading? c).getD ""
        if !(((cl.splitOn "\n").drop 1).dropLast.all isWsC) then return none
        pure (((Lean4Fmt.Syntax.trailing? c).getD "").trimAscii.toString)
      | none => pure ""
    let trailT := String.intercalate " " (([eTrail, cTrail].filter (fun t => !t.isEmpty)))
    if trailT.any (· == '\n') then return none
    -- when the comma is the LAST element's trailing zone owner, drop through:
    let _ := ()
    let commaD : Doc := if last then .nil else .text ","
    let trailD : Doc := if trailT.isEmpty then .nil else .text (" " ++ trailT)
    body := body ++ sep ++ eDoc ++ commaD ++ trailD
  return some (.text l ++ .nest 2 body ++ .hardline ++ .text r)

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
  -- seam-owning kinds bypass this guard (Kinds.ownsSeams): their arms place
  -- inter-item comments structurally; anything they can't hold falls back
  -- internally.
  if !Lean4Fmt.Syntax.ownsSeams stx.getKind
      && Lean4Fmt.Syntax.hasOwnedLineComment stx then
    return (← verbatim stx)
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
      let children := (args[1]?.map (·.getArgs)).getD #[]
      if Lean4Fmt.Syntax.interiorHasLineComment stx then
        let mut pairs : Array (Lean.Syntax × Option Lean.Syntax) := #[]
        for c in children do
          if c.isAtom then
            if !pairs.isEmpty then
              pairs := pairs.set! (pairs.size - 1) (pairs[pairs.size - 1]!.1, some c)
          else pairs := pairs.push (c, none)
        match ← seamCommaList? walk "⟨" "⟩" pairs (args[2]?.getD .missing) with
        | some d => return d
        | none => return (← verbatim stx)
      return (← commaGroup walk "⟨" "⟩" children)
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
    else if kind.toString == "«term[_]»" || kind.toString == "«term#[_,]»" then
      let l := if kind.toString == "«term[_]»" then "[" else "#["
      let children := (args[1]?.map (·.getArgs)).getD #[]
      if Lean4Fmt.Syntax.interiorHasLineComment stx then
        let mut pairs : Array (Lean.Syntax × Option Lean.Syntax) := #[]
        for c in children do
          if c.isAtom then
            if !pairs.isEmpty then
              pairs := pairs.set! (pairs.size - 1) (pairs[pairs.size - 1]!.1, some c)
          else pairs := pairs.push (c, none)
        match ← seamCommaList? walk l "]" pairs (args[2]?.getD .missing) with
        | some d => return d
        | none => return (← verbatim stx)
      return (← commaGroup walk l "]" children)
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
      -- The CHAIN arm: unroll `let a := x; let b := y; body` into a vertical
      -- sequence of binding lines + the final body, each at the SAME indent
      -- (Lean let-chains don't nest). The loop OWNS the inter-binding trivia
      -- (the seam model): comment/blank lines between bindings place
      -- structurally, same-line trailing comments re-append; a comment INSIDE
      -- a binding verbatims that one binding (its span carries the comment).
      -- The chain's outer leading/trailing belong to the enclosing seam.
      let mut d : Doc := .nil
      let mut cur := stx
      let mut first := true
      let mut steps := 0
      while cur.getKind == ``Lean.Parser.Term.let && steps < 10000 do
        steps := steps + 1
        let a := cur.getArgs
        if a.size < 5 then return (← verbatim stx)
        let lead := (Lean4Fmt.Syntax.leading? cur).getD ""
        if !first then
          let some sep := Lean4Fmt.Emit.leadingSep? lead | return (← verbatim stx)
          d := d ++ sep
        else
          -- the chain's head leading (between `:=` and the first `let`) is
          -- OURS when it carries comment lines — the enclosing seam only
          -- provides the line break. Plain whitespace stays the caller's.
          let isWs (l : String) : Bool := l.all (fun c => c == ' ' || c == '\t')
          if !(((lead.splitOn "\n").drop 1).dropLast.all isWs) then
            let some sep := Lean4Fmt.Emit.leadingSep? lead | return (← verbatim stx)
            d := d ++ sep
        first := false
        let cfgT := (((a[1]?.map bareSrc).getD "").trimAscii.toString)
        if cfgT.any (· == '\n') then return (← verbatim stx)
        let decl := a[2]?.getD .missing
        let declDoc ← walk decl
        let sepT := (((a[3]?.map bareSrc).getD "").trimAscii.toString)
        if sepT.any (· == '\n') then return (← verbatim stx)
        -- same-line trailing comment on the binding (the gap to the next
        -- binding's leading is the seam above)
        let trailT := ((Lean4Fmt.Syntax.trailing? decl).getD "").trimAscii.toString
        if trailT.any (· == '\n') then return (← verbatim stx)
        let cfgDoc : Doc := if cfgT.isEmpty then .nil else .text cfgT ++ .space
        d := d ++ .text "let " ++ cfgDoc ++ declDoc ++ .text sepT
          ++ (if trailT.isEmpty then Doc.nil else .text (" " ++ trailT))
        cur := a[a.size-1]?.getD .missing
      -- the final body: its leading is the last seam the chain owns
      let some bodySep := Lean4Fmt.Emit.leadingSep? ((Lean4Fmt.Syntax.leading? cur).getD "")
        | return (← verbatim stx)
      let bodyDoc ← walk cur
      return d ++ bodySep ++ bodyDoc
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
      let mut armsPlain : Doc := .nil   -- the classic first-nil/hardline join, for the §7 grid fallback
      let mut aligned : Array (Doc × Option Doc) := #[]
      let mut plainArms := true
      for h : i in [0:alts.size] do
        let alt := alts[i]
        -- a comment INSIDE the arm (pattern/body interior) — whole-match verbatim
        if Lean4Fmt.Syntax.interiorHasLineComment alt then return (← verbatim stx)
        let lead := (Lean4Fmt.Syntax.leading? alt).getD ""
        let some sep := Lean4Fmt.Emit.leadingSep? lead | return (← verbatim stx)
        let plainSep := ((lead.splitOn "\n").drop 1).dropLast.isEmpty
        let trailT := ((Lean4Fmt.Syntax.trailing? alt).getD "").trimAscii.toString
        let last := i + 1 == alts.size
        if !last && trailT.any (· == '\n') then return (← verbatim stx)
        let trailDoc : Doc := if !last && !trailT.isEmpty then .text (" " ++ trailT) else .nil
        if !plainSep || (!last && !trailT.isEmpty) then plainArms := false
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
        armsDoc := armsDoc ++ sep ++ armDoc ++ trailDoc
        armsPlain := armsPlain ++ (if i == 0 then Doc.nil else .hardline) ++ armDoc
        let inlineOk := body.getKind != ``Lean.Parser.Term.do
          && !Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc
        aligned := aligned.push (patDoc, if inlineOk then some bodyDoc else none)
      let al := (← read).alignment
      -- the aligned grid only for a comment-free, blank-free arm set (a grid
      -- with foreign lines interleaved reads worse than no grid)
      if plainArms then
        return .text head ++ .hardline
          ++ armsAligned al.matchArms al.maxDelta aligned armsPlain
      return .text head ++ armsDoc
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
    else if kind == ``Lean.Parser.Term.fun then
      -- `fun x (y : τ) => body` — ["fun", basicFun [binders, type?, "=>", body]].
      -- Binders as active text (trimmed, single-spaced), the body walked: flat
      -- on the `=>` line when it fits, else on the next line at +2; a `do` body
      -- glues (its statements bring their own hardline). The `fun | pat => …`
      -- match-alternative form stays verbatim.
      let some bf := args[1]? | return (← verbatim stx)
      if bf.getKind != ``Lean.Parser.Term.basicFun then return (← verbatim stx)
      let ba := bf.getArgs
      if ba.size != 4 then return (← verbatim stx)
      let mut head := "fun"
      for b in ((ba[0]?).map (·.getArgs)).getD #[] do
        let t := (bareSrc b).trimAscii.toString
        if t.isEmpty || t.any (· == '\n') then return (← verbatim stx)
        head := head ++ " " ++ t
      let tyT := ((ba[1]?.map bareSrc).getD "").trimAscii.toString
      if tyT.any (· == '\n') then return (← verbatim stx)
      if !tyT.isEmpty then head := head ++ " " ++ tyT
      let body := ba[3]!
      let bodyDoc ← walk body
      if Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc then return (← verbatim stx)
      if body.getKind == ``Lean.Parser.Term.do then
        return .text (head ++ " => ") ++ bodyDoc
      return .text (head ++ " =>") ++ .group (.nest 2 (.line ++ bodyDoc))
    else if kind == ``Lean.Parser.Term.tuple then
      -- `(a, b, c)` — [hygienicLParen, elems, ")"] where elems RIGHT-NEST:
      -- null[e, ",", null[e₂, ",", e₃]] with the innermost tail a bare term.
      -- Flatten, walk each element, and lay out as the standard commaList.
      let mut elems : Array Lean.Syntax := #[]
      let mut cur := args[1]?.getD .missing
      let mut steps := 0
      while cur.getKind == `null && cur.getArgs.size == 3 && steps < 1000 do
        elems := elems.push cur.getArgs[0]!
        cur := cur.getArgs[2]!
        steps := steps + 1
      if cur.getKind == `null && cur.getArgs.size == 1 then cur := cur.getArgs[0]!
      if elems.isEmpty then return (← verbatim stx)
      elems := elems.push cur
      let mut ds : Array Doc := #[]
      for e in elems do ds := ds.push (← walk e)
      return Lean4Fmt.Doc.commaList "(" ")" ds
    else if kind == ``Lean.Parser.Term.forall then
      -- [∀|forall, binders, opt, ",", body] — head token-for-token (the
      -- quantifier atom keeps its source spelling), the body walked: flat
      -- after the comma when it fits, else on the next line at
      -- continuationIndent (quantifier bodies read as continuations)
      if args.size != 5 then return (← verbatim stx)
      let mut head := (bareSrc args[0]!).trimAscii.toString
      if head.isEmpty then return (← verbatim stx)
      for b in args[1]!.getArgs do
        let t := (bareSrc b).trimAscii.toString
        if t.isEmpty || t.any (· == '\n') then return (← verbatim stx)
        head := head ++ " " ++ t
      let optT := (bareSrc args[2]!).trimAscii.toString
      if optT.any (· == '\n') then return (← verbatim stx)
      if !optT.isEmpty then head := head ++ " " ++ optT
      let bodyDoc ← walk args[4]!
      if Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc then return (← verbatim stx)
      let cont := (← read).layout.continuationIndent
      return .text (head ++ ",") ++ .group (.nest cont (.line ++ bodyDoc))
    else if kind == ``Lean.Parser.Term.hole then
      return .text "_"
    else if kind == `str || kind == `num || kind == `scientific || kind == `char then
      return (← verbatim stx)      -- literal: reproduce exactly
    else
      return (← verbatim stx)      -- not yet ported (let/match/do/if/…): opaque
  | .missing => return .nil

end Lean4Fmt.Emit.Term
