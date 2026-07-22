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
import Lean4Fmt.Emit.Tokens
import Lean4Fmt.Emit.Binders
import Lean4Fmt.Syntax.Kinds
import Lean4Fmt.Syntax.Trivia
import Lean4Fmt.Syntax.Query

namespace Lean4Fmt.Emit.Term

open Lean Lean4Fmt.Doc Lean4Fmt.Emit

/-- Width-aware bracketed comma list `l e₁, e₂, … r`: flat if it fits, else one
    element per line indented by 2 with `l`/`r` on their own lines (the standard
    all-or-nothing `commaList` group). Skips the parser's comma atoms. -/
private def commaGroup
            (walk : Walk)
            (l r : String)
            (children : Array Lean.Syntax)
            : EmitM (Option Doc) := do

  -- an authored TRAILING comma (`[a, b,]`) has no slot in the rebuilt list
  -- (commas go BETWEEN items) — `none` rather than drop the token
  -- (gate-caught on aleph CLI.lean, tokens; the listItems? lesson again)
  if (children.back?.map (fun c =>
      c.isAtom && (bareSrc c).trimAscii.toString == ",")).getD false then
    return none
  let mut ds : Array Doc := #[]
  for c in children do
    if c.isAtom then continue
    ds := ds.push (← walk c)
  -- literal pools (§5 fill): many short flat items — byte tables, opcode
  -- lists — pack and wrap at the width instead of exploding one per line
  if ds.size ≥ 8 && ds.all (fun d => ((Lean4Fmt.Doc.flatWidth d).getD 1000) ≤ 12) then
    let items :=
      ((Array.range ds.size).map
        (fun i => ds[i]! ++ (if i + 1 == ds.size then Doc.nil else Doc.text ","))).toList
    return some (.text l ++ .nest 2 (Doc.fillSep items) ++ .text r)
  return some (Lean4Fmt.Doc.commaList l r ds)

/-- Comment-bearing comma list, FORCED broken (a line comment cannot flatten,
    §0.4): one element per line at +2, each element's leading comment/blank
    lines placed structurally, the same-line comment after each COMMA (its
    trailing) re-appended, the last element's same-line trailing kept before
    the closer. `none` (caller verbatims) when the closer's leading carries
    content, a trailing spans lines, or a seam has no home. -/
private def seamCommaList?
            (walk : Walk)
            (l r : String)
            (opener : Lean.Syntax)
            (pairs : Array (Lean.Syntax × Option Lean.Syntax))
            (closer : Lean.Syntax)
            : EmitM (Option Doc) := do

  if pairs.isEmpty then return none
  -- a comment on the opener's own line (`[ -- note`) is OUR zone
  let openTrail := ((Lean4Fmt.Syntax.trailing? opener).getD "").trimAscii.toString
  if openTrail.any (· == '\n') then return none
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
    -- inter-element comments in LEADING-COMMA style live in the COMMA's
    -- leading full lines — own them via the seam kit (placed after this
    -- element's comma, before the next element; pend collapse merges the
    -- separators). Plain whitespace comma-leading contributes nothing.
    let mut commaLeadSep : Doc := .nil
    let cTrail ← do
      match comma? with
      | some c =>
        let isWsC (t : String) : Bool := t.all (fun ch => ch == ' ' || ch == '\t')
        let cl := (Lean4Fmt.Syntax.leading? c).getD ""
        if !(((cl.splitOn "\n").drop 1).dropLast.all isWsC) then
          match Lean4Fmt.Emit.leadingSep? cl with
          | some d => commaLeadSep := d
          | none => return none
        pure (((Lean4Fmt.Syntax.trailing? c).getD "").trimAscii.toString)
      | none => pure ""
    let trailT := String.intercalate " " (([eTrail, cTrail].filter (fun t => !t.isEmpty)))
    if trailT.any (· == '\n') then return none
    -- when the comma is the LAST element's trailing zone owner, drop through:
    let _ := ()
    let commaD : Doc := if last then .nil else .text ","
    let trailD : Doc := if trailT.isEmpty then .nil else .text (" " ++ trailT)
    body := body ++ sep ++ eDoc ++ commaD ++ trailD ++ commaLeadSep
  let openD : Doc := if openTrail.isEmpty then .nil else .text (" " ++ openTrail)
  return some (.text l ++ openD ++ .nest 2 body ++ .hardline ++ .text r)

/-- A single `structInstField` = [structInstLVal, «rest»]. The LVal (field name /
    path) is reproduced verbatim; the value (the term after `:=`, found inside the
    `structInstFieldDef` in «rest») is walked so it lays out actively. A shorthand
    field `{ x }` (no `:=`) is just its LVal. -/
private partial def structFieldDoc
                    (walk : Walk)
                    (field : Lean.Syntax)
                    : EmitM Doc := do

  let fa := field.getArgs
  let lvalStx := fa[0]?.getD .missing
  let lvalT := bareSrc lvalStx
  let lval ← if !lvalT.isEmpty && !lvalT.any (· == '\n') then
      pure (Doc.text (Lean4Fmt.Emit.canonTok lvalStx))
    else verbatim lvalStx
  let rest := (fa[1]?.getD Lean.Syntax.missing).getArgs
  let fd? := rest.find? (·.getKind == ``Lean.Parser.Term.structInstFieldDef)
  match fd? with
  | some fd =>
    let da := fd.getArgs
    let v := da[da.size - 1]?.getD Lean.Syntax.missing -- [":=", null?, value]
    -- a field with BINDERS or type ascription (`symm _ _ h := …`) carries
    -- tokens between the lval and the value — the lval++":="++value shape
    -- would DELETE them (gate-caught on mathlib): token-exact join instead
    let expected := Lean4Fmt.Syntax.leafToks lvalStx ++ #[":="] ++ Lean4Fmt.Syntax.leafToks v
    if Lean4Fmt.Syntax.leafToks field != expected then
      let t := Lean4Fmt.Emit.canonTok field
      if t.isEmpty || t.any (· == '\n') then return (← verbatim field)
      return .text t
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
      && Lean4Fmt.Syntax.hasUnownedLineComment stx then
    return (← verbatim stx)
  match stx with
  | .atom _ v => return .text v
  | .ident _ _ n _ => return .text n.toString
  | .node _ kind args =>
    -- binary operator: lhs ␣ op ␣ rhs. `Term.arrow` is the same 3-slot shape
    -- (the atom carries the source spelling — `→` or `->` — and the token gate
    -- cares, so it rides through the walk as-is).
    if (Lean4Fmt.Syntax.isBinOp kind || kind == ``Lean.Parser.Term.arrow) && args.size == 3 then
      -- `lhs op rhs` — width-aware: flat if it fits, else break BEFORE the
      -- operator (operator leads the continuation line). A CHAIN of the same
      -- operator flattens to ONE continuation indent (no staircase):
      --   a = true
      --       ∧ b = true
      --       ∧ c = true
      -- comment hazard: the chain reflow walks its pieces BARE — a line
      -- comment in a piece's leading has no seam here and would silently
      -- drop (gate-caught on mathlib ContextInfo: comments inside a nested
      -- `<|` chain). Whole-chain verbatim carries it byte-exact.
      if Lean4Fmt.Syntax.interiorHasLineComment stx then
        return (← verbatim stx "chain-comment")
      let lhs ← walk args[0]!
      let op ← walk args[1]!
      let mut tail : Doc := .nil
      let mut cur := args[2]!
      let mut steps := 0
      while cur.getKind == kind && cur.getArgs.size == 3 && steps < 64 do
        let ca := cur.getArgs
        tail := tail ++ .line ++ op ++ .space ++ (← walk ca[0]!)
        cur := ca[2]!
        steps := steps + 1
      let rhs ← walk cur
      -- ws-sensitivity (fixed-point class): a multi-line RE-ANCHORING piece
      -- glued mid-chain re-indents its interior by its placement column,
      -- which the previous pass just moved — never a fixed point. A base-0
      -- (mid-line-anchored) verbatim is the worst case: its interior indent
      -- ADDS to the placement (gate-caught on mathlib Abel: `pure <| ←` +
      -- app drifted +8 per pass). Whole-chain verbatim; porting the piece's
      -- kind is the coverage fix, this is the correctness floor.
      if Lean4Fmt.Doc.hasMultilineReanchor lhs || Lean4Fmt.Doc.hasMultilineReanchor op
          || Lean4Fmt.Doc.hasMultilineReanchor tail
          || Lean4Fmt.Doc.hasMultilineReanchor rhs then
        return (← verbatim stx "chain-multiline-piece")
      let cont := (← read).layout.continuationIndent
      if (← read).breaking.opBreak == .trailing then
        -- trailing operators (mathlib arrows): `a →\n  b →\n  c`. Flat form
        -- identical to the leading build — only the broken shape differs.
        let mut tailT : Doc := .nil
        let mut cur2 := args[2]!
        let mut steps2 := 0
        while cur2.getKind == kind && cur2.getArgs.size == 3 && steps2 < 64 do
          let ca := cur2.getArgs
          tailT := tailT ++ .line ++ (← walk ca[0]!) ++ .space ++ op
          cur2 := ca[2]!
          steps2 := steps2 + 1
        return .group (lhs ++ .space ++ op ++ .nest cont (tailT ++ .line ++ rhs))
      return .group (lhs ++ .nest cont (tail ++ .line ++ op ++ .space ++ rhs))
    else if kind == ``Lean.Parser.Term.app then
      -- `fn a b c` — width-aware: flat if it fits, else `fn` on its line with each
      -- argument on a continuation line indented by `layout.indent`. All-or-
      -- nothing (a `group`): the source did not dictate this, the width does.
      let fn := args[0]!
      let argList := (args[1]?.map (·.getArgs)).getD #[]
      let ind := (← read).layout.indent
      let fnDoc ← walk fn
      if Lean4Fmt.Syntax.interiorHasLineComment stx then
        -- comment-bearing application: forced broken, one argument per line,
        -- per-argument seams (leading comment lines placed, same-line trailing
        -- comments re-appended; the LAST argument's trailing is the enclosing
        -- seam's)
        if Lean4Fmt.Syntax.interiorHasLineComment fn then return (← verbatim stx)
        let mut argsDoc : Doc := .nil
        for h : i in [0:argList.size] do
          let a := argList[i]
          let last := i + 1 == argList.size
          let some sep := Lean4Fmt.Emit.leadingSep? ((Lean4Fmt.Syntax.leading? a).getD "")
            | return (← verbatim stx)
          let trailT := ((Lean4Fmt.Syntax.trailing? a).getD "").trimAscii.toString
          if !last && trailT.any (· == '\n') then return (← verbatim stx)
          let trailD : Doc := if !last && !trailT.isEmpty then .text (" " ++ trailT) else .nil
          argsDoc := argsDoc ++ sep ++ (← walk a) ++ trailD
        return fnDoc ++ .nest ind argsDoc
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
        match ← seamCommaList? walk "⟨" "⟩" (args[0]?.getD .missing) pairs (args[2]?.getD .missing) with
        | some d => return d
        | none => return (← verbatim stx)
      match ← commaGroup walk "⟨" "⟩" children with
      | some d => return d
      | none => return (← verbatim stx "trailing-comma")
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
      -- the UPDATE form `{ src with fields }`: the source segment joins
      -- canonically (`p with`); comment-bearing and grid paths stay
      -- conservative (plain group only)
      let srcT := if srcEmpty then "" else Lean4Fmt.Emit.canonTok (args[1]?.getD .missing)
      if srcT.any (· == '\n') || !ellipsisEmpty then return (← verbatim stx)
      -- a `: T` ascription (any content between the ellipsis slot and the
      -- closer) has no active placement — dropping it DELETED tokens
      for i in [4:args.size - 1] do
        if !((args[i]?.map bareSrc).getD "").trimAscii.toString.isEmpty then
          return (← verbatim stx)
      let mut fields : Array Lean.Syntax := #[]
      let mut pairs : Array (Lean.Syntax × Option Lean.Syntax) := #[]
      let mut commas := 0
      for g in ((args[2]?.map (·.getArgs)).getD #[]) do
        for c in g.getArgs do
          if c.getKind == ``Lean.Parser.Term.structInstField then
            fields := fields.push c
            pairs := pairs.push (c, none)
          else if c.isAtom && bareSrc c == "," then
            commas := commas + 1
            if !pairs.isEmpty then
              pairs := pairs.set! (pairs.size - 1) (pairs[pairs.size - 1]!.1, some c)
      if fields.isEmpty then return (← verbatim stx)
      if fields.size > 1 && commas + 1 != fields.size then return (← verbatim stx)  -- newline-separated
      if Lean4Fmt.Syntax.interiorHasLineComment stx then
        if !srcT.isEmpty then return (← verbatim stx)
        -- comment-bearing record: forced broken, per-field seams
        match ← seamCommaList? walk "{" "}" (args[0]?.getD .missing) pairs (args[args.size - 1]?.getD .missing) with
        | some d => return d
        | none => return (← verbatim stx)
      let mut ds : Array Doc := #[]
      for f in fields do ds := ds.push (← structFieldDoc walk f)
      let groupForm : Doc := if srcT.isEmpty then
          .group (.text "{ " ++ .nest 2 (Lean4Fmt.Doc.sepBy (.text "," ++ .line) ds) ++ .text " }")
        else
          -- `{ src with` rides the opener; fields below at +2 when broken
          .group (.text ("{ " ++ srcT) ++ .nest 2 (.line
            ++ Lean4Fmt.Doc.sepBy (.text "," ++ .line) ds) ++ .text " }")
      -- §7 recordFields: the broken form as an aligned grid — `{ `/`  ` ride in
      -- the first column so the grid IS the hanging house style; flat still
      -- wins when it fits (the renderer prefers a flat-capable fallback).
      let al := (← read).alignment
      if srcT.isEmpty && al.recordFields != Lean4Fmt.Style.AlignMode.never && fields.size ≥ 2 then
        let mut rows : List (List Doc) := []
        let mut ok := true
        for h : i in [0:fields.size] do
          let fa := fields[i]!.getArgs
          let lvalT := Lean4Fmt.Emit.canonTok (fa[0]?.getD .missing)
          if lvalT.isEmpty || lvalT.any (· == '\n') then ok := false
          let rest := (fa[1]?.getD Lean.Syntax.missing).getArgs
          match rest.find? (·.getKind == ``Lean.Parser.Term.structInstFieldDef) with
          | some fd =>
            let v := (fd.getArgs[fd.getArgs.size - 1]?).getD Lean.Syntax.missing
            let vDoc ← walk v
            if (Lean4Fmt.Doc.flatWidth vDoc).isNone then ok := false
            let last := i + 1 == fields.size
            rows := rows ++
              [[Doc.text ((if i == 0 then "{ " else "  ") ++ lvalT), Doc.text ":=",
                vDoc ++ Doc.text (if last then " }" else ",")]]
          | none => ok := false
        if ok then
          let cap := if al.recordFields == Lean4Fmt.Style.AlignMode.always
            then 1000000 else al.maxDelta
          return Doc.alignOr { sep := " ", maxDelta := cap } rows groupForm
      return groupForm
    else if kind == Lean4Fmt.Syntax.listLitKind || kind == Lean4Fmt.Syntax.arrayLitKind then
      let l := if kind == Lean4Fmt.Syntax.listLitKind then "[" else "#["
      let children := (args[1]?.map (·.getArgs)).getD #[]
      if Lean4Fmt.Syntax.interiorHasLineComment stx then
        let mut pairs : Array (Lean.Syntax × Option Lean.Syntax) := #[]
        for c in children do
          if c.isAtom then
            if !pairs.isEmpty then
              pairs := pairs.set! (pairs.size - 1) (pairs[pairs.size - 1]!.1, some c)
          else pairs := pairs.push (c, none)
        match ← seamCommaList? walk l "]" (args[0]?.getD .missing) pairs (args[2]?.getD .missing) with
        | some d => return d
        | none => return (← verbatim stx)
      match ← commaGroup walk l "]" children with
      | some d => return d
      | none => return (← verbatim stx "trailing-comma")
    else if kind == Lean4Fmt.Syntax.iteKind then
      -- [if, cond, then, thenBranch, else, elseBranch]; a width-aware group:
      -- flat `if c then a else b`, or broken with 2-space branches, `else` at
      -- the if's base column (§ active layout). Branches recurse via `walk`.
      -- An interior slot whose TAIL carries a comment (`… then x -- note` before
      -- `else`) has no seam in this layout — verbatim keeps it. (The entry
      -- guard can't see it: the comment hides in an ownsSeams subtree whose
      -- own emitter treats its tail trailing as the PARENT's zone.)
      for slot in [args[1]?, args[3]?] do
        let t := ((slot.bind Lean4Fmt.Syntax.lastTokenTrailing?).getD "").trimAscii.toString
        if !t.isEmpty then return (← verbatim stx)
      -- a full-line comment in a BRANCH's leading (`else⏎  -- note⏎  body`)
      -- has no seam in this layout either — the branch walk drops leading
      -- trivia (gate-caught on evring HttpConn, comments class)
      for slot in [args[3]?, args[5]?] do
        if Lean4Fmt.Syntax.countLineComments ((slot.bind Lean4Fmt.Syntax.leading?).getD "") > 0 then
          return (← verbatim stx "ite-branch-leading-comment")
      let cond ← walk (args[1]?.getD .missing)
      let thenB ← walk (args[3]?.getD .missing)
      let elseB ← walk (args[5]?.getD .missing)
      -- else-if CHAIN (breaking.elseIfChain): a nested ite glues after `else`
      let elseIsIte := (args[5]?.map (fun e =>
        e.getKind == Lean4Fmt.Syntax.iteKind || e.getKind == Lean4Fmt.Syntax.diteKind)).getD false
      let elseTail : Doc := if (← read).breaking.elseIfChain && elseIsIte
        then .text "else " ++ elseB
        else .text "else" ++ .nest 2 (.line ++ elseB)
      return .group (
        .text "if " ++ cond ++ .text " then"
          ++ .nest 2 (.line ++ thenB)
          ++ .line ++ elseTail)
    else if kind == ``Lean.Parser.Term.let || kind == ``Lean.Parser.Term.have then
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
      -- have chains like let (same shape: [kw, letConfig, letDecl, …, body])
      -- and the two INTERLEAVE (`have h := …` then `let x := …`)
      while (cur.getKind == ``Lean.Parser.Term.let
          || cur.getKind == ``Lean.Parser.Term.have) && steps < 10000 do
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
        -- ws-sensitivity (fixed-point master class): the binding glues after
        -- `let ` mid-line — a multi-line re-anchoring declDoc drifts by its
        -- placement column (gate-caught on SSP/Trust.Protocol home files:
        -- comma-less structInst values, +4/pass). Whole-chain verbatim keeps
        -- the source's column alignment byte-exact.
        if Lean4Fmt.Doc.hasMultilineReanchor declDoc then
          return (← verbatim stx "let-multiline-binding")
        let sepT := (((a[3]?.map bareSrc).getD "").trimAscii.toString)
        if sepT.any (· == '\n') then return (← verbatim stx)
        -- same-line trailing comment on the binding (the gap to the next
        -- binding's leading is the seam above)
        let trailT := ((Lean4Fmt.Syntax.trailing? decl).getD "").trimAscii.toString
        if trailT.any (· == '\n') then return (← verbatim stx)
        let cfgDoc : Doc := if cfgT.isEmpty then .nil else .text cfgT ++ .space
        let kwT := (bareSrc (a[0]?.getD .missing)).trimAscii.toString
        if kwT.isEmpty then return (← verbatim stx)
        d := d ++ .text (kwT ++ " ") ++ cfgDoc ++ declDoc ++ .text sepT
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
      let headParts := ((args.extract 0 3).map Lean4Fmt.Emit.canonTok).filter
        (fun s => !s.isEmpty)
      let head := String.intercalate " " headParts.toList
      if head.isEmpty || head.any (· == '\n') then return (← verbatim stx)
      let v := args[4]!
      let vdoc ← walk v
      -- by glues like do (`h : T := by` + tactics below — the sequence-seam
      -- invariant tolerates interior verbatims); other kinds keep the bail
      if v.getKind == ``Lean.Parser.Term.do || v.getKind == ``Lean.Parser.Term.byTactic then
        return .text head ++ .text " := " ++ vdoc
      if Lean4Fmt.Doc.hasMultilineVerbatim vdoc then return (← verbatim stx)
      return .text head ++ .text " :=" ++ .group (.nest 2 (.line ++ vdoc))
    else if kind == ``Lean.Parser.Term.match then
      -- [match, motive?, motive?, discrs, "with", matchAlts]. Reproduce the head
      -- `match <discrs> with` token-for-token; lay each arm `| pat => body` on its
      -- own line at the match's indent, the body width-aware after `=>`. Patterns
      -- are walked (opaque, so a multi-line pattern trips the valDoc gate to the
      -- safe span). Guarded: any structural surprise falls back to verbatim.
      let midParts := (#[args[1]?, args[2]?, args[3]?].filterMap id).toList.filterMap
        (fun s => let t := Lean4Fmt.Emit.canonTok s; if t.isEmpty then none else some t)
      let head := "match " ++ String.intercalate " " midParts ++ " with"
      let some altsNode := args[5]? | return (← verbatim stx)
      let alts := Lean4Fmt.Emit.matchAltsOf altsNode
      if alts.isEmpty || head.any (· == '\n') then return (← verbatim stx)
      -- the shared arm loop (Emit/Monad.armPieces?): `none` = some arm is
      -- unportable (interior comment, unownable leading, mid-set multi-line
      -- trailing) — whole-match verbatim
      let some pieces ← Lean4Fmt.Emit.armPieces? walk alts | return (← verbatim stx)
      let al := (← read).alignment
      -- grids per visible-seam section (comments/blanks split; a section with
      -- a grid-ineligible arm rides plain — see armsAlignedRuns)
      return .text head ++ Lean4Fmt.Emit.armsAlignedRuns al.matchArms al.maxDelta pieces
    else if kind == Lean4Fmt.Syntax.diteKind then
      -- [if, binderIdent, :, cond, then, thenBranch, else, elseBranch] — the
      -- dependent `if h : c then … else …`; same layout as termIfThenElse,
      -- same interior-tail comment bail (no seam for `… then x -- note`).
      for slot in [args[3]?, args[5]?] do
        let t := ((slot.bind Lean4Fmt.Syntax.lastTokenTrailing?).getD "").trimAscii.toString
        if !t.isEmpty then return (← verbatim stx)
      -- and the branch-LEADING comment bail (see termIfThenElse)
      for slot in [args[5]?, args[args.size - 1]?] do
        if Lean4Fmt.Syntax.countLineComments ((slot.bind Lean4Fmt.Syntax.leading?).getD "") > 0 then
          return (← verbatim stx "ite-branch-leading-comment")
      let binder ← walk (args[1]?.getD .missing)
      let cond ← walk (args[3]?.getD .missing)
      let thenB ← walk (args[5]?.getD .missing)
      let elseB ← walk (args[args.size-1]?.getD .missing)
      -- else-if CHAIN (breaking.elseIfChain): a nested ite in the else slot
      -- glues (`else if … then`) instead of breaking to `else` + line
      let elseIsIte := (args[args.size-1]?.map (fun e =>
        e.getKind == Lean4Fmt.Syntax.iteKind || e.getKind == Lean4Fmt.Syntax.diteKind)).getD false
      let elseTail : Doc := if (← read).breaking.elseIfChain && elseIsIte
        then .text "else " ++ elseB
        else .text "else" ++ .nest 2 (.line ++ elseB)
      return .group (
        .text "if " ++ binder ++ .text " : " ++ cond ++ .text " then"
          ++ .nest 2 (.line ++ thenB)
          ++ .line ++ elseTail)
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
      -- the keyword token from SOURCE: `fun` and `λ` are distinct tokens and
      -- the gate cares (found on Pantograph — hardcoding "fun" ate every `λ`)
      let mut head := (bareSrc args[0]!).trimAscii.toString
      if head.isEmpty then return (← verbatim stx)
      for b in ((ba[0]?).map (·.getArgs)).getD #[] do
        let t := Lean4Fmt.Emit.canonTok b
        if t.isEmpty || t.any (· == '\n') then return (← verbatim stx)
        head := head ++ " " ++ t
      let tyT := (ba[1]?.map Lean4Fmt.Emit.canonTok).getD ""
      if tyT.any (· == '\n') then return (← verbatim stx)
      if !tyT.isEmpty then head := head ++ " " ++ tyT
      -- arrow spelling from SOURCE (`=>` vs `↦` — same lesson as fun/λ above)
      let arrowT := (bareSrc ba[2]!).trimAscii.toString
      let arrowT := if arrowT.isEmpty then "=>" else arrowT
      let body := ba[3]!
      let bodyDoc ← walk body
      if Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc then return (← verbatim stx)
      if body.getKind == ``Lean.Parser.Term.do then
        return .text (head ++ " " ++ arrowT ++ " ") ++ bodyDoc
      return .text (head ++ " " ++ arrowT) ++ .group (.nest 2 (.line ++ bodyDoc))
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
    else if kind == ``Lean.Parser.Term.letrec then
      -- single, plain `let rec` binding: 'let rec ' ++ decl (walked — the
      -- 5-slot letIdDecl machinery applies) ++ body at the SAME indent.
      -- Multi-decl (comma), doc/attr-bearing, or suffix-bearing recs verbatim.
      if args.size != 4 then return (← verbatim stx)
      let kwT := (bareSrc args[0]!).trimAscii.toString
      if kwT.any (· == '\n') then return (← verbatim stx)
      let decls := ((args[1]!.getArgs[0]?).map (·.getArgs)).getD #[]
      if decls.size != 1 then return (← verbatim stx)
      let rd := decls[0]!
      if rd.getKind != ``Lean.Parser.Term.letRecDecl || rd.getArgs.size != 4 then
        return (← verbatim stx)
      if !(bareSrc rd.getArgs[0]!).trimAscii.toString.isEmpty then return (← verbatim stx)
      if !(bareSrc rd.getArgs[1]!).trimAscii.toString.isEmpty then return (← verbatim stx)
      if !(bareSrc rd.getArgs[3]!).trimAscii.toString.isEmpty then return (← verbatim stx)
      let declDoc ← walk rd.getArgs[2]!
      if Lean4Fmt.Doc.hasMultilineVerbatim declDoc then return (← verbatim stx)
      let sepT := (((args[2]?.map bareSrc).getD "").trimAscii.toString)
      if sepT.any (· == '\n') then return (← verbatim stx)
      let body := args[3]!
      let some bodySep := Lean4Fmt.Emit.leadingSep? ((Lean4Fmt.Syntax.leading? body).getD "")
        | return (← verbatim stx)
      let bodyDoc ← walk body
      return .text (kwT ++ " ") ++ declDoc ++ .text sepT ++ bodySep ++ bodyDoc
    else if kind == ``Lean.Parser.Term.forall then
      -- [∀|forall, binders, opt, ",", body] — head token-for-token (the
      -- quantifier atom keeps its source spelling), the body walked: flat
      -- after the comma when it fits, else on the next line at
      -- continuationIndent (quantifier bodies read as continuations)
      if args.size != 5 then return (← verbatim stx)
      let kwT := (bareSrc args[0]!).trimAscii.toString
      if kwT.isEmpty then return (← verbatim stx)
      let mut hd : Doc := .text kwT
      for b in args[1]!.getArgs do
        let bd ← Lean4Fmt.Emit.binderDoc walk b   -- multi-line types walk
        if Lean4Fmt.Doc.hasMultilineVerbatim bd then return (← verbatim stx)
        hd := hd ++ .space ++ bd
      let optT := (bareSrc args[2]!).trimAscii.toString
      if optT.any (· == '\n') then return (← verbatim stx)
      if !optT.isEmpty then hd := hd ++ .text (" " ++ optT)
      let bodyDoc ← walk args[4]!
      if Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc then return (← verbatim stx)
      let cont := (← read).layout.continuationIndent
      return hd ++ .text "," ++ .group (.nest cont (.line ++ bodyDoc))
    else if kind == `Lean.«term∀__,_» || kind == `Lean.«term∃__,_»
        || kind == `«term∃_,_» || kind == `«term∀_,_» then
      -- binder-predicate quantifiers (`∀ x ∈ s, p` / `∃ x ∈ s, p`): head
      -- tokens canonical (comma glued), body width-aware at the continuation
      let n := args.size
      if n < 2 then return (← verbatim stx)
      let mut head := ""
      for c in args.extract 0 (n - 1) do
        let t := Lean4Fmt.Emit.canonTok c
        if t.any (· == '\n') then return (← verbatim stx)
        if t == "," then head := head ++ ","
        else if !t.isEmpty then head := if head.isEmpty then t else head ++ " " ++ t
      if head.isEmpty then return (← verbatim stx)
      let bodyDoc ← walk args[n - 1]!
      if Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc then return (← verbatim stx)
      let cont := (← read).layout.continuationIndent
      return .text head ++ .group (.nest cont (.line ++ bodyDoc))
    else if kind == `«term¬_» && args.size == 2 then
      -- prefix negation over a (possibly multi-line) operand; GLUED (`¬p`,
      -- `¬(a = b)`) — the community convention, and mathlib's at 60:1
      let opT := (bareSrc args[0]!).trimAscii.toString
      if opT.isEmpty || opT.any (· == '\n') then return (← verbatim stx)
      let d ← walk args[1]!
      if Lean4Fmt.Doc.hasMultilineVerbatim d then return (← verbatim stx)
      return .text opT ++ d
    else if kind == ``Lean.Parser.Term.hole then
      return .text "_"
    else if kind == `str || kind == `num || kind == `scientific || kind == `char then
      -- literal: exact token; multi-line strings are CONTENT (quiet — not an
      -- actionable opt-out)
      let t := bareSrc stx
      if !t.isEmpty && !t.any (· == '\n') then return .text t
      return (← verbatimQuiet stx)
    else
      return (← verbatim stx)      -- not yet ported (let/match/do/if/…): opaque
  | .missing => return .nil

end Lean4Fmt.Emit.Term
