/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // EMIT // DoNotation
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Open-recursion emitter for the DoNotation category (DESIGN_V2 §11): the `do`
    block itself plus its binding statements (`doLet`, `doLetArrow`, `doReassign`,
    `doReassignArrow`, `doExpr` — their values walked so they lay out actively).

    The statement loop OWNS the inter-statement trivia (the seam model, §0.3):
    each statement's leading comment/blank lines are placed structurally before
    it (re-anchored to the statement indent), and a same-line trailing comment is
    re-appended after it — so a do-block with comments BETWEEN statements formats
    actively instead of forcing the whole value verbatim. A comment INSIDE a
    statement still reproduces that one statement verbatim (its span carries the
    comment). Everything else (`doIf`, `for`, pattern-arrow lets with an `| else`
    tail, …) reproduces verbatim, guarded by the safety gate so every
    intermediate state stays correct.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Emit.Monad
import Lean4Fmt.Emit.Tokens

namespace Lean4Fmt.Emit.DoNotation

open Lean Lean4Fmt.Doc

/-- `x (: τ)? ← v` — the monadic-bind decl inside doLetArrow / doReassignArrow.
    The arrow atom is reproduced from source (`←` or `<-` — the token gate cares);
    the value inside the `doExpr` is walked, flat on the arrow line when it fits,
    else on the next line at +2. A `do` value glues to the arrow (its body brings
    its own hardline). `none` on any structural surprise or a value carrying a
    multi-line opaque block — the caller reproduces the whole statement verbatim. -/
private
def idDeclDoc?
    (walk : Lean4Fmt.Emit.Walk)
    (d : Lean.Syntax)
    : Lean4Fmt.Emit.EmitM (Option Doc) := do
  let a := d.getArgs
  -- doIdDecl = [id, type?, "←", doExpr]; doPatDecl = [pat, type?, "←",
  -- doExpr, else?] — same arrow/expr slots; the pattern joins flat and the
  -- optional `| else` tail bails
  let head ← do
    if d.getKind == ``Lean.Parser.Term.doIdDecl then
      if a.size != 4 then return none
      let idT := Lean4Fmt.Emit.canonTok a[0]!
      let tyT := Lean4Fmt.Emit.canonTok a[1]!
      pure (String.intercalate " " ([idT, tyT].filter (fun s => !s.isEmpty)))
    else if d.getKind == ``Lean.Parser.Term.doPatDecl then
      if a.size != 5 then return none
      if !((a[4]?.map (fun s =>
          (Lean4Fmt.Emit.bareSrc s).trimAscii.toString.isEmpty)).getD true) then
        return none
      let patT := Lean4Fmt.Emit.canonTok a[0]!
      let tyT := Lean4Fmt.Emit.canonTok a[1]!
      pure (String.intercalate " " ([patT, tyT].filter (fun s => !s.isEmpty)))
    else return none
  let arrowT := (Lean4Fmt.Emit.bareSrc a[2]!).trimAscii.toString
  if head.isEmpty || head.any (· == '\n') || arrowT.any (· == '\n') then
    return none
  let ex := a[3]!
  if ex.getKind != ``Lean.Parser.Term.doExpr then
    return none
  let some v := ex.getArgs[0]? | return none
  let vdoc ← walk v
  -- a bare whole-verbatim value gains nothing; otherwise the ASSEMBLED
  -- layout decides (hasMidlineReanchor — interior verbatims at hardline
  -- seams re-anchor deterministically): a do/by/match value GLUES to the
  -- arrow (its members bring their own hardlines — `let x ← match e with`
  -- + arms below, the ApplyFun shape), anything else width-aware at +2
  if (match vdoc with | .verbatim _ _ => true | _ => false) then return none
  -- ANY multi-line value glues (`x ← cachedBuild args do`, `x ← match e
  -- with` — the house shape hangs the value head on the arrow line; its own
  -- doc breaks below); a FLAT value keeps the width-aware group (inline
  -- when it fits, else own line at +2 — unchanged)
  let glue := v.getKind == ``Lean.Parser.Term.do
    || v.getKind == ``Lean.Parser.Term.byTactic
    || v.getKind == ``Lean.Parser.Term.match
    || (Lean4Fmt.Doc.flatWidth vdoc).isNone
  let layout : Doc :=
    if glue then .text head ++ .text (" " ++ arrowT ++ " ") ++ vdoc
    else .text head ++ .text (" " ++ arrowT) ++ .group (.nest 2 (.line ++ vdoc))
  if Lean4Fmt.Doc.hasMidlineReanchor layout then return none
  return some layout

/-- The statements of a plain `doSeqIndent`, provided no item carries an explicit
    `;` terminator (walking only the statement would lose that token). `none` on
    the bracketed `{ … }` shape or any structural surprise. -/
private
def stmts? (seq : Lean.Syntax) : Option (Array Lean.Syntax) :=
  Id.run do
    if seq.getKind != ``Lean.Parser.Term.doSeqIndent then
      return none
    let mut items : Array Lean.Syntax := #[]
    for g in seq.getArgs do
      for c in g.getArgs do
        if c.getKind == ``Lean.Parser.Term.doSeqItem then items := items.push c
    if items.isEmpty then
      return none
    for it in items do
      let ia := it.getArgs
      if ia.size > 1 && !((Lean4Fmt.Emit.bareSrc (ia[ia.size-1]!)).trimAscii.toString.isEmpty) then
        return none
    return some (items.map (fun it => it.getArgs[0]?.getD Lean.Syntax.missing))

/-- The statement LINES of a sequence: each statement preceded by its structural
    leading (comments/blanks — `leadingSep?`) and followed by its same-line
    trailing comment. `lastOwned`: when true, the LAST statement's trailing
    belongs to the enclosing seam and is skipped (a whole `do`, whose do-loop
    caller re-appends it; a final if-branch, whose statement seam follows); when
    false there is NO seam for it (a then-branch before `else`) — any content
    there aborts to `none`. -/
def seqLinesDoc?
    (walk : Lean4Fmt.Emit.Walk)
    (ss : Array Lean.Syntax)
    (lastOwned : Bool)
    : Lean4Fmt.Emit.EmitM (Option Doc) := do
  let mut body : Doc := .nil
  for h : i in [0:ss.size] do
    let stmt := ss[i]
    let trailT := ((Lean4Fmt.Syntax.trailing? stmt).getD "").trimAscii.toString
    let last := i + 1 == ss.size
    if !last && trailT.any (· == '\n') then
      return none
    if last && !lastOwned && !trailT.isEmpty then
      return none
    let trailDoc : Doc := if !last && !trailT.isEmpty then .text (" " ++ trailT) else .nil
    let lead := (Lean4Fmt.Syntax.leading? stmt).getD ""
    -- FIRST statement: a comment-free blank run between the block opener and
    -- the first statement is LAYOUT, not content — drop it and let the style
    -- re-add its own (bodyOwnLine/glueBodyBlank). Without this, one style's
    -- injected blank reads as content to the next (the wash-test leak).
    let sep ← if i == 0 && lead.toList.all (·.isWhitespace) then pure Doc.hardline
      else match Lean4Fmt.Emit.leadingSep? lead with
        | some s => pure s
        | none => return none
    let sDoc ← walk stmt
    body := body ++ sep ++ sDoc ++ trailDoc
  return some body

/-- A nested statement sequence (an if-branch), placed directly after its keyword:
    a single clean statement (no comment/blank lines above it, no trailing
    comment, flattenable) becomes a width-aware `group` — inline when it fits
    (`if c then return 1`), else on its own line at +2; anything else goes one
    statement per line at +2. `none` when the sequence has no safe layout. -/
private
def branchDoc?
    (walk : Lean4Fmt.Emit.Walk)
    (seq : Lean.Syntax)
    (lastOwned : Bool)
    (guardBreak : Bool := false)
    : Lean4Fmt.Emit.EmitM (Option Doc) := do
  let some ss := stmts? seq | return none
  if ss.size == 1 then
    let lead := (Lean4Fmt.Syntax.leading? ss[0]!).getD ""
    let plainLead := ((lead.splitOn "\n").drop 1).dropLast.isEmpty
    let srcInline := !lead.any (· == '\n')
    let trailT := ((Lean4Fmt.Syntax.trailing? ss[0]!).getD "").trimAscii.toString
    if plainLead && (lastOwned || trailT.isEmpty)
        && (!(← read).breaking.preserveLineBreaks || srcInline) then
      let sDoc ← walk ss[0]!
      -- guardIfOwnLine: a CONTROL-FLOW branch (`return`/`throw`) keeps its
      -- own line even when it fits — the guard ladder reads vertically;
      -- effect branches still inline by width (the house distinction)
      let isCtl := ss[0]!.getKind == ``Lean.Parser.Term.doReturn
        || ((Lean4Fmt.Emit.bareSrc ss[0]!).trimAscii.toString.startsWith "throw")
      if (← read).breaking.inlineBranches
          && !(guardBreak && isCtl)
          && (Lean4Fmt.Doc.flatWidth sDoc).isSome
          && !Lean4Fmt.Doc.hasMultilineVerbatim sDoc then
        return some (.group (.nest 2 (.line ++ sDoc)))
      -- a nested `do` GLUES to the branch keyword (`=> do` / `then do`) —
      -- its statements bring their own hardlines (mirrors the eqns arm rule;
      -- without this the `do` lands alone on its own line)
      let k := ss[0]!.getKind
      if !Lean4Fmt.Doc.hasMultilineVerbatim sDoc
          && (k == ``Lean.Parser.Term.doNested
            || (k == ``Lean.Parser.Term.doExpr
              && (ss[0]!.getArgs[0]?.map (·.getKind)) == some ``Lean.Parser.Term.do)) then
        return some (.text " " ++ sDoc)
  match ← seqLinesDoc? walk ss lastOwned with
  | some body => return some (.nest 2 body)
  | none => return none

/-- Emit `do <seq>` — one statement per line indented by 2, leading comment/blank
    lines placed structurally, same-line trailing comments re-appended — or one of
    the binding statements (see module header). Only the plain `doSeqIndent` shape
    of `do` is handled; the bracketed `{ … }` shape and any structural surprise
    fall back to verbatim so no token (or comment) is dropped. -/
def emit (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.EmitM Doc := do

  -- preserveLineBreaks: a single-line do-statement is byte-exact (the
  -- author's `let x: T ← …` spacing survives); the do BLOCK itself and
  -- multi-line statements stay structural
  if (← read).breaking.preserveLineBreaks && stx.getKind != ``Lean.Parser.Term.do then
    let t := Lean4Fmt.Emit.bareSrc stx
    if !t.isEmpty && !t.any (· == '\n') then
      return .text t

  let kind := stx.getKind
  let a := stx.getArgs
  if kind == ``Lean.Parser.Term.doLet || kind == ``Lean.Parser.Term.doLetArrow then
    -- `let (mut)? (config)? decl` = [let, mut?, letConfig, decl] where decl is a
    -- letDecl (`:=`, walked — Term handles the 5-slot shape), a doIdDecl (`←`),
    -- or a doPatDecl (`pat ←`; its optional `| else` tail bails inside
    -- idDeclDoc?). Only INTERIOR comments force verbatim — the statement's
    -- outer leading/trailing are the do-loop's to place.
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    if a.size != 4 then return (← Lean4Fmt.Emit.verbatim stx)
    let mutT := (Lean4Fmt.Emit.bareSrc a[1]!).trimAscii.toString
    let cfgT := (Lean4Fmt.Emit.bareSrc a[2]!).trimAscii.toString
    if mutT.any (· == '\n') || cfgT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    let headD : Doc := .text "let " ++ (if mutT.isEmpty then .nil else .text (mutT ++ " "))
      ++ (if cfgT.isEmpty then .nil else .text (cfgT ++ " "))
    if kind == ``Lean.Parser.Term.doLet then
      let dDoc ← walk a[3]!
      if Lean4Fmt.Doc.hasMultilineVerbatim dDoc then return (← Lean4Fmt.Emit.verbatim stx)
      return headD ++ dDoc
    else
      match ← idDeclDoc? walk a[3]! with
      | some d => return headD ++ d
      | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == ``Lean.Parser.Term.doLetElse then
    -- `let pat := v | fallback` — [let, mut?, letConfig, pat, ":="/"←", v,
    -- "|", doSeq, tail?]: head flat, the value width-aware (the idDeclDoc?
    -- treatment), the else arm on its own line at +4 (`    | throwError …`,
    -- the mathlib shape). Single-statement else only this round.
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    if a.size != 9 then return (← Lean4Fmt.Emit.verbatim stx)
    let mutT := (Lean4Fmt.Emit.bareSrc a[1]!).trimAscii.toString
    let cfgT := (Lean4Fmt.Emit.bareSrc a[2]!).trimAscii.toString
    let patT := Lean4Fmt.Emit.canonTok a[3]!
    let asgnT := (Lean4Fmt.Emit.bareSrc a[4]!).trimAscii.toString
    if [mutT, cfgT, patT, asgnT].any (fun t => t.any (· == '\n')) || patT.isEmpty
        || asgnT.isEmpty then
      return (← Lean4Fmt.Emit.verbatim stx)
    let vdoc ← walk a[5]!
    if (match vdoc with | .verbatim _ _ => true | _ => false) then
      return (← Lean4Fmt.Emit.verbatim stx)
    let some ss := stmts? a[7]! | return (← Lean4Fmt.Emit.verbatim stx)
    if ss.size != 1 then return (← Lean4Fmt.Emit.verbatim stx)
    let eDoc ← walk ss[0]!
    if (match eDoc with | .verbatim _ _ => true | _ => false) then
      return (← Lean4Fmt.Emit.verbatim stx)
    let head := "let " ++ (if mutT.isEmpty then "" else mutT ++ " ")
      ++ (if cfgT.isEmpty then "" else cfgT ++ " ") ++ patT ++ " " ++ asgnT
    let glue := (Lean4Fmt.Doc.flatWidth vdoc).isNone
    let valPart : Doc :=
      if glue then .text (head ++ " ") ++ vdoc
      else .text head ++ .group (.nest 2 (.line ++ vdoc))
    -- a[8] carries the CONTINUATION of the do block (the let-else scopes the
    -- rest): emit it through the statement loop at the let's own column
    let contD : Doc ← do
      match a[8]!.getArgs[0]? with
      | some seq =>
        if (Lean4Fmt.Emit.bareSrc seq).trimAscii.toString.isEmpty then pure Doc.nil
        else
          let some ss2 := stmts? seq | return (← Lean4Fmt.Emit.verbatim stx)
          match ← seqLinesDoc? walk ss2 true with
          | some body => pure body
          | none => return (← Lean4Fmt.Emit.verbatim stx)
      | none => pure Doc.nil
    -- width decides flat vs broken (the house one-liner
    -- `let some b := b? | return fallback` stays flat when it fits)
    let flatTotal : Option Nat := do
      let wv ← Lean4Fmt.Doc.flatWidth vdoc
      let we ← Lean4Fmt.Doc.flatWidth eDoc
      pure (head.length + 1 + wv + 3 + we)
    let width := (← read).layout.lineWidth
    let layout :=
      match flatTotal with
      | some t =>
        if t + 4 ≤ width then
          .text (head ++ " ") ++ .flatten vdoc ++ .text " | " ++ .flatten eDoc ++ contD
        else valPart ++ .nest 4 (.hardline ++ .text "| " ++ eDoc) ++ contD
      | none => valPart ++ .nest 4 (.hardline ++ .text "| " ++ eDoc) ++ contD
    if Lean4Fmt.Doc.hasMidlineReanchor layout then
      return (← Lean4Fmt.Emit.verbatim stx)
    return layout
  else if kind == ``Lean.Parser.Term.doLetRec then
    -- `let rec <decl>` = [group[let,rec], letRecDecls, null] — single, plain,
    -- suffix-free binding rides the letDecl machinery (mirrors Term.letrec,
    -- minus the body: the do-loop owns what follows). This statement was a
    -- MUTUAL POISONER: its multi-line verbatim marked the whole enclosing
    -- decl (and any mutual) opaque.
    if Lean4Fmt.Syntax.interiorHasLineComment stx then
      return (← Lean4Fmt.Emit.verbatim stx)
    if a.size < 2 || a.size > 3 then
      return (← Lean4Fmt.Emit.verbatim stx)
    let kwT := Lean4Fmt.Emit.canonTok a[0]!
    if kwT.isEmpty || kwT.any (· == '\n') then
      return (← Lean4Fmt.Emit.verbatim stx)
    if !((a[2]?.map (fun s => (Lean4Fmt.Emit.bareSrc s).trimAscii.toString.isEmpty)).getD true) then
      return (← Lean4Fmt.Emit.verbatim stx)
    let decls := ((a[1]!.getArgs[0]?).map (·.getArgs)).getD #[]
    if decls.size != 1 then
      return (← Lean4Fmt.Emit.verbatim stx)
    let rd := decls[0]!
    if rd.getKind != ``Lean.Parser.Term.letRecDecl || rd.getArgs.size != 4 then
      return (← Lean4Fmt.Emit.verbatim stx)
    if !(Lean4Fmt.Emit.bareSrc rd.getArgs[0]!).trimAscii.toString.isEmpty then
      return (← Lean4Fmt.Emit.verbatim stx)
    if !(Lean4Fmt.Emit.bareSrc rd.getArgs[1]!).trimAscii.toString.isEmpty then
      return (← Lean4Fmt.Emit.verbatim stx)
    if !(Lean4Fmt.Emit.bareSrc rd.getArgs[3]!).trimAscii.toString.isEmpty then
      return (← Lean4Fmt.Emit.verbatim stx)
    let declDoc ← walk rd.getArgs[2]!
    if Lean4Fmt.Doc.hasMultilineVerbatim declDoc then
      return (← Lean4Fmt.Emit.verbatim stx)
    return .text (kwT ++ " ") ++ declDoc
  else if kind == ``Lean.Parser.Term.doReassign then
    -- bare `x := v` = [letIdDeclNoBinders] — the inner decl IS the statement
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    let some inner := a[0]? | return (← Lean4Fmt.Emit.verbatim stx)
    let dDoc ← walk inner
    if Lean4Fmt.Doc.hasMultilineVerbatim dDoc then return (← Lean4Fmt.Emit.verbatim stx)
    return dDoc
  else if kind == ``Lean.Parser.Term.doReassignArrow then
    -- bare `x ← v` = [doIdDecl]
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    let some inner := a[0]? | return (← Lean4Fmt.Emit.verbatim stx)
    match ← idDeclDoc? walk inner with
    | some d => return d
    | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == ``Lean.Parser.Term.doReturn then
    -- `return` or `return v` = ["return", null(term?)] — the value GLUES to
    -- the keyword line: the argument is OPTIONAL, so a break after `return`
    -- reparses as a bare return plus a stray statement ("must be last element
    -- in a do sequence" — found on Pantograph). A too-wide value breaks
    -- INSIDE itself (its head stays on the line).
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    match ((a[1]?.map (·.getArgs)).getD #[])[0]? with
    | none => return (Doc.text "return")
    | some v =>
      let vdoc ← walk v
      if Lean4Fmt.Doc.hasMultilineVerbatim vdoc then return (← Lean4Fmt.Emit.verbatim stx)
      return Doc.text "return " ++ vdoc
  else if kind == ``Lean.Parser.Term.doExpr then
    -- a plain expression statement: the term IS the statement
    match a[0]? with
    | some t => return (← walk t)
    | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == ``Lean.Parser.Term.doIf then
    -- [if, cond, then, seq, (else-if group)*, else?]. Conditions (doIfProp /
    -- if-let, with an optional `h :` binder) are reproduced token-for-token,
    -- single-line. Every line comment must live INSIDE one of the branch
    -- sequences (the accounting below) — a comment around a keyword or in a
    -- condition has no seam here and forces verbatim. Only the FINAL branch may
    -- end in a trailing comment (the statement seam follows it); a comment
    -- before an `else` has no seam.
    if a.size != 6 then return (← Lean4Fmt.Emit.verbatim stx)
    let condT := Lean4Fmt.Emit.canonTok a[1]!
    if condT.isEmpty || condT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    let mut branches : Array (String × Lean.Syntax) := #[("if " ++ condT ++ " then", a[3]!)]
    for g in a[4]!.getArgs do
      let ga := g.getArgs
      if ga.size != 4 then return (← Lean4Fmt.Emit.verbatim stx)
      let cT := Lean4Fmt.Emit.canonTok ga[1]!
      if cT.isEmpty || cT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
      branches := branches.push ("else if " ++ cT ++ " then", ga[3]!)
    let elseArgs := a[5]!.getArgs
    if !elseArgs.isEmpty then
      if elseArgs.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
      branches := branches.push ("else", elseArgs[1]!)
    -- comments only inside branch seqs (the statement's own leading is the
    -- do-loop's and exempt; its trailing is inside the final seq's count)
    let seqCmts := branches.foldl
      (fun n b => n + Lean4Fmt.Syntax.countSubtreeLineComments b.2) 0
    let ownLead := Lean4Fmt.Syntax.countLineComments ((Lean4Fmt.Syntax.leading? stx).getD "")
    if Lean4Fmt.Syntax.countSubtreeLineComments stx != seqCmts + ownLead then
      return (← Lean4Fmt.Emit.verbatim stx)
    let mut d : Doc := .nil
    for h : i in [0:branches.size] do
      let (kw, seq) := branches[i]
      let some bD ← branchDoc? walk seq (i + 1 == branches.size)
        (guardBreak := (← read).breaking.guardIfOwnLine)
        | return (← Lean4Fmt.Emit.verbatim stx)
      d := d ++ (if i == 0 then Doc.nil else .hardline) ++ .text kw ++ bD
    return d
  else if kind == ``Lean.Parser.Term.doMatch then
    -- [match, generalizing?, motive?, ?, discrs, "with", matchAlts] — the head
    -- `match <discrs> with` reproduced token-for-token, single-line; each arm
    -- `| pat =>` with its doSeq body via branchDoc? (inline when a single clean
    -- statement fits). Seam accounting as for doIf: every line comment must sit
    -- inside an arm's sequence; only the FINAL arm may end in a trailing
    -- comment (the statement seam follows it).
    if a.size != 7 then return (← Lean4Fmt.Emit.verbatim stx)
    let midParts := ((a.extract 1 5).map
      (fun s => Lean4Fmt.Emit.canonTok s)).filter (fun s => !s.isEmpty)
    let head := "match " ++ String.intercalate " " midParts.toList ++ " with"
    if head.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    let mut alts : Array Lean.Syntax := #[]
    for g in a[6]!.getArgs do
      for c in g.getArgs do
        if c.getKind == ``Lean.Parser.Term.matchAlt then alts := alts.push c
    if alts.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
    for alt in alts do
      if alt.getArgs.size != 4 then return (← Lean4Fmt.Emit.verbatim stx)
      -- the seam accounting below counts LINE comments only — a BLOCK
      -- comment between arms passes it uncounted and the arm loop (which
      -- places no leadings) would DROP it (gate-caught on mathlib
      -- Algebraize, comments class). Whole-match verbatim keeps it.
      if (((Lean4Fmt.Syntax.leading? alt).getD "").splitOn "/-").length > 1 then
        return (← Lean4Fmt.Emit.verbatim stx "doMatch-arm-block-comment")
    -- arm-LEADING line comments place via the seam kit (leadingSep? — the
    -- armPieces? treatment; the Algebraize `-- explains next arm` shape);
    -- comment accounting: every line comment must sit inside an arm's
    -- sequence, in an arm's now-placed leading, or in the match's own lead
    let seqCmts := alts.foldl
      (fun n alt => n + Lean4Fmt.Syntax.countSubtreeLineComments (alt.getArgs[3]!)) 0
    let armLeadCmts := alts.foldl
      (fun n alt =>
        n + Lean4Fmt.Syntax.countLineComments ((Lean4Fmt.Syntax.leading? alt).getD "")) 0
    let ownLead := Lean4Fmt.Syntax.countLineComments ((Lean4Fmt.Syntax.leading? stx).getD "")
    if Lean4Fmt.Syntax.countSubtreeLineComments stx != seqCmts + armLeadCmts + ownLead then
      return (← Lean4Fmt.Emit.verbatim stx)
    let mut d : Doc := .text head
    for h : i in [0:alts.size] do
      let aa := alts[i].getArgs
      let mut patDoc ← walk aa[1]!
      let mut patBroken := false
      if Lean4Fmt.Doc.hasMultilineVerbatim patDoc then
        -- the alternative-pattern stack (the ApplyFun `| (A, _)\n| (B, _) =>`
        -- shape) rebuilds; anything else keeps the whole match verbatim
        match ← Lean4Fmt.Emit.altPatternStack? aa[1]! Lean4Fmt.Emit.tokenJoinFlat? with
        | some (pd, broken) =>
          patDoc := pd
          patBroken := broken
        | none => return (← Lean4Fmt.Emit.verbatim stx)
      let some bD ← branchDoc? walk aa[3]! (i + 1 == alts.size)
        | return (← Lean4Fmt.Emit.verbatim stx)
      let armSrc := (Lean4Fmt.Emit.bareSrc alts[i]).trimAscii.toString
      let armD : Doc :=
        if (← read).breaking.preserveLineBreaks && !armSrc.isEmpty
            && !armSrc.any (· == '\n') && !patBroken then
          .text armSrc
        else
          let arrowT := (Lean4Fmt.Emit.bareSrc (aa[2]?.getD .missing)).trimAscii.toString
          let arrowT := if arrowT.isEmpty then "=>" else arrowT
          .text "| " ++ patDoc ++ .text (" " ++ arrowT) ++ bD
      let some sep := Lean4Fmt.Emit.leadingSep? ((Lean4Fmt.Syntax.leading? alts[i]).getD "")
        | return (← Lean4Fmt.Emit.verbatim stx)
      d := d ++ sep ++ armD
    return d
  else if kind == ``Lean.Parser.Term.doFor || kind == `Lean.Parser.Term.doWhile
      || kind == `Lean.Parser.Term.doUnless then
    -- `for x in xs do` / `while c do` / `unless c do` — head tokens
    -- single-line (canonically respaced), the body sequence one statement
    -- per line at +2 with the seam loop owning inter-statement trivia
    if a.size < 2 then return (← Lean4Fmt.Emit.verbatim stx)
    let mut head := ""
    for h : i in [0:a.size - 1] do
      let c := a[i]!
      -- first child's leading = the FORM's own leading — the enclosing seam
      -- owns it (see exampleDoc?); interior comments still bail
      let ownLead := if i == 0
        then Lean4Fmt.Syntax.countLineComments ((Lean4Fmt.Syntax.leading? c).getD "")
        else 0
      if Lean4Fmt.Syntax.countSubtreeLineComments c > ownLead then
        return (← Lean4Fmt.Emit.verbatim stx)
      let t := Lean4Fmt.Emit.canonTok c
      if t.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
      if !t.isEmpty then head := if head.isEmpty then t else head ++ " " ++ t
    if head.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
    let some ss := stmts? a[a.size - 1]! | return (← Lean4Fmt.Emit.verbatim stx)
    match ← seqLinesDoc? walk ss true with
    | some body => return .text head ++ .nest 2 body
    | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind != ``Lean.Parser.Term.do && kind != ``Lean.Parser.Term.doNested then
    return (← Lean4Fmt.Emit.verbatim stx)
  else
  -- a comment on the `do` line itself (`do -- setup`) has no home in the layout
  let doKwTrail := ((Lean4Fmt.Syntax.trailing? (a[0]?.getD .missing)).getD "").trimAscii.toString
  if !doKwTrail.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
  let some seq := a[1]? | return (← Lean4Fmt.Emit.verbatim stx)
  let some ss := stmts? seq | return (← Lean4Fmt.Emit.verbatim stx)
  -- compactDo: a SINGLE clean statement rides width-aware after `do` —
  -- inline when it fits (`do pure 1`), else the ordinary block. This is what
  -- makes the active path agree with the interception's inline `do a; b`
  -- (single-statement dos used to force three lines for a one-line body).
  if (← read).breaking.compactDo && ss.size == 1
      && ((Lean4Fmt.Syntax.leading? ss[0]!).getD "").toList.all (·.isWhitespace) then
    let sDoc ← walk ss[0]!
    if !Lean4Fmt.Doc.hasMultilineVerbatim sDoc then
      return .text "do" ++ .group (.nest 2 (.line ++ sDoc))
  -- trailing comments per statement placed by the loop; the LAST statement's
  -- trailing is the whole do's trailing — the enclosing seam owns it
  match ← seqLinesDoc? walk ss true with
  | some body => return .text "do" ++ .nest 2 body
  | none => return (← Lean4Fmt.Emit.verbatim stx)

end Lean4Fmt.Emit.DoNotation
