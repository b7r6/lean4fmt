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
private
def comma_group
    (walk : Walk)
    (l r : String)
    (children : Array Lean.Syntax)
    : emit_m (Option Doc) := do

  -- an authored TRAILING comma (`[a, b,]`) has no slot in the rebuilt list
  -- (commas go BETWEEN items) — `none` rather than drop the token
  -- (gate-caught on aleph CLI.lean, tokens; the listItems? lesson again)
  if (children.back?.map (fun c =>
      c.isAtom && (bare_src c).trimAscii.toString == ",")).getD false then
    return none
  let mut ds : Array Doc := #[]
  for c in children do
    if c.isAtom then continue
    ds := ds.push (← walk c)
  -- literal pools (§5 fill): many short flat items — byte tables, opcode
  -- lists — pack and wrap at the width instead of exploding one per line
  if ds.size ≥ 8 && ds.all (fun d => ((Lean4Fmt.Doc.flat_width d).getD 1000) ≤ 12) then
    let items :=
      ((Array.range ds.size).map
        (fun i => ds[i]! ++ (if i + 1 == ds.size then Doc.nil else Doc.text ","))).toList
    return some (.text l ++ .nest 2 (Doc.fillSep items) ++ .text r)
  return some (Lean4Fmt.Doc.comma_list l r ds)

/-- Comment-bearing comma list, FORCED broken (a line comment cannot flatten,
    §0.4): one element per line at +2, each element's leading comment/blank
    lines placed structurally, the same-line comment after each COMMA (its
    trailing) re-appended, the last element's same-line trailing kept before
    the closer. `none` (caller verbatims) when the closer's leading carries
    content, a trailing spans lines, or a seam has no home. -/
private
def seam_comma_list?
    (walk : Walk)
    (l r : String)
    (opener : Lean.Syntax)
    (pairs : Array (Lean.Syntax × Option Lean.Syntax))
    (closer : Lean.Syntax)
    : emit_m (Option Doc) := do
  if pairs.isEmpty then
    return none
  -- a comment on the opener's own line (`[ -- note`) is OUR zone
  let openTrail := ((Lean4Fmt.Syntax.trailing? opener).getD "").trimAscii.toString
  if openTrail.any (· == '\n') then
    return none
  -- comments directly before the closer have no seam yet
  let isWs (t : String) : Bool := t.all (fun c => c == ' ' || c == '\t')
  let closerLead := (Lean4Fmt.Syntax.leading? closer).getD ""
  if !(((closerLead.splitOn "\n").drop 1).dropLast.all isWs) then
    return none
  if !isWs ((closerLead.splitOn "\n").headD "") then
    return none
  let mut body : Doc := .nil
  for h : i in [0:pairs.size] do
    let (e, comma?) := pairs[i]
    let last := i + 1 == pairs.size
    let some sep := Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? e).getD "")
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
          match Lean4Fmt.Emit.leading_sep? cl with
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

/-- A `do`/`by` DESCENDANT — NEWLINE-BLIND: this feeds a layout decision,
    and "is it multi-line in the SOURCE" flips pass-to-pass (the DualNumber
    fixed-point: pass 1 glued the chain flat, pass 2 saw the now-single-line
    `by` and broke at the ops). Statement hardlines re-anchor at the
    placement's nest column on the broken chain layout, which can cross the
    parse floor and re-associate the block (the ApplyAt lesson — an
    elaboration-level tree change the gate caught as tokens). let/structInst
    newline semantics ride safely inside their own self-anchored docs. -/
private partial
def contains_do_by (s : Lean.Syntax) : Bool :=
  s.getKind == ``Lean.Parser.Term.do || s.getKind == ``Lean.Parser.Term.byTactic
      || s.getKind == `Lean.Parser.Term.byTactic'
      || s.getArgs.any contains_do_by

/-- A chain TAIL that is SAFE to glue after the flat head: a by/do block, or
    a spine of app/fun/show ENDING in one — the glued doc's only hardlines
    are the block's members, which anchor nest-relative below the line. A
    container with its OWN column discipline (calc: later steps must sit at
    the first step's column, which rides the glued line) re-associates on
    reparse (gate-caught on OmegaLimit: `<| calc` glued flat, the step list
    ended early — tokens). -/
private partial
def tail_glue_safe (s : Lean.Syntax) : Bool :=
  let k := s.getKind
  if k == ``Lean.Parser.Term.byTactic || k == `Lean.Parser.Term.byTactic'
      || k == ``Lean.Parser.Term.do then
    true
  else if k == ``Lean.Parser.Term.app then
    ((s.getArgs[1]?.bind (·.getArgs.back?)).map tail_glue_safe).getD false
  else if k == ``Lean.Parser.Term.fun then
    match s.getArgs[1]? with
    | some bf => ((bf.getArgs.back?).map tail_glue_safe).getD false
    | none    => false
  else if k == ``Lean.Parser.Term.show then
    ((s.getArgs.back?).map
      (fun r =>
        r.getKind == `Lean.Parser.Term.byTactic' || r.getKind == ``Lean.Parser.Term.byTactic
            || (r.getKind == ``Lean.Parser.Term.fromTerm
                && ((r.getArgs.back?).map tail_glue_safe).getD false))).getD
      false
  else
    false

/-- Whether the subtree contains a COMMA-form structInst — the one doc shape
    whose broken layout carries FIRST-LINE-ANCHORED interior columns (later
    fields must sit colGe the first field, which rides the `{ ` line). Glued
    after `lval := ` that anchor is deep and the parser closes the inner
    list early on reparse (home Preset.lean). Every other multi-line value
    is nest-relative and re-anchors deterministically. -/
private partial
def contains_comma_struct_inst (s : Lean.Syntax) : Bool :=
  (s.getKind == ``Lean.Parser.Term.structInst && (bare_src s).any (· == ','))
      || s.getArgs.any contains_comma_struct_inst

/-- Flatten a subtree into single-line canonTok PIECES (the binder groups of
    a wide quantifier head): a single-line node is one piece, a multi-line
    container contributes its children's pieces recursively; `none` when a
    leaf itself spans lines (nothing to wrap on). -/
private partial
def head_pieces? (s : Lean.Syntax) : Option (Array String) :=
  let t := Lean4Fmt.Emit.canon_tok s
  if !t.any (· == '\n') then
    if t.isEmpty then some #[] else some #[t]
  else if s.getArgs.isEmpty then
    none
  else
    Id.run do
      let mut acc : Array String := #[]
      for c in s.getArgs do
        match head_pieces? c with
        | some ps => acc := acc ++ ps
        | none => return none
      return some acc

/-- A CHAIN value (let/letrec/have) whose doc breaks: its body rides
    hardline seams that anchor at the CURRENT indent — safe at own-line
    placements, a column hazard when glued at a field/binding column
    (doc-derived test: flatWidth none is pass-stable). -/
private
def chain_own_line (v : Lean.Syntax) (vdoc : Doc) : Bool :=
  (v.getKind == ``Lean.Parser.Term.let || v.getKind == ``Lean.Parser.Term.letrec
      || v.getKind == ``Lean.Parser.Term.have
      || v.getKind == ``Lean.Parser.Term.letI
      || v.getKind == ``Lean.Parser.Term.haveI)
      && (Lean4Fmt.Doc.flat_width vdoc).isNone

/-- A single `structInstField` = [structInstLVal, «rest»]. The LVal (field name /
    path) is reproduced verbatim; the value (the term after `:=`, found inside the
    `structInstFieldDef` in «rest») is walked so it lays out actively. A shorthand
    field `{ x }` (no `:=`) is just its LVal. -/
private partial
def struct_field_doc (walk : Walk) (field : Lean.Syntax) : emit_m Doc := do
  let fa := field.getArgs
  let lvalStx := fa[0]?.getD .missing
  let lvalT := bare_src lvalStx
  let lval ← if !lvalT.isEmpty && !lvalT.any (· == '\n') then
      pure (Doc.text (Lean4Fmt.Emit.canon_tok lvalStx))
    else verbatim lvalStx
  let rest := (fa[1]?.getD Lean.Syntax.missing).getArgs
  let fd? := rest.find? (·.getKind == ``Lean.Parser.Term.structInstFieldDef)
  match fd? with
  | some fd =>
    let da := fd.getArgs
    let v := da[da.size - 1]?.getD Lean.Syntax.missing -- [":=", null?, value]
    -- a field with BINDERS or type ascription (`symm _ _ h := …`) carries
    -- tokens between the lval and the value — the lval++":="++value shape
    -- would DELETE them (gate-caught on mathlib): join the HEAD (lval +
    -- binders + type) single-line and walk the VALUE, same shape as the
    -- plain field. The old whole-field token join required the VALUE
    -- single-line too — the functor-instance idiom (`map {X Y} f := <app
    -- with (by …)>`) rode verbatim on it.
    let expected := Lean4Fmt.Syntax.leaf_toks lvalStx ++ #[":="] ++ Lean4Fmt.Syntax.leaf_toks v
    if Lean4Fmt.Syntax.leaf_toks field != expected then
      let mut headT := Lean4Fmt.Emit.canon_tok lvalStx
      let mut ok := !headT.isEmpty && !headT.any (· == '\n')
      for r in rest do
        if !ok then break
        if r.getKind == ``Lean.Parser.Term.structInstFieldDef then continue
        let t := Lean4Fmt.Emit.canon_tok r
        if t.any (· == '\n') then ok := false
        else if !t.isEmpty then headT := headT ++ " " ++ t
      -- the def node must be exactly the assign shape (`:=` + value)
      if ok && Lean4Fmt.Syntax.leaf_toks fd == #[":="] ++ Lean4Fmt.Syntax.leaf_toks v then
        let vdoc ← walk v
        if chain_own_line v vdoc then
          return .text (headT ++ " :=") ++ .nest 2 (.hardline ++ vdoc)
        return .text (headT ++ " := ") ++ vdoc
      let t := Lean4Fmt.Emit.canon_tok field
      if t.isEmpty || t.any (· == '\n') then
        return (← verbatim field)
      return .text t
    let vdoc ← walk v
    -- a LET-chain value's body sits at hardline seams that ANCHOR AT THE
    -- CURRENT INDENT — glued after `lval := ` that is the FIELD column, so
    -- the comma-less field list ends at the chain body on reparse (the
    -- sepByIndent colGe law; gate-caught on Configuration as a hidden
    -- reparse-fail). A breaking chain value goes OWN-LINE at +2 instead
    -- (the mathlib source shape); flat ones still glue.
    if chain_own_line v vdoc then
      return lval ++ .text " :=" ++ .nest 2 (.hardline ++ vdoc)
    return lval ++ .text " := " ++ vdoc
  | none => return lval

/-- Emit an expression construct, recursing via `walk`. Produces flat Doc for the
    handled kinds; everything else (and anything with a line comment) reproduces
    verbatim. -/
partial
def emit (walk : Walk) (stx : Lean.Syntax) : emit_m Doc := do

  -- comment hazard (§0.4): never restructure a subtree carrying a line comment.
  -- The tail token's TRAILING is exempt: it belongs to the enclosing seam
  -- (whoever places this form also places its trailing — Module for commands,
  -- the do-statement loop for statements), so it survives without our help.
  -- seam-owning kinds bypass this guard (Kinds.ownsSeams): their arms place
  -- inter-item comments structurally; anything they can't hold falls back
  -- internally.
  if !Lean4Fmt.Syntax.owns_seams stx.getKind
      && Lean4Fmt.Syntax.has_unowned_line_comment stx then
    return (← verbatim stx)
  match stx with
  | .atom _ v => return .text v
  | .ident _ _ n _ => return .text n.toString
  | .node _ kind args =>
    -- binary operator: lhs ␣ op ␣ rhs. `Term.arrow` is the same 3-slot shape
    -- (the atom carries the source spelling — `→` or `->` — and the token gate
    -- cares, so it rides through the walk as-is).
    if (Lean4Fmt.Syntax.is_bin_op kind || kind == ``Lean.Parser.Term.arrow) && args.size ≥ 3 then
      -- `lhs op rhs` — width-aware: flat if it fits, else break BEFORE the
      -- operator (operator leads the continuation line). A CHAIN of the same
      -- operator flattens to ONE continuation indent (no staircase):
      --   a = true
      --       ∧ b = true
      --       ∧ c = true
      -- BRACKETED ops (`M →ₗ[R] N`, `f ≫ g` with params — the mathlib hom
      -- family) are the ≥3-arity case: the op spans the MIDDLE slots and is
      -- extracted PER LINK (each link's bracket interior can differ:
      -- `M →ₗ[R] N →ₗ[S] P`).
      -- comment hazard: the chain reflow walks its pieces BARE — a line
      -- comment in a piece's leading has no seam here and would silently
      -- drop (gate-caught on mathlib ContextInfo: comments inside a nested
      -- `<|` chain). Whole-chain verbatim carries it byte-exact.
      if Lean4Fmt.Syntax.interior_has_line_comment stx then
        return (← verbatim stx "chain-comment")
      let opOf := fun (a : Array Lean.Syntax) =>
        Lean4Fmt.Emit.canon_tok (Lean.mkNullNode (a.extract 1 (a.size - 1)))
      -- the ≥4 arity is ONLY the leading-operator bracket family (`→ₗ[R]`,
      -- `≃ₐ[R]`): the op's first char must be an OPERATOR, not an opening
      -- bracket — «term__[_]» (getElem) is isBinOp-shaped with 4 slots and
      -- its `[` adjacency is parse-critical (respacing it broke 48 home
      -- files + 32 fuzz seeds in one build; caught by the battery)
      if args.size > 3 then
        let t := opOf args
        if t.isEmpty || t.any (· == '\n')
            || (t.toList.headD ' ') ∈ ['[', '(', '{', '⁻', '!', '?'] then
          return (← verbatim stx)
      -- same first-char exclusion for the arity-3 op (the widened namespaced
      -- family reaches here): bracket/postfix adjacency is parse-critical —
      -- the getElem lesson, applied before any respacing
      if args.size == 3 then
        let t := (bare_src args[1]!).trimAscii.toString
        if (t.toList.headD ' ') ∈ ['[', '(', '{', '⁻', '!', '?'] then
          return (← verbatim stx)
      let lhs ← walk args[0]!
      let op ← do
        if args.size == 3 then walk args[1]!
        else
          let t := opOf args
          if t.isEmpty || t.any (· == '\n') then return (← verbatim stx "chain-op-shape")
          pure (Doc.text t)
      -- LEADING rows pair each piece with the PARENT level's op (`M →ₛₗ[ρ] N
      -- →ₛₗ[σ] P` = ρ before N, σ before P): thread prevOp — pairing the
      -- link's OWN op swapped bracket interiors one position (gate-caught on
      -- BilinearMap, tokens: ρ₁₂/σ₁₂ transposed)
      let mut tail : Doc := .nil
      let mut prevOp := op
      let mut cur := args[args.size - 1]!
      let mut steps := 0
      while cur.getKind == kind && cur.getArgs.size == args.size && steps < 64 do
        let ca := cur.getArgs
        let linkOp ← do
          if args.size == 3 then walk ca[1]!
          else
            let t := opOf ca
            if t.isEmpty || t.any (· == '\n') then return (← verbatim stx "chain-op-shape")
            pure (Doc.text t)
        tail := tail ++ .line ++ prevOp ++ .space ++ (← walk ca[0]!)
        prevOp := linkOp
        cur := ca[ca.size - 1]!
        steps := steps + 1
      let rhs ← walk cur
      -- the `lhs <| by …` idiom (mathlib-pervasive): a by/do TAIL glues —
      -- flat head (`injective <| by`), the block's members at sequence-seam
      -- hardlines below (deterministic, same as decl `:= by` glue). Only the
      -- TAIL: a by mid-chain has no seam. A whole-block verbatim by (the
      -- emitter bailed) falls through to the guard below.
      -- ANY tail carrying newline-semantic content (an app ending in a do —
      -- `withSynthesize <| withMainContext do`) must ALSO take the glue
      -- form: the broken chain layout re-anchors the do's statements at the
      -- chain's nest column, which can cross the parse floor and re-associate
      -- the block (gate-caught on ApplyAt: elaboration-level tree change,
      -- tokens reject) — glue reproduces the flat-head source shape with
      -- members at their sequence seams; a tail that cannot glue bails.
      let rhsDoBy := contains_do_by cur
      let chainWidth := (← read).layout.lineWidth
      let headFits := match Lean4Fmt.Doc.flat_width (lhs ++ tail ++ Doc.line ++ prevOp) with
        | some w => w + 12 ≤ chainWidth
        | none => false
      if (cur.getKind == ``Lean.Parser.Term.byTactic || cur.getKind == ``Lean.Parser.Term.do
            || (rhsDoBy && headFits && tail_glue_safe cur))
          && (Lean4Fmt.Doc.flat_width lhs).isSome && (Lean4Fmt.Doc.flat_width op).isSome
          && (Lean4Fmt.Doc.flat_width tail).isSome
          && !(match rhs with | .verbatim _ _ => true | _ => false)
          && !Lean4Fmt.Doc.has_midline_reanchor rhs then
        return .flatten (lhs ++ tail ++ .line ++ prevOp) ++ .space ++ rhs
      -- a do/by-bearing tail that cannot GLUE falls to the general layout
      -- (the rounds-1-4 behavior: blocks anchor nest-relative right of any
      -- reachable column floor) — EXCEPT a CALC tail: its later steps must
      -- sit at the first step's column, which the mid-line `op calc` glue
      -- moves (noparse, gate-caught on Control/Fold); a multi-line calc
      -- tail that cannot take the flat-head glue keeps the chain verbatim
      if cur.getKind == `Lean.calc && (bare_src cur).any (· == '\n') then
        -- a multi-line CALC tail takes the TRAILING-op break with the calc
        -- at a LINE-START seam (`Eq.symm <|` then calc at +cont on its own
        -- line — the mathlib source shape): the calc doc anchors exactly as
        -- at a `:=` body, steps nest-relative to its own line. Mid-line
        -- `op calc` moved the step column (noparse, Control/Fold); a head
        -- that cannot flatten keeps the chain verbatim.
        if (Lean4Fmt.Doc.flat_width (lhs ++ tail ++ Doc.line ++ prevOp)).isSome
            && !(match rhs with | .verbatim _ _ => true | _ => false)
            && !Lean4Fmt.Doc.has_midline_reanchor rhs then
          let cont := (← read).layout.continuationIndent
          return .flatten (lhs ++ tail ++ .line ++ prevOp)
            ++ .nest cont (.hardline ++ rhs)
        return (← verbatim stx "chain-calc-tail")
      -- ws-sensitivity (fixed-point class): a multi-line RE-ANCHORING piece
      -- glued mid-chain re-indents its interior by its placement column,
      -- which the previous pass just moved — never a fixed point. A base-0
      -- (mid-line-anchored) verbatim is the worst case: its interior indent
      -- ADDS to the placement (gate-caught on mathlib Abel: `pure <| ←` +
      -- app drifted +8 per pass). The PRECISE test is on the ASSEMBLED
      -- layout (hasMidlineReanchor threads line-start through the actual
      -- seams): a SELF-ANCHORED piece — an app tail ending in a glued
      -- fun/by/do block, a walked show/have value — keeps its interior
      -- verbatims at hardline seams and is a deterministic re-anchor; only
      -- a verbatim the layout genuinely glues mid-line keeps the whole
      -- chain verbatim (porting that piece's kind is the coverage fix).
      let cont := (← read).layout.continuationIndent
      if (← read).breaking.opBreak == .trailing then
        -- trailing operators (mathlib arrows): `a →\n  b →\n  c`. Flat form
        -- identical to the leading build — only the broken shape differs.
        let mut tailT : Doc := .nil
        let mut cur2 := args[args.size - 1]!
        let mut steps2 := 0
        while cur2.getKind == kind && cur2.getArgs.size == args.size && steps2 < 64 do
          let ca := cur2.getArgs
          -- trailing rows carry the LINK's own op after its piece (the ops
          -- sit between pieces; bracket interiors differ per link)
          let linkOp ← do
            if args.size == 3 then walk ca[1]!
            else pure (Doc.text (opOf ca))
          tailT := tailT ++ .line ++ (← walk ca[0]!) ++ .space ++ linkOp
          cur2 := ca[ca.size - 1]!
          steps2 := steps2 + 1
        let layout := lhs ++ .space ++ op ++ .nest cont (tailT ++ .line ++ rhs)
        if Lean4Fmt.Doc.has_midline_reanchor layout then
          return (← verbatim stx "chain-multiline-piece")
        return .group layout
      let layout := lhs ++ .nest cont (tail ++ .line ++ prevOp ++ .space ++ rhs)
      if Lean4Fmt.Doc.has_midline_reanchor layout then
        return (← verbatim stx "chain-multiline-piece")
      return .group layout
    else if kind == ``Lean.Parser.Term.app then
      -- `fn a b c` — width-aware: flat if it fits, else `fn` on its line with each
      -- argument on a continuation line indented by `layout.indent`. All-or-
      -- nothing (a `group`): the source did not dictate this, the width does.
      let fn := args[0]!
      let argList := (args[1]?.map (·.getArgs)).getD #[]
      let ind := (← read).layout.indent
      let fnDoc ← walk fn
      if Lean4Fmt.Syntax.interior_has_line_comment stx then
        -- comment-bearing application: forced broken, one argument per line,
        -- per-argument seams (leading comment lines placed, same-line trailing
        -- comments re-appended; the LAST argument's trailing is the enclosing
        -- seam's)
        if Lean4Fmt.Syntax.interior_has_line_comment fn then return (← verbatim stx)
        let mut argsDoc : Doc := .nil
        for h : i in [0:argList.size] do
          let a := argList[i]
          let last := i + 1 == argList.size
          let some sep := Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? a).getD "")
            | return (← verbatim stx)
          let trailT := ((Lean4Fmt.Syntax.trailing? a).getD "").trimAscii.toString
          if !last && trailT.any (· == '\n') then return (← verbatim stx)
          let trailD : Doc := if !last && !trailT.isEmpty then .text (" " ++ trailT) else .nil
          argsDoc := argsDoc ++ sep ++ (← walk a) ++ trailD
        return fnDoc ++ .nest ind argsDoc
      -- a final do/by ARG glues (`Id.run do`, `IO.mkRef do`, `foo x by …`):
      -- flat head of fn + prior args, the block's members at seams — the
      -- by-tail rule at the app site
      if argList.size ≥ 1 then
        let lastA := argList[argList.size - 1]!
        if lastA.getKind == ``Lean.Parser.Term.do
            || lastA.getKind == ``Lean.Parser.Term.byTactic
            -- trailing-lambda idiom (`.map fun s => do …`): the fun doc is
            -- self-anchored when its own body glued (do/by/match) — same
            -- seam as a final do arg
            || ((← read).breaking.glueFun && lastA.getKind == ``Lean.Parser.Term.fun) then
          let dDoc ← walk lastA
          -- fun args additionally guard the mid-line hazard (do/by docs
          -- place interior verbatims at seams by construction; fun bodies
          -- may not)
          let funHazard := lastA.getKind == ``Lean.Parser.Term.fun
              && Lean4Fmt.Doc.has_midline_reanchor dDoc
          if !(match dDoc with | .verbatim _ _ => true | _ => false) && !funHazard then
            let mut headD := fnDoc
            let mut flatOk := (Lean4Fmt.Doc.flat_width fnDoc).isSome
            for h : i in [0:argList.size - 1] do
              let aDoc ← walk argList[i]!
              if (Lean4Fmt.Doc.flat_width aDoc).isNone then flatOk := false
              headD := headD ++ .space ++ aDoc
            if flatOk then return .flatten headD ++ .space ++ dDoc
      let mut argsDoc : Doc := .nil
      for a in argList do argsDoc := argsDoc ++ .line ++ (← walk a)
      return .group (fnDoc ++ .nest ind argsDoc)
    else if kind == ``Lean.Parser.Term.paren then
      -- "(" content ")" — content is args[1] (may be empty for unit)
      match args[1]? with
      | some c =>
        let d ← walk c
        -- `(by …)` / `(do …)` — the mathlib-pervasive tactic-arg idiom: the
        -- block's members sit at sequence-seam hardlines (deterministic
        -- re-anchor), so only a MID-LINE multiline verbatim is a hazard —
        -- hasMidlineReanchor, exact here because the doc STARTS with the
        -- keyword text (the initial line-start state is irrelevant). A bare
        -- whole-verbatim block still bails.
        if c.getKind == ``Lean.Parser.Term.byTactic || c.getKind == ``Lean.Parser.Term.do then
          match d with
          | .verbatim _ _ => return (← verbatim stx "paren-multiline-piece")
          | _ =>
            if Lean4Fmt.Doc.has_midline_reanchor d then
              return (← verbatim stx "paren-multiline-piece")
            return .text "(" ++ d ++ .text ")"
        -- ws-sensitivity (fixed-point master class): other content glues
        -- after `(` MID-LINE — a multi-line re-anchoring piece drifts by its
        -- placement (+10/pass on mathlib Induced: a bailed ∘ₗ chain inside a
        -- paren app-arg); and even at a seam, a HALF-VERBATIM mixture
        -- re-anchors its hand-shaped interior columns at the new anchor and
        -- reads mangled (home Derived.lean, the tuple table). Whole-paren
        -- verbatim gets a line-start seam from its own placement instead.
        if Lean4Fmt.Doc.hasMultilineReanchor d then
          return (← verbatim stx "paren-multiline-piece")
        return .text "(" ++ d ++ .text ")"
      | none => return .text "()"
    else if kind == ``Lean.Parser.Term.show then
      -- `show T from e` / `show T by tacs` — [show, type, fromTerm|byTactic'].
      -- The type joins FLAT (parse-derived — tokenJoinFlat? refuses comments
      -- and newline-semantic interiors; multi-line ∀-types bail v1). A by
      -- rhs GLUES (`show T by` + tactics below at their sequence seams); a
      -- `from` trails the type with the value width-aware after it (by/do
      -- values glue the same way). Trivia in the joined zones (kw trailing,
      -- from trivia, value leading) has no seam — bail.
      let some ty := args[1]? | return (← verbatim stx)
      let some rhs := args[2]? | return (← verbatim stx)
      let kw := (bare_src args[0]!).trimAscii.toString
      let kw := if kw.isEmpty then "show" else kw
      if !(((Lean4Fmt.Syntax.trailing? args[0]!).getD "").trimAscii.toString.isEmpty) then
        return (← verbatim stx "show-head-comment")
      let width := (← read).layout.lineWidth
      let tyD ← (do
        match Lean4Fmt.Emit.token_join_flat? ty with
        | some t =>
          if !t.isEmpty && !t.any (· == '\n') && t.length + 12 ≤ width then
            pure (some (Doc.text t))
          else pure none
        | none => pure (none : Option Doc))
      let some tyD := tyD | return (← verbatim stx "show-type-shape")
      if rhs.getKind == `Lean.Parser.Term.byTactic'
          || rhs.getKind == ``Lean.Parser.Term.byTactic then
        if !(((Lean4Fmt.Syntax.leading? rhs).getD "").trimAscii.toString.isEmpty) then
          return (← verbatim stx "show-by-lead-comment")
        let bd ← walk rhs
        let layout := .text (kw ++ " ") ++ tyD ++ .text " " ++ bd
        if Lean4Fmt.Doc.has_midline_reanchor layout then
          return (← verbatim stx "show-by-shape")
        return layout
      if rhs.getKind == ``Lean.Parser.Term.fromTerm then
        let ra := rhs.getArgs
        let fromA := ra[0]?.getD .missing
        let fromT := (bare_src fromA).trimAscii.toString
        let fromT := if fromT.isEmpty then "from" else fromT
        let v := ra[1]?.getD .missing
        for t in [(Lean4Fmt.Syntax.leading? fromA).getD "",
            (Lean4Fmt.Syntax.trailing? fromA).getD "",
            (Lean4Fmt.Syntax.leading? v).getD ""] do
          if !t.trimAscii.toString.isEmpty then
            return (← verbatim stx "show-from-comment")
        let vd ← walk v
        let glue := v.getKind == ``Lean.Parser.Term.do
          || v.getKind == ``Lean.Parser.Term.byTactic
        let layout : Doc :=
          if glue then .text (kw ++ " ") ++ tyD ++ .text (" " ++ fromT ++ " ") ++ vd
          else .group (.text (kw ++ " ") ++ tyD ++ .text (" " ++ fromT)
            ++ .nest 2 (.line ++ vd))
        if Lean4Fmt.Doc.has_midline_reanchor layout then
          return (← verbatim stx "show-from-shape")
        return layout
      return (← verbatim stx "show-rhs-shape")
    else if kind == ``Lean.Parser.Term.proj then
      -- obj "." field   (args[0]=obj, args[1]=".", args[2]=field)
      return (← walk args[0]!) ++ .text "." ++ (← walk (args[2]?.getD .missing))
    else if kind == ``Lean.Parser.Term.dotIdent then
      return .text "." ++ (← walk (args[1]?.getD .missing))
    else if kind == ``Lean.Parser.Term.anonymousCtor then
      let children := (args[1]?.map (·.getArgs)).getD #[]
      if Lean4Fmt.Syntax.interior_has_line_comment stx then
        let mut pairs : Array (Lean.Syntax × Option Lean.Syntax) := #[]
        for c in children do
          if c.isAtom then
            if !pairs.isEmpty then
              pairs := pairs.set! (pairs.size - 1) (pairs[pairs.size - 1]!.1, some c)
          else pairs := pairs.push (c, none)
        match ← seam_comma_list? walk "⟨" "⟩" (args[0]?.getD .missing) pairs (args[2]?.getD .missing) with
        | some d => return d
        | none => return (← verbatim stx)
      match ← comma_group walk "⟨" "⟩" children with
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
      let srcEmpty := ((args[1]?.map bare_src).getD "").trimAscii.toString.isEmpty
      let ellipsisEmpty := ((args[3]?.map bare_src).getD "").trimAscii.toString.isEmpty
      -- the UPDATE form `{ src with fields }`: the source segment joins
      -- canonically (`p with`); comment-bearing and grid paths stay
      -- conservative (plain group only)
      let srcT := if srcEmpty then "" else Lean4Fmt.Emit.canon_tok (args[1]?.getD .missing)
      if srcT.any (· == '\n') || !ellipsisEmpty then return (← verbatim stx)
      -- a `: T` ascription (any content between the ellipsis slot and the
      -- closer) has no active placement — dropping it DELETED tokens
      for i in [4:args.size - 1] do
        if !((args[i]?.map bare_src).getD "").trimAscii.toString.isEmpty then
          return (← verbatim stx)
      let mut fields : Array Lean.Syntax := #[]
      let mut pairs : Array (Lean.Syntax × Option Lean.Syntax) := #[]
      let mut commas := 0
      for g in ((args[2]?.map (·.getArgs)).getD #[]) do
        for c in g.getArgs do
          if c.getKind == ``Lean.Parser.Term.structInstField then
            fields := fields.push c
            pairs := pairs.push (c, none)
          else if c.isAtom && bare_src c == "," then
            commas := commas + 1
            if !pairs.isEmpty then
              pairs := pairs.set! (pairs.size - 1) (pairs[pairs.size - 1]!.1, some c)
      if fields.isEmpty then return (← verbatim stx)
      if fields.size > 1 && commas + 1 != fields.size then
        -- NEWLINE-separated fields (no comma tokens, 24.8KB of the wide
        -- census): emit the canonical vertical form — one field per line at
        -- +2, no commas added (token-preserving by construction; the
        -- source's hand column-alignment is replaced by canonical
        -- indentation, which also retires CLASS 4 for the active path).
        -- Mixed separators (some commas) or any interior comment stay
        -- verbatim; field docs with midline hazards bail.
        if commas != 0 || !ellipsisEmpty then return (← verbatim stx)
        -- `{ src with` rides the brace line (single-line source term); the
        -- fields below at +2 are the same vertical machinery — all at one
        -- column, sepByIndent-safe like the no-src form
        if srcT.any (· == '\n') then return (← verbatim stx)
        -- comment hazard, per seam: comments AT the vertical seams (field
        -- leading, field-tail trailing — where brace-adjacent trivia also
        -- lands) have no slot in this assembly. A field-INTERIOR comment is
        -- the field walk's business: owned seams place it, anything unowned
        -- verbatims a piece the bare/midline checks below catch. The old
        -- blanket interiorHasLineComment kept every record with a commented
        -- by-proof field verbatim (the FreeAlgebra lift idiom).
        for f in fields do
          if Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.leading? f).getD "") > 0
              || Lean4Fmt.Syntax.count_line_comments
                  ((Lean4Fmt.Syntax.last_token_trailing? f).getD "") > 0 then
            return (← verbatim stx)
        let mut body : Doc := .nil
        for f in fields do
          let fDoc ← struct_field_doc walk f
          -- structInstFields is sepByIndent: the hazard is FIRST-LINE-
          -- ANCHORED interior columns — a comma-form structInst in the
          -- value breaks with later fields colGe its own first field, which
          -- glued after `lval := ` sits deep, and the parser closes the
          -- inner list early on reparse (home Preset.lean). Bail on that
          -- shape (containsCommaStructInst); every other multi-line value
          -- is nest-relative (by-glue hardlines, fresh-line app groups) and
          -- both re-anchors deterministically AND lands strictly deeper
          -- than the field column (outer colGe holds).
          -- a field too wide to fit flat BREAKS inside its own group (the
          -- same nest-relative colGe argument as the hardline case); only
          -- the comma-form hazard is real either way
          if contains_comma_struct_inst f then return (← verbatim stx)
          if (match fDoc with | .verbatim _ _ => true | _ => false)
              || Lean4Fmt.Doc.has_midline_reanchor fDoc then
            return (← verbatim stx)
          body := body ++ .hardline ++ fDoc
        if srcT.isEmpty then
          return .text "{" ++ .nest 2 body ++ .hardline ++ .text "}"
        -- srcT is the canonTok of the source-with slot — it CARRIES the
        -- `with` atom already
        return .text ("{ " ++ srcT) ++ .nest 2 body ++ .hardline ++ .text "}"
      if Lean4Fmt.Syntax.interior_has_line_comment stx then
        if !srcT.isEmpty then return (← verbatim stx)
        -- comment-bearing record: forced broken, per-field seams
        match ← seam_comma_list? walk "{" "}" (args[0]?.getD .missing) pairs (args[args.size - 1]?.getD .missing) with
        | some d => return d
        | none => return (← verbatim stx)
      let mut ds : Array Doc := #[]
      for f in fields do ds := ds.push (← struct_field_doc walk f)
      let groupForm : Doc := if srcT.isEmpty then
          .group (.text "{ " ++ .nest 2 (Lean4Fmt.Doc.sep_by (.text "," ++ .line) ds) ++ .text " }")
        else
          -- `{ src with` rides the opener; fields below at +2 when broken
          .group (.text ("{ " ++ srcT) ++ .nest 2 (.line
            ++ Lean4Fmt.Doc.sep_by (.text "," ++ .line) ds) ++ .text " }")
      -- §7 recordFields: the broken form as an aligned grid — `{ `/`  ` ride in
      -- the first column so the grid IS the hanging house style; flat still
      -- wins when it fits (the renderer prefers a flat-capable fallback).
      let al := (← read).alignment
      if srcT.isEmpty && al.recordFields != Lean4Fmt.Style.align_mode.never && fields.size ≥ 2 then
        let mut rows : List (List Doc) := []
        let mut ok := true
        for h : i in [0:fields.size] do
          let fa := fields[i]!.getArgs
          let lvalT := Lean4Fmt.Emit.canon_tok (fa[0]?.getD .missing)
          if lvalT.isEmpty || lvalT.any (· == '\n') then ok := false
          let rest := (fa[1]?.getD Lean.Syntax.missing).getArgs
          match rest.find? (·.getKind == ``Lean.Parser.Term.structInstFieldDef) with
          | some fd =>
            let v := (fd.getArgs[fd.getArgs.size - 1]?).getD Lean.Syntax.missing
            let vDoc ← walk v
            if (Lean4Fmt.Doc.flat_width vDoc).isNone then ok := false
            let last := i + 1 == fields.size
            rows := rows ++
              [[Doc.text ((if i == 0 then "{ " else "  ") ++ lvalT), Doc.text ":=",
                vDoc ++ Doc.text (if last then " }" else ",")]]
          | none => ok := false
        if ok then
          let cap := if al.recordFields == Lean4Fmt.Style.align_mode.always
            then 1000000 else al.maxDelta
          return Doc.align_or { sep := " ", maxDelta := cap } rows groupForm
      return groupForm
    else if kind == Lean4Fmt.Syntax.list_lit_kind || kind == Lean4Fmt.Syntax.array_lit_kind then
      let l := if kind == Lean4Fmt.Syntax.list_lit_kind then "[" else "#["
      let children := (args[1]?.map (·.getArgs)).getD #[]
      if Lean4Fmt.Syntax.interior_has_line_comment stx then
        let mut pairs : Array (Lean.Syntax × Option Lean.Syntax) := #[]
        for c in children do
          if c.isAtom then
            if !pairs.isEmpty then
              pairs := pairs.set! (pairs.size - 1) (pairs[pairs.size - 1]!.1, some c)
          else pairs := pairs.push (c, none)
        match ← seam_comma_list? walk l "]" (args[0]?.getD .missing) pairs (args[2]?.getD .missing) with
        | some d => return d
        | none => return (← verbatim stx)
      match ← comma_group walk l "]" children with
      | some d => return d
      | none => return (← verbatim stx "trailing-comma")
    else if kind == Lean4Fmt.Syntax.ite_kind then
      -- [if, cond, then, thenBranch, else, elseBranch]; a width-aware group:
      -- flat `if c then a else b`, or broken with 2-space branches, `else` at
      -- the if's base column (§ active layout). Branches recurse via `walk`.
      -- An interior slot whose TAIL carries a comment (`… then x -- note` before
      -- `else`) has no seam in this layout — verbatim keeps it. (The entry
      -- guard can't see it: the comment hides in an ownsSeams subtree whose
      -- own emitter treats its tail trailing as the PARENT's zone.)
      for slot in [args[1]?, args[3]?] do
        let t := ((slot.bind Lean4Fmt.Syntax.last_token_trailing?).getD "").trimAscii.toString
        if !t.isEmpty then return (← verbatim stx)
      -- a full-line comment in a BRANCH's leading (`else⏎  -- note⏎  body`)
      -- has no seam in this layout either — the branch walk drops leading
      -- trivia (gate-caught on evring HttpConn, comments class)
      for slot in [args[3]?, args[5]?] do
        if Lean4Fmt.Syntax.count_line_comments ((slot.bind Lean4Fmt.Syntax.leading?).getD "") > 0 then
          return (← verbatim stx "ite-branch-leading-comment")
      let cond ← walk (args[1]?.getD .missing)
      let thenB ← walk (args[3]?.getD .missing)
      let elseB ← walk (args[5]?.getD .missing)
      -- else-if CHAIN (breaking.elseIfChain): a nested ite glues after `else`
      let elseIsIte := (args[5]?.map (fun e =>
        e.getKind == Lean4Fmt.Syntax.ite_kind || e.getKind == Lean4Fmt.Syntax.dite_kind)).getD false
      let elseTail : Doc := if (← read).breaking.elseIfChain && elseIsIte
        then .text "else " ++ elseB
        else .text "else" ++ .nest 2 (.line ++ elseB)
      return .group (
        .text "if " ++ cond ++ .text " then"
          ++ .nest 2 (.line ++ thenB)
          ++ .line ++ elseTail)
    else if kind == ``Lean.Parser.Term.let || kind == ``Lean.Parser.Term.have
        || kind == ``Lean.Parser.Term.letI || kind == ``Lean.Parser.Term.haveI then
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
      -- letI/haveI are the same 5-slot chain shape (the mathlib
      -- local-instance idiom — Order/Basic's letI ladders) and interleave
      -- with let/have freely
      while (cur.getKind == ``Lean.Parser.Term.let
          || cur.getKind == ``Lean.Parser.Term.have
          || cur.getKind == ``Lean.Parser.Term.letI
          || cur.getKind == ``Lean.Parser.Term.haveI) && steps < 10000 do
        steps := steps + 1
        let a := cur.getArgs
        if a.size < 5 then return (← verbatim stx)
        let lead := (Lean4Fmt.Syntax.leading? cur).getD ""
        if !first then
          let some sep := Lean4Fmt.Emit.leading_sep? lead | return (← verbatim stx)
          d := d ++ sep
        else
          -- the chain's head leading (between `:=` and the first `let`) is
          -- OURS when it carries comment lines — the enclosing seam only
          -- provides the line break. Plain whitespace stays the caller's.
          let isWs (l : String) : Bool := l.all (fun c => c == ' ' || c == '\t')
          if !(((lead.splitOn "\n").drop 1).dropLast.all isWs) then
            let some sep := Lean4Fmt.Emit.leading_sep? lead | return (← verbatim stx)
            d := d ++ sep
        first := false
        let cfgT := (((a[1]?.map bare_src).getD "").trimAscii.toString)
        if cfgT.any (· == '\n') then return (← verbatim stx)
        let decl := a[2]?.getD .missing
        let declDoc ← walk decl
        -- ws-sensitivity (fixed-point master class): the binding glues after
        -- `let ` mid-line — a BARE multi-line verbatim binding drifts by its
        -- placement column (SSP/Trust.Protocol, +4/pass). The letIdDecl path
        -- now places its interior opaque values OWN-LINE (seam-stable), so
        -- an ACTIVE declDoc with seam-placed verbatims is safe to glue —
        -- trust the inner discipline, bail only on the bare-verbatim bind
        -- (the tacticHave lesson).
        if (match declDoc with | .verbatim _ _ => true | _ => false)
            || Lean4Fmt.Doc.has_midline_reanchor declDoc then
          return (← verbatim stx "let-multiline-binding")
        let sepT := (((a[3]?.map bare_src).getD "").trimAscii.toString)
        if sepT.any (· == '\n') then return (← verbatim stx)
        -- the `;`-form let (`let y := n / x; body`) is SAME-LINE semantic:
        -- emitting it broken re-shapes the separator slot on reparse (tree
        -- class, gate-caught on mathlib Divisors). The authored flat form
        -- IS canonical — ride verbatim.
        if sepT == ";" then return (← verbatim stx "semicolon-let")
        -- same-line trailing comment on the binding (the gap to the next
        -- binding's leading is the seam above)
        let trailT := ((Lean4Fmt.Syntax.trailing? decl).getD "").trimAscii.toString
        if trailT.any (· == '\n') then return (← verbatim stx)
        let cfgDoc : Doc := if cfgT.isEmpty then .nil else .text cfgT ++ .space
        let kwT := (bare_src (a[0]?.getD .missing)).trimAscii.toString
        if kwT.isEmpty then return (← verbatim stx)
        d := d ++ .text (kwT ++ " ") ++ cfgDoc ++ declDoc ++ .text sepT
          ++ (if trailT.isEmpty then Doc.nil else .text (" " ++ trailT))
        cur := a[a.size-1]?.getD .missing
      -- the final body: its leading is the last seam the chain owns
      let some bodySep := Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? cur).getD "")
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
      if (bare_src args[3]!).trimAscii.toString != ":=" then return (← verbatim stx)
      let headParts := ((args.extract 0 2).map Lean4Fmt.Emit.canon_tok).filter
        (fun s => !s.isEmpty)
      let head0 := String.intercalate " " headParts.toList
      -- head0 may be EMPTY: the anonymous `have : T := …` has no name and
      -- no binders (regression caught by census: -1.1pt, the old 0-3 join
      -- accepted it) — only the ASSEMBLED head must be nonempty
      if head0.any (· == '\n') then return (← verbatim stx)
      let tyT := Lean4Fmt.Emit.canon_tok (args[2]?.getD .missing)
      if head0.isEmpty && tyT.isEmpty then return (← verbatim stx)
      let headDoc : Doc ← do
        if tyT.isEmpty then pure (.text head0)
        else if !tyT.any (· == '\n') then
          pure (.text (if head0.isEmpty then tyT else head0 ++ " " ++ tyT))
        else
          -- multi-line TYPE (the have/let broken-head class — the census
          -- cluster's dominator): name+binders flat, `:` trails the head,
          -- the walked type breaks at +4 (the sig continuation shape);
          -- `:= value` glues after the type's last line
          -- the optional type slot arrives null-wrapped in the have/let
          -- shapes — unwrap before the typeSpec check (a multi-line type
          -- otherwise bailed structurally: the 68K tacticHave census pool)
          let ts0 := args[2]!
          let ts := if ts0.getKind == Lean.nullKind && ts0.getArgs.size == 1
            then ts0.getArgs[0]! else ts0
          let tyNode :=
            if ts.getKind == ``Lean.Parser.Term.typeSpec then ts.getArgs[1]?.getD .missing
            else .missing
          if tyNode.isMissing then return (← verbatim stx)
          let tyDoc ← walk tyNode
          if (match tyDoc with | .verbatim _ _ => true | _ => false)
              || Lean4Fmt.Doc.hasMultilineVerbatim tyDoc then
            return (← verbatim stx)
          pure (.text (if head0.isEmpty then ":" else head0 ++ " :")
            ++ .group (.nest 4 (.line ++ tyDoc)))
      let v := args[4]!
      let vdoc ← walk v
      -- by glues like do (`h : T := by` + tactics below — the sequence-seam
      -- invariant tolerates interior verbatims); other kinds keep the bail
      if v.getKind == ``Lean.Parser.Term.do || v.getKind == ``Lean.Parser.Term.byTactic then
        return headDoc ++ .text " := " ++ vdoc
      -- a fun WRAPPING a block glues the same way — but only when the fun
      -- itself laid out (a bare-verbatim fun would re-anchor mid-line)
      if Lean4Fmt.Syntax.is_fun_block_value v
          && !(match vdoc with | .verbatim _ _ => true | _ => false) then
        return headDoc ++ .text " := " ++ vdoc
      -- the vertical structInst glues by its unconditional `{` left edge —
      -- house shape `:= {` … `}` (see valForm; same seam argument)
      if ((Lean4Fmt.Doc.left_edge_text? vdoc).map (·.startsWith "{")).getD false
          && !Lean4Fmt.Doc.hasMultilineVerbatim vdoc then
        return headDoc ++ .text " := " ++ vdoc
      if Lean4Fmt.Doc.hasMultilineVerbatim vdoc then
        -- multi-line opaque value: OWN-LINE placement is a deterministic
        -- seam (the uniform re-anchor preserves interior relations) — the
        -- old whole-binding bail protected against the mid-line glue only.
        -- A bare whole-verbatim value still bails (nothing active to keep).
        match vdoc with
        | .verbatim _ _ => return (← verbatim stx)
        | _ =>
          if Lean4Fmt.Doc.has_midline_reanchor vdoc then return (← verbatim stx)
          return headDoc ++ .text " :=" ++ .nest 2 (.hardline ++ vdoc)
      return headDoc ++ .text " :=" ++ .group (.nest 2 (.line ++ vdoc))
    else if kind == ``Lean.Parser.Term.match then
      -- [match, motive?, motive?, discrs, "with", matchAlts]. Reproduce the head
      -- `match <discrs> with` token-for-token; lay each arm `| pat => body` on its
      -- own line at the match's indent, the body width-aware after `=>`. Patterns
      -- are walked (opaque, so a multi-line pattern trips the valDoc gate to the
      -- safe span). Guarded: any structural surprise falls back to verbatim.
      let midParts := (#[args[1]?, args[2]?, args[3]?].filterMap id).toList.filterMap
        (fun s => let t := Lean4Fmt.Emit.canon_tok s; if t.isEmpty then none else some t)
      let head := "match " ++ String.intercalate " " midParts ++ " with"
      let some altsNode := args[5]? | return (← verbatim stx)
      let alts := Lean4Fmt.Emit.match_alts_of altsNode
      if alts.isEmpty || head.any (· == '\n') then return (← verbatim stx)
      -- the shared arm loop (Emit/Monad.armPieces?): `none` = some arm is
      -- unportable (interior comment, unownable leading, mid-set multi-line
      -- trailing) — whole-match verbatim
      let some pieces ← Lean4Fmt.Emit.arm_pieces? walk alts Lean4Fmt.Emit.token_join_flat? | return (← verbatim stx)
      let al := (← read).alignment
      -- grids per visible-seam section (comments/blanks split; a section with
      -- a grid-ineligible arm rides plain — see armsAlignedRuns)
      return .text head ++ Lean4Fmt.Emit.arms_aligned_runs al.matchArms al.maxDelta pieces
    else if kind == Lean4Fmt.Syntax.dite_kind then
      -- [if, binderIdent, :, cond, then, thenBranch, else, elseBranch] — the
      -- dependent `if h : c then … else …`; same layout as termIfThenElse,
      -- same interior-tail comment bail (no seam for `… then x -- note`).
      for slot in [args[3]?, args[5]?] do
        let t := ((slot.bind Lean4Fmt.Syntax.last_token_trailing?).getD "").trimAscii.toString
        if !t.isEmpty then return (← verbatim stx)
      -- and the branch-LEADING comment bail (see termIfThenElse)
      for slot in [args[5]?, args[args.size - 1]?] do
        if Lean4Fmt.Syntax.count_line_comments ((slot.bind Lean4Fmt.Syntax.leading?).getD "") > 0 then
          return (← verbatim stx "ite-branch-leading-comment")
      let binder ← walk (args[1]?.getD .missing)
      let cond ← walk (args[3]?.getD .missing)
      let thenB ← walk (args[5]?.getD .missing)
      let elseB ← walk (args[args.size-1]?.getD .missing)
      -- else-if CHAIN (breaking.elseIfChain): a nested ite in the else slot
      -- glues (`else if … then`) instead of breaking to `else` + line
      let elseIsIte := (args[args.size-1]?.map (fun e =>
        e.getKind == Lean4Fmt.Syntax.ite_kind || e.getKind == Lean4Fmt.Syntax.dite_kind)).getD false
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
      if bf.getKind == ``Lean.Parser.Term.matchAlts then
        -- `fun | pat => …` alternative form: FLAT when the whole fun joins
        -- within width (the house `fun | .idle => true | _ => false` idiom,
        -- origin-independent via the flatten-first law); else the shared
        -- arm loop, arms under the keyword at +2
        match Lean4Fmt.Emit.token_join_flat? stx with
        | some t =>
          if !t.any (· == '\n') && t.length + 4 ≤ (← read).layout.lineWidth then
            return .text t
        | none => pure ()
        let kw := (bare_src args[0]!).trimAscii.toString
        if kw.isEmpty then return (← verbatim stx)
        let alts := Lean4Fmt.Emit.match_alts_of bf
        if alts.isEmpty then return (← verbatim stx)
        let some pieces ← Lean4Fmt.Emit.arm_pieces? walk alts Lean4Fmt.Emit.token_join_flat? | return (← verbatim stx)
        let al := (← read).alignment
        return .text kw
          ++ .nest 2 (Lean4Fmt.Emit.arms_aligned_runs al.matchArms al.maxDelta pieces)
      if bf.getKind != ``Lean.Parser.Term.basicFun then return (← verbatim stx)
      let ba := bf.getArgs
      if ba.size != 4 then return (← verbatim stx)
      -- the keyword token from SOURCE: `fun` and `λ` are distinct tokens and
      -- the gate cares (found on Pantograph — hardcoding "fun" ate every `λ`)
      let mut head := (bare_src args[0]!).trimAscii.toString
      if head.isEmpty then return (← verbatim stx)
      for b in ((ba[0]?).map (·.getArgs)).getD #[] do
        let t := Lean4Fmt.Emit.canon_tok b
        if t.isEmpty || t.any (· == '\n') then return (← verbatim stx)
        head := head ++ " " ++ t
      let tyT := (ba[1]?.map Lean4Fmt.Emit.canon_tok).getD ""
      if tyT.any (· == '\n') then return (← verbatim stx)
      if !tyT.isEmpty then head := head ++ " " ++ tyT
      -- arrow spelling from SOURCE (`=>` vs `↦` — same lesson as fun/λ above)
      let arrowT := (bare_src ba[2]!).trimAscii.toString
      let arrowT := if arrowT.isEmpty then "=>" else arrowT
      let body := ba[3]!
      let bodyDoc ← walk body
      if body.getKind == ``Lean.Parser.Term.do || body.getKind == ``Lean.Parser.Term.byTactic then
        -- glued do/by body: members at sequence seams; a bare-verbatim
        -- block bails (mid-line glue is the master fixed-point class)
        match bodyDoc with
        | .verbatim _ _ => return (← verbatim stx)
        | _ => return .text (head ++ " " ++ arrowT ++ " ") ++ bodyDoc
      -- the vertical structInst body glues by its unconditional `{` left
      -- edge — house shape `fun a b => {` … `}` (same seam as letIdDecl)
      if ((Lean4Fmt.Doc.left_edge_text? bodyDoc).map (·.startsWith "{")).getD false
          && !Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc then
        return .text (head ++ " " ++ arrowT ++ " ") ++ bodyDoc
      -- a MATCH body glues too (`fun s => match s with` riding, arms at
      -- their hardline seams below at +2 — the house shape)
      if body.getKind == ``Lean.Parser.Term.match
          && !Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc
          && !(match bodyDoc with | .verbatim _ _ => true | _ => false) then
        return .text (head ++ " " ++ arrowT ++ " ") ++ .nest 2 bodyDoc
      if Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc then
        -- multi-line opaque body: OWN-LINE at +2 is a deterministic seam
        -- (the fun class was 26KB of the wide census and the interior piece
        -- of half the chain bails)
        match bodyDoc with
        | .verbatim _ _ => return (← verbatim stx)
        | _ =>
          if Lean4Fmt.Doc.has_midline_reanchor bodyDoc then return (← verbatim stx)
          return .text (head ++ " " ++ arrowT) ++ .nest 2 (.hardline ++ bodyDoc)
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
      return Lean4Fmt.Doc.comma_list "(" ")" ds
    else if kind == ``Lean.Parser.Term.letrec then
      -- single, plain `let rec` binding: 'let rec ' ++ decl (walked — the
      -- 5-slot letIdDecl machinery applies) ++ body at the SAME indent.
      -- Multi-decl (comma), doc/attr-bearing, or suffix-bearing recs verbatim.
      if args.size != 4 then return (← verbatim stx)
      let kwT := (bare_src args[0]!).trimAscii.toString
      if kwT.any (· == '\n') then return (← verbatim stx)
      let decls := ((args[1]!.getArgs[0]?).map (·.getArgs)).getD #[]
      if decls.size != 1 then return (← verbatim stx)
      let rd := decls[0]!
      if rd.getKind != ``Lean.Parser.Term.letRecDecl || rd.getArgs.size != 4 then
        return (← verbatim stx)
      if !(bare_src rd.getArgs[0]!).trimAscii.toString.isEmpty then return (← verbatim stx)
      if !(bare_src rd.getArgs[1]!).trimAscii.toString.isEmpty then return (← verbatim stx)
      if !(bare_src rd.getArgs[3]!).trimAscii.toString.isEmpty then return (← verbatim stx)
      let declDoc ← walk rd.getArgs[2]!
      if Lean4Fmt.Doc.hasMultilineVerbatim declDoc then return (← verbatim stx)
      let sepT := (((args[2]?.map bare_src).getD "").trimAscii.toString)
      if sepT.any (· == '\n') then return (← verbatim stx)
      let body := args[3]!
      let some bodySep := Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? body).getD "")
        | return (← verbatim stx)
      let bodyDoc ← walk body
      return .text (kwT ++ " ") ++ declDoc ++ .text sepT ++ bodySep ++ bodyDoc
    else if kind == ``Lean.Parser.Term.forall then
      -- [∀|forall, binders, opt, ",", body] — head token-for-token (the
      -- quantifier atom keeps its source spelling), the body walked: flat
      -- after the comma when it fits, else on the next line at
      -- continuationIndent (quantifier bodies read as continuations)
      if args.size != 5 then return (← verbatim stx)
      let kwT := (bare_src args[0]!).trimAscii.toString
      if kwT.isEmpty then return (← verbatim stx)
      let mut hd : Doc := .text kwT
      for b in args[1]!.getArgs do
        let bd ← Lean4Fmt.Emit.binder_doc walk b   -- multi-line types walk
        if Lean4Fmt.Doc.hasMultilineVerbatim bd then return (← verbatim stx)
        hd := hd ++ .space ++ bd
      let optT := (bare_src args[2]!).trimAscii.toString
      if optT.any (· == '\n') then return (← verbatim stx)
      if !optT.isEmpty then hd := hd ++ .text (" " ++ optT)
      let bodyDoc ← walk args[4]!
      if Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc then return (← verbatim stx)
      let cont := (← read).layout.continuationIndent
      return hd ++ .text "," ++ .group (.nest cont (.line ++ bodyDoc))
    else if kind == `Lean.«term∀__,_» || kind == `Lean.«term∃__,_»
        || kind == `«term∃_,_» || kind == `«term∀_,_»
        || Lean4Fmt.Syntax.is_binder_comma kind then
      -- binder-predicate quantifiers (`∀ x ∈ s, p` / `∃ x ∈ s, p`): head
      -- tokens canonical (comma glued), body width-aware at the continuation.
      -- The EXTENDED family (isBinderComma — arbitrary notations) keeps its
      -- head SOURCE-EXACT instead: respacing changed which notation wins the
      -- longest-match parse (`∫ t in a..b,` → the `..` adjacency flipped
      -- «term∫_In_.._,_» to «term∫_In_,_» — tree class, gate-caught on
      -- AbelSummation/Chebyshev; the getElem lesson for unknown token sets)
      let n := args.size
      if n < 2 then return (← verbatim stx)
      let core := kind == `Lean.«term∀__,_» || kind == `Lean.«term∃__,_»
        || kind == `«term∃_,_» || kind == `«term∀_,_»
      let mut head := ""
      if core then
        -- head PIECES: a wide binder list wraps width-aware (fillSep below)
        -- instead of bailing — each piece is canonTok'd per binder group
        -- (core-notation respacing is parse-stable; the source-exact law is
        -- for UNKNOWN token sets)
        let mut pieces : Array String := #[]
        for c in args.extract 0 (n - 1) do
          let t := Lean4Fmt.Emit.canon_tok c
          if t.any (· == '\n') then
            -- the binder container (null / explicitBinders / nested groups)
            -- splits into per-group single-line pieces
            match head_pieces? c with
            | some ps => pieces := pieces ++ ps
            | none => return (← verbatim stx)
          else if t == "," then
            if pieces.isEmpty then return (← verbatim stx)
            pieces := pieces.set! (pieces.size - 1) (pieces[pieces.size - 1]! ++ ",")
          else if !t.isEmpty then pieces := pieces.push t
        if pieces.isEmpty then return (← verbatim stx)
        let joined := String.intercalate " " pieces.toList
        if !joined.any (· == '\n')
            && joined.length + 1 ≤ (← read).layout.lineWidth then
          head := joined
        else
          -- wrapped head: keyword anchors, binder pieces fill at the
          -- continuation; the body group follows as usual
          let cont := (← read).layout.continuationIndent
          let hd := .nest cont (Doc.fillSep (pieces.toList.map Doc.text))
          let bodyDoc ← walk args[n - 1]!
          if Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc then return (← verbatim stx)
          return hd ++ .group (.nest cont (.line ++ bodyDoc))
      else
        let t := (bare_src (Lean.mkNullNode (args.extract 0 (n - 1)))).trimAscii.toString
        if t.any (· == '\n') then return (← verbatim stx)
        head := t
      if head.isEmpty then return (← verbatim stx)
      let bodyDoc ← walk args[n - 1]!
      if Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc then return (← verbatim stx)
      let cont := (← read).layout.continuationIndent
      return .text head ++ .group (.nest cont (.line ++ bodyDoc))
    else if kind == `«term¬_» && args.size == 2 then
      -- prefix negation over a (possibly multi-line) operand; GLUED (`¬p`,
      -- `¬(a = b)`) — the community convention, and mathlib's at 60:1
      let opT := (bare_src args[0]!).trimAscii.toString
      if opT.isEmpty || opT.any (· == '\n') then return (← verbatim stx)
      let d ← walk args[1]!
      if Lean4Fmt.Doc.hasMultilineVerbatim d then return (← verbatim stx)
      return .text opT ++ d
    else if kind == ``Lean.Parser.Term.hole then
      return .text "_"
    else if kind == `str || kind == `num || kind == `scientific || kind == `char then
      -- literal: exact token; multi-line strings are CONTENT (quiet — not an
      -- actionable opt-out)
      let t := bare_src stx
      if !t.isEmpty && !t.any (· == '\n') then return .text t
      return (← verbatim_quiet stx)
    else
      return (← verbatim stx)      -- not yet ported (let/match/do/if/…): opaque
  | .missing => return .nil

end Lean4Fmt.Emit.Term
