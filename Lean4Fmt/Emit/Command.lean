/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // EMIT // Command
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Open-recursion emitter for the Command category (DESIGN_V2 §11): `inductive`
    declarations (reached through `Decl.emit` — the modifiers live there). The
    head goes on one line, each constructor on its own line at +2 (doc comment
    above it, byte-exact), `deriving` at +2 below. Anything the layout can't
    hold — old `:=`-style bodies, computed fields, a line comment anywhere, a
    multi-line head or constructor — returns `none` and the whole declaration
    reproduces verbatim, guarded by the safety gate as always.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Emit.Monad
import Lean4Fmt.Emit.Tokens
import Lean4Fmt.Emit.Binders
import Lean4Fmt.Syntax.Trivia

namespace Lean4Fmt.Emit.Command

open Lean Lean4Fmt.Doc Lean4Fmt.Emit

/-- One constructor `(/-- doc -/)? | (modifiers)? name (binders)* (: τ)?`, as a
    single line (the doc comment on its own line above). `none` on a multi-line
    piece or a structural surprise — the caller reproduces the whole
    declaration. -/
private def ctorDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (c : Lean.Syntax)
            (preserve : Bool)
            : Lean4Fmt.Emit.EmitM (Option (Doc × String × Option Doc)) := do

  let ctor := c
  if c.getKind != ``Lean.Parser.Command.ctor then
    return none
  let a := c.getArgs
  if a.size != 5 then
    return none
  let docT := (bareSrc a[0]!).trimAscii.toString
  let modsT := (bareSrc a[2]!).trimAscii.toString
  let nameT := (bareSrc a[3]!).trimAscii.toString
  if nameT.isEmpty || nameT.any (· == '\n') || modsT.any (· == '\n') then
    return none
  let sig := a[4]!.getArgs
  let mut parts : Array String := #[]
  let mut fillDocs : Array Doc := #[]
  let mut needFill := false
  for b in ((sig[0]?).map (·.getArgs)).getD #[] do
    let t := Lean4Fmt.Emit.canonTok b
    if t.any (· == '\n') then
      -- multi-line param: flatten it; the LINE goes to fill mode
      match Lean4Fmt.Emit.tokenJoinFlat? b with
      | some ft =>
        needFill := true
        parts := parts.push ft
        fillDocs := fillDocs.push (Doc.text ft)
      | none => return none
    else
      parts := parts.push t
      fillDocs := fillDocs.push (Doc.text t)
  let tyT ← do
    match ((sig[1]?).map (·.getArgs)).getD #[] |>.toList with
    | [ts] =>
      let t := Lean4Fmt.Emit.canonTok ((ts.getArgs[1]?).getD .missing)
      if t.isEmpty || t.any (· == '\n') then return none
      pure (some t)
    | [] => pure (none : Option String)
    | _ => return none
  let joined :=
    "| " ++ (if modsT.isEmpty then "" else modsT ++ " ") ++ nameT
        ++ (parts.foldl (fun s p => s ++ " " ++ p) "")
        ++ (match tyT with
        | some t => " : " ++ t
        | none   => "")
  -- exact tail: the ctor bytes AFTER the doc comment (docD carries the doc)
  let exact := (Lean4Fmt.Emit.bareSrc (Lean.mkNullNode (a.extract 1 a.size))).trimAscii.toString
  let line := if preserve && !exact.isEmpty && !exact.any (· == '\n') then "| " ++ exact else joined
  -- a ctor whose joined line cannot fit gets FILL mode: params packed and
  -- wrapped at the continuation (deterministic; grid-ineligible)
  let w := (← read).layout.lineWidth
  let lineDoc? : Option Doc :=
    if (needFill || joined.length + 4 > w) && !fillDocs.isEmpty then
      some
        (.text ("| " ++ (if modsT.isEmpty then "" else modsT ++ " ") ++ nameT ++ " ")
            ++ .nest
              6
              (Doc.fillSep fillDocs.toList
                  ++ (match tyT with
                  | some t => Doc.text (" : " ++ t)
                  | none   => Doc.nil)))
    else
      none
  -- the doc comment is byte-exact on its own line above (it may be multi-line;
  -- it sits at a hardline position, literal emission is the stable choice)
  let docD : Doc := if docT.isEmpty then .nil else .textRaw docT ++ .hardline
  return some (docD, line, lineDoc?)

/-- A body item for the seam-owning loops: its separator (leading trivia,
    already placed), whether that separator is a plain single newline, its
    prefix (doc comment lines), the single-line content, and its trailing
    comment (empty when none / not owned). -/
private structure Item where
  sep       : Doc
  plainSep  : Bool
  prefixDoc : Doc
  hasPrefix : Bool
  line      : String
  /-- Doc-valued line (multi-line types walk); excluded from grids. -/
  lineDoc : Option Doc := none
  /-- the `name (binders)` segment of `line`, when the site aligns name columns
      (§7 structFields); empty when the site aligns trailing comments only -/
  nameSeg : String := ""
  /-- the `: τ (:= v)` remainder matching `nameSeg` -/
  restSeg : String := ""
  trailT : String
  deriving Inhabited

/-- Assemble body items, aligning RUNS of consecutive plain items that carry
    trailing comments into `[code, comment]` alignTable rows (§7,
    `alignment.trailingComments`). A run breaks at: a doc-comment prefix, a
    non-plain separator (blank lines / placed comments — a blank line resets
    alignment, matching clang-format), or an item without a trailing comment.
    `.always` ignores the delta cap; `.whenShort` passes it to the renderer
    (which opts the whole run out rather than padding raggedly); `.never`
    emits everything plain. -/
private def assemble
            (trailMode : Lean4Fmt.Style.AlignMode)
            (colMode : Lean4Fmt.Style.AlignMode)
            (maxDelta : Nat)
            (items : Array Item)
            : Doc :=

  Id.run
    do
      let trailOn := trailMode != Lean4Fmt.Style.AlignMode.never
      let colOn := colMode != Lean4Fmt.Style.AlignMode.never
      let cap :=
        if trailMode == Lean4Fmt.Style.AlignMode.always
            || colMode == Lean4Fmt.Style.AlignMode.always then
          1000000
        else
          maxDelta
      let plain (o : Doc) (it : Item) : Doc :=
        o ++ it.sep ++ it.prefixDoc
            ++ (match it.lineDoc with
            | some d => d
            | none   => .text it.line)
            ++ (if it.trailT.isEmpty then Doc.nil else .text (" " ++ it.trailT))
      let flush (o : Doc) (run : Array Item) : Doc := Id.run do
        if run.size < 2 then
          -- short runs emit plainly, WITH their separators
          let mut o := o
          for it in run do o := plain o it
          return o
        -- the run's leading separator is emitted once, outside the alignOr — the
        -- fallback must start sep-less, or a fallback render would double it (a
        -- spurious blank that shifts the run every pass: caught as idempotence
        -- failures by the harness)
        let mut fallback : Doc := .nil
        for h : i in [0:run.size] do
          let it := run[i]!
          if i == 0 then
            fallback := fallback ++ it.prefixDoc ++ .text it.line
              ++ (if it.trailT.isEmpty then Doc.nil else .text (" " ++ it.trailT))
          else fallback := plain fallback it
        if run.size >= 2 then
          -- name-column rows when the site provides the split (structFields);
          -- [code, comment] rows otherwise. A row without a trailing comment is
          -- shorter — its last populated column goes unpadded, so no trailing
          -- whitespace is ever produced.
          let rows := run.toList.map (fun it =>
            if colOn && !it.nameSeg.isEmpty then
              if it.trailT.isEmpty then [Doc.text it.nameSeg, Doc.text it.restSeg]
              else [Doc.text it.nameSeg, Doc.text it.restSeg, Doc.text it.trailT]
            else
              if it.trailT.isEmpty then [Doc.text it.line]
              else [Doc.text it.line, Doc.text it.trailT])
          return o ++ run[0]!.sep
            ++ Doc.alignOr { sep := " ", maxDelta := cap } rows fallback
        return o ++ fallback -- unreachable (size < 2 returned above)
      -- run eligibility: plain separator, no doc-comment prefix, and — when only
      -- trailing alignment is on — a trailing comment to align
      let eligible (it : Item) : Bool :=
        it.plainSep && !it.hasPrefix
            && ((colOn && !it.nameSeg.isEmpty) || (trailOn && !it.trailT.isEmpty))
      let mut out : Doc := .nil
      let mut run : Array Item := #[]
      for it in items do
        if eligible it then run := run.push it
        else
          out := flush out run
          run := #[]
          out := plain out it
      return flush out run

/-- Active layout for a `where`-style `inductive` body (the declaration node
    WITHOUT its modifiers — `Decl.emit` places those). `none` when this layout
    can't hold the input faithfully. -/
def inductiveDoc?
    (walk : Lean4Fmt.Emit.Walk)
    (defn : Lean.Syntax)
    (alignMode : Lean4Fmt.Style.AlignMode)
    (alignDelta : Nat)
    (preserve : Bool := false)
    : Lean4Fmt.Emit.EmitM (Option Doc) := do

  let a := defn.getArgs
  if a.size != 7 then
    return none
  -- head: `inductive Name <binders> (: τ)? where` — one line, token-for-token
  let idT := (bareSrc a[1]!).trimAscii.toString
  if idT.isEmpty || idT.any (· == '\n') then
    return none
  let sig := a[2]!.getArgs
  let mut head := "inductive " ++ idT
  for b in ((sig[0]?).map (·.getArgs)).getD #[] do
    let t := Lean4Fmt.Emit.canonTok b
    if t.any (· == '\n') then
      return none
    head := head ++ " " ++ t
  match ((sig[1]?).map (·.getArgs)).getD #[] |>.toList with
  | [ts] =>
    let t := Lean4Fmt.Emit.canonTok ((ts.getArgs[1]?).getD .missing)
    if t.isEmpty || t.any (· == '\n') then
      return none
    head := head ++ " : " ++ t
  | [] => pure ()
  | _ => return none
  -- `where` optional (the headless `inductive X | ctor …` form is the same
  -- ctor loop); old `:=`-style bodies and computed fields stay verbatim
  let whereT := ((a[3]?.map bareSrc).getD "").trimAscii.toString
  if whereT != "where" && !whereT.isEmpty then
    return none
  if !((a[5]?.map bareSrc).getD "").trimAscii.toString.isEmpty then
    return none
  -- a comment on the `where` line itself has no home in the layout
  if whereT == "where"
      && !((Lean4Fmt.Syntax.trailing? a[3]!).getD "").trimAscii.toString.isEmpty then
    return none
  if whereT == "where" then head := head ++ " where"
  -- constructors, one per line at +2. The loop OWNS the inter-ctor trivia (the
  -- seam model): each ctor's leading comment/blank lines are placed
  -- structurally before it, and a same-line trailing comment is re-appended —
  -- the LAST ctor's trailing belongs to the deriving/enclosing seam. A comment
  -- INSIDE a ctor (between its tokens) has no seam — whole-decl verbatim.
  let ctors := (a[4]?.map (·.getArgs)).getD #[]
  if ctors.isEmpty then
    return none
  -- deriving (its leading trivia placed structurally, so blank groups before
  -- it survive), token-for-token
  let derT := (a[6]?.map Lean4Fmt.Emit.canonTok).getD ""
  if derT.any (· == '\n') then
    return none
  let hasDer := !derT.isEmpty
  let some derSep :=
    (if hasDer then leadingSep? ((Lean4Fmt.Syntax.leading? a[6]!).getD "") else some Doc.nil)
    | return none
  let mut items : Array Item := #[]
  for h : i in [0:ctors.size] do
    let c := ctors[i]
    if Lean4Fmt.Syntax.interiorHasLineComment c then return none
    let trailT := ((Lean4Fmt.Syntax.trailing? c).getD "").trimAscii.toString
    let last := i + 1 == ctors.size
    -- the LAST ctor's trailing belongs to the enclosing seam (Module) — unless
    -- `deriving` follows, in which case the loop owns it like any other
    let owned := !last || hasDer
    if owned && trailT.any (· == '\n') then return none
    let lead := (Lean4Fmt.Syntax.leading? c).getD ""
    let some sep := leadingSep? lead | return none
    let plainSep := ((lead.splitOn "\n").drop 1).dropLast.isEmpty
    let some (docD, line, lineDoc?) ← ctorDoc? walk c preserve | return none
    -- preserve: the trailing comment's hand padding is part of the line
    let rawTrail := (((Lean4Fmt.Syntax.trailing? c).getD "").trimAsciiEnd).toString
    let (line, trailT) :=
      if preserve && owned && !trailT.isEmpty && !rawTrail.any (· == '\n') then
        (line ++ rawTrail, "")
      else (line, trailT)
    items := items.push
      { sep, plainSep, prefixDoc := docD, hasPrefix := !(docD matches Doc.nil),
        line, lineDoc := lineDoc?, trailT := if owned then trailT else "" }
  let derD : Doc := if hasDer then derSep ++ .text derT else .nil
  -- ctorsOneLine (purtell): an all-BARE ctor set (`| GET | POST …` — no
  -- docs, no comments, no binders/types) joins on ONE line when it fits —
  -- the enum-table idiom, headless form, ctor line at column 0
  if (← read).breaking.ctorsOneLine && whereT.isEmpty
      && items.all (fun it => !it.hasPrefix && it.trailT.isEmpty && it.plainSep
        && it.lineDoc.isNone && (it.line.splitOn " ").length == 2) then
    let joined := String.intercalate " " (items.toList.map (·.line))
    if joined.length ≤ (← read).layout.lineWidth then
      return some (.text head ++ .hardline ++ .text joined ++ .nest 2 derD)
  let body := assemble alignMode .never alignDelta items
  return some (.text head ++ .nest 2 (body ++ derD))

/-- One structure field `(/-- doc -/)? (modifiers)? name (binders)* : τ (:= v)?`,
    as a single line (the doc comment on its own line above — it lives INSIDE
    the field's declModifiers, unlike a ctor's). `none` on a multi-line piece,
    a parenthesized field group (`structExplicitBinder`), or a structural
    surprise. -/
private def fieldDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (f : Lean.Syntax)
            (preserve : Bool)
            : Lean4Fmt.Emit.EmitM (Option (Doc × String × String × String × Option Doc)) := do

  if f.getKind != ``Lean.Parser.Command.structSimpleBinder then
    return none
  let a := f.getArgs
  if a.size != 4 then
    return none
  let margs := (a[0]?.map (·.getArgs)).getD #[]
  let docT := ((margs[0]?.map bareSrc).getD "").trimAscii.toString
  let mut modsT := ""
  for m in margs.toList.drop 1 do
    let t := (bareSrc m).trimAscii.toString
    if t.any (· == '\n') then
      return none
    if !t.isEmpty then modsT := modsT ++ t ++ " "
  let nameT := (bareSrc a[1]!).trimAscii.toString
  if nameT.isEmpty || nameT.any (· == '\n') then
    return none
  let sig := a[2]!.getArgs
  let mut parts : Array String := #[]
  for b in ((sig[0]?).map (·.getArgs)).getD #[] do
    let t := Lean4Fmt.Emit.canonTok b
    if t.any (· == '\n') then
      return none
    parts := parts.push t
  let mut tyDoc? : Option Doc := none
  let tyT ← do
    match ((sig[1]?).map (·.getArgs)).getD #[] |>.toList with
    | [ts] =>
      let tyStx := (ts.getArgs[1]?).getD .missing
      let t := Lean4Fmt.Emit.canonTok tyStx
      if t.isEmpty then return none
      if t.any (· == '\n') then
        -- multi-line field TYPE: FLATTEN when the one-line spelling fits
        -- (keeps the item grid-able and the passes shape-stable); otherwise
        -- walk it (forall/arrow chains lay out)
        let w := (← read).layout.lineWidth
        match Lean4Fmt.Emit.tokenJoinFlat? tyStx with
        | some ft =>
          if ft.length + 12 ≤ w then pure (some ft)
          else
            let d ← walk tyStx
            if Lean4Fmt.Doc.hasMultilineVerbatim d then return none
            tyDoc? := some d
            pure (none : Option String)
        | none =>
          let d ← walk tyStx
          if Lean4Fmt.Doc.hasMultilineVerbatim d then return none
          tyDoc? := some d
          pure (none : Option String)
      else pure (some t)
    | [] => pure (none : Option String)
    | _ => return none
  let defT := ((a[3]?.map bareSrc).getD "").trimAscii.toString
  let mut defDoc? : Option Doc := none
  if defT.any (· == '\n') then
    -- multi-line DEFAULT (class-field `:= by exact …` — the structure-shape
    -- class): walk the value; a by/do glues (members at sequence seams),
    -- anything else places OWN-LINE (the seam law). The item rides lineDoc,
    -- grid-ineligible, like walked types do.
    -- walk the WHOLE default node: its bytes carry the `:=` (and the `by` of
    -- a binderTactic default — unwrapping into the tactic seq DROPPED those
    -- tokens; gate-caught on ModelTheory/Basic, and the repro's earlier
    -- "pass" was a silent gate-identity — check stderr on direct exe runs)
    let d ← walk a[3]!
    defDoc? := some (.nest 2 (.hardline ++ d))
  if tyDoc?.isSome && !defT.isEmpty then
    return none
  let defTFlat := if defDoc?.isSome then "" else defT
  let nameSeg := modsT ++ nameT ++ (parts.foldl (fun s p => s ++ " " ++ p) "")
  let restSeg :=
    (match tyT with
    | some t => ": " ++ t
    | none   => "")
        ++ (if defTFlat.isEmpty then "" else (if tyT.isSome then " " else "") ++ defTFlat)
  let joined := nameSeg ++ (if restSeg.isEmpty then "" else " " ++ restSeg)
  -- exact tail: the field bytes from the name onward (doc rides docD)
  let exact := (Lean4Fmt.Emit.bareSrc (Lean.mkNullNode (a.extract 1 a.size))).trimAscii.toString
  let line :=
    if preserve && modsT.isEmpty && !exact.isEmpty && !exact.any (· == '\n') then exact else joined
  let lineDoc? :=
    match tyDoc?, defDoc? with
    | some d, _ => some (Doc.text (nameSeg ++ " : ") ++ d)
    | none, some dd =>
      some
        (Doc.text
          (nameSeg
              ++ (match tyT with
              | some t => " : " ++ t
              | none   => ""))
            ++ dd)
    | none, none => none
  let docD : Doc := if docT.isEmpty then .nil else .textRaw docT ++ .hardline
  return some (docD, nameSeg, restSeg, line, lineDoc?)

/-- Active layout for a `structure`/`class` declaration (WITHOUT its modifiers —
    `Decl.emit` places those): head on one line
    (`structure Name <binders> (: τ)? (extends …)? where`), one field per line
    at +2 via the seam-owning item loop, `deriving` at +2 below. `none` when
    this layout can't hold the input (an explicit `mk ::`, parenthesized field
    groups, comments in seamless zones, multi-line pieces). -/
def structureDoc?
    (walk : Lean4Fmt.Emit.Walk)
    (defn : Lean.Syntax)
    (alignMode : Lean4Fmt.Style.AlignMode)
    (fieldColMode : Lean4Fmt.Style.AlignMode)
    (alignDelta : Nat)
    (preserve : Bool := false)
    : Lean4Fmt.Emit.EmitM (Option Doc) := do

  let a := defn.getArgs
  if a.size != 6 then
    return none
  let kwT := (bareSrc a[0]!).trimAscii.toString
  if kwT.isEmpty || kwT.any (· == '\n') then
    return none
  let idT := (bareSrc a[1]!).trimAscii.toString
  if idT.isEmpty || idT.any (· == '\n') then
    return none
  let sig := a[2]!.getArgs
  let mut head := kwT ++ " " ++ idT
  for b in ((sig[0]?).map (·.getArgs)).getD #[] do
    let t := Lean4Fmt.Emit.canonTok b
    if t.any (· == '\n') then
      return none
    head := head ++ " " ++ t
  match ((sig[1]?).map (·.getArgs)).getD #[] |>.toList with
  | [ts] =>
    let t := (bareSrc ((ts.getArgs[1]?).getD .missing)).trimAscii.toString
    if t.isEmpty || t.any (· == '\n') then
      return none
    head := head ++ " : " ++ t
  | [] => pure ()
  | _ => return none
  let extT := ((a[3]?.map bareSrc).getD "").trimAscii.toString
  if extT.any (· == '\n') then
    return none
  if !extT.isEmpty then head := head ++ " " ++ extT
  -- deriving, shared with the fieldless form
  let derT := (a[5]?.map Lean4Fmt.Emit.canonTok).getD ""
  if derT.any (· == '\n') then
    return none
  let hasDer := !derT.isEmpty
  let some derSep :=
    (if hasDer then leadingSep? ((Lean4Fmt.Syntax.leading? a[5]!).getD "") else some Doc.nil)
    | return none
  let derD : Doc := if hasDer then derSep ++ .text derT else .nil
  -- the where-block: ["where", mk?, structFields] — absent for a fieldless
  -- structure; an explicit `mk ::` stays verbatim
  let wargs := (a[4]?.map (·.getArgs)).getD #[]
  if wargs.isEmpty then
    return some (.text head ++ .nest 2 derD)
  if wargs.size != 3 then return none
  if ((wargs[0]?.map bareSrc).getD "").trimAscii.toString != "where" then return none
  if !((wargs[1]?.map bareSrc).getD "").trimAscii.toString.isEmpty then return none
  if !((Lean4Fmt.Syntax.trailing? wargs[0]!).getD "").trimAscii.toString.isEmpty then return none
  head := head ++ " where"
  let fields := ((wargs[2]?.bind (·.getArgs[0]?)).map (·.getArgs)).getD #[]
  if fields.isEmpty then return none
  -- fields, one per line at +2: the loop OWNS the inter-field trivia (leading
  -- comment/blank lines placed structurally, same-line trailing comments
  -- re-appended; the LAST field's trailing belongs to the enclosing seam
  -- unless `deriving` follows)
  let mut items : Array Item := #[]
  for h : i in [0:fields.size] do
    let f := fields[i]
    if Lean4Fmt.Syntax.interiorHasLineComment f then return none
    let trailT := ((Lean4Fmt.Syntax.trailing? f).getD "").trimAscii.toString
    let last := i + 1 == fields.size
    let owned := !last || hasDer
    if owned && trailT.any (· == '\n') then return none
    let lead := (Lean4Fmt.Syntax.leading? f).getD ""
    let some sep := leadingSep? lead | return none
    let plainSep := ((lead.splitOn "\n").drop 1).dropLast.isEmpty
    let some (docD, nameSeg, restSeg, line, lineDoc?) ← fieldDoc? walk f preserve | return none
    let rawTrail := (((Lean4Fmt.Syntax.trailing? f).getD "").trimAsciiEnd).toString
    let (line, trailT) :=
      if preserve && owned && !trailT.isEmpty && !rawTrail.any (· == '\n') then
        (line ++ rawTrail, "")
      else (line, trailT)
    items := items.push
      { sep, plainSep, prefixDoc := docD, hasPrefix := !(docD matches Doc.nil),
        line, lineDoc := lineDoc?, nameSeg, restSeg := restSeg,
        trailT := if owned then trailT else "" }
  let body := assemble alignMode fieldColMode alignDelta items
  return some (.text head ++ .nest 2 (body ++ derD))

/-- Emit the Command construct rooted at `stx`, recursing via `walk`:
    `mutual … end` blocks lay their member declarations out via `walk` (each is
    a `declaration` — `Decl.emit` does the real work), one per group at +2,
    inter-declaration comment/blank structure placed by the seam loop, `end` at
    the mutual's column. Everything else reproduces verbatim. -/
def emit
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.EmitM Doc := do

  let kind := stx.getKind
  if kind == ``Lean.Parser.Command.variable then
    -- `variable <binders>`: a MULTI-LINE binder list packs BINDER-WISE as a
    -- fillSep at the continuation (each binder one item — a token fill
    -- would wrap inside brackets); single-line lists fit on the line the
    -- same way (mathlib's long variable blocks were 4.3KB of the census)
    if Lean4Fmt.Syntax.hasOwnedLineComment stx then
      return (← Lean4Fmt.Emit.verbatim stx)
    let binders := ((stx.getArgs[1]?).map (·.getArgs)).getD #[]
    let mut items : Array Doc := #[]
    for b in binders do
      let bd ← Lean4Fmt.Emit.binderDoc walk b
      if Lean4Fmt.Doc.hasMultilineReanchor bd then
        return (← Lean4Fmt.Emit.verbatim stx)
      if (Lean4Fmt.Doc.flatWidth bd).isNone then
        return (← Lean4Fmt.Emit.verbatim stx)
      items := items.push (.flatten bd)
    if items.isEmpty then
      return (← Lean4Fmt.Emit.verbatim stx)
    let cont := (← read).layout.continuationIndent
    return .text "variable " ++ .nest cont (Doc.fillSep items.toList)
  if kind == ``Lean.Parser.Command.open || kind == ``Lean.Parser.Command.namespace
      || kind == ``Lean.Parser.Command.end || kind == ``Lean.Parser.Command.section
      || kind == ``Lean.Parser.Command.universe || kind == ``Lean.Parser.Command.eval then
    -- trivial one-line commands, token-for-token; a MULTI-LINE command
    -- (an `open Ns (long ident list)`) reflows its tokens as a fillSep pool
    if Lean4Fmt.Syntax.hasOwnedLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    if kind == ``Lean.Parser.Command.open && (bareSrc stx).any (· == '\n') then
      let toks := (Lean4Fmt.Emit.leafTokens stx).map
        (fun l => (bareSrc l).trimAscii.toString) |>.filter (fun t => !t.isEmpty)
      if toks.isEmpty || toks.any (·.any (· == '\n')) then
        return (← Lean4Fmt.Emit.verbatim stx)
      match toks.toList with
      | kw :: rest =>
        -- glue parens onto their neighbors (fill items are space-separated)
        let mut items : Array String := #[]
        let mut pfx := ""
        for t in rest do
          if t == "(" then pfx := pfx ++ "("
          else if t == ")" then
            if items.isEmpty then pfx := pfx ++ ")"
            else items := items.set! (items.size - 1) (items[items.size - 1]! ++ ")")
          else
            items := items.push (pfx ++ t)
            pfx := ""
        if !pfx.isEmpty then items := items.push pfx
        let cont := (← read).layout.continuationIndent
        return .text (kw ++ " ") ++ .nest cont (Doc.fillSep (items.toList.map Doc.text))
      | [] => return (← Lean4Fmt.Emit.verbatim stx)
    let mut line := ""
    for c in stx.getArgs do
      let t := Lean4Fmt.Emit.canonTok c
      if t.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
      if !t.isEmpty then line := if line.isEmpty then t else line ++ " " ++ t
    if line.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
    return .text line
  if kind == ``Lean.Parser.Command.in then
    -- `open X in\n<command>` — prefix command token-for-token, the trailed
    -- command walked (usually a declaration; Decl does the real work)
    let a := stx.getArgs
    if a.size != 3 then
      return (← Lean4Fmt.Emit.verbatim stx)
    let preT := Lean4Fmt.Emit.canonTok a[0]!
    if preT.isEmpty || preT.any (· == '\n') then
      return (← Lean4Fmt.Emit.verbatim stx)
    if !((Lean4Fmt.Syntax.trailing? a[1]!).getD "").trimAscii.toString.isEmpty then
      return (← Lean4Fmt.Emit.verbatim stx)
    let some sep := leadingSep? ((Lean4Fmt.Syntax.leading? a[2]!).getD "")
      | return (← Lean4Fmt.Emit.verbatim stx)
    return .text (preT ++ " in") ++ sep ++ (← walk a[2]!)
  if kind != ``Lean.Parser.Command.mutual then
    return (← Lean4Fmt.Emit.verbatim stx)
  let a := stx.getArgs
  if a.size != 3 then
    return (← Lean4Fmt.Emit.verbatim stx)
  if ((a[2]?.map bareSrc).getD "").trimAscii.toString != "end" then
    return (← Lean4Fmt.Emit.verbatim stx)
  -- a comment on the `mutual` line itself has no home in the layout
  if !((Lean4Fmt.Syntax.trailing? a[0]!).getD "").trimAscii.toString.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  let decls := (a[1]?.map (·.getArgs)).getD #[]
  if decls.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  let mut body : Doc := .nil
  for d in decls do
    let some sep := leadingSep? ((Lean4Fmt.Syntax.leading? d).getD "")
      | return (← Lean4Fmt.Emit.verbatim stx)
    let trailT := ((Lean4Fmt.Syntax.trailing? d).getD "").trimAscii.toString
    if trailT.any (· == '\n') then
      return (← Lean4Fmt.Emit.verbatim stx)
    let trailDoc : Doc := if !trailT.isEmpty then .text (" " ++ trailT) else .nil
    let dDoc ← walk d
    -- a member that reproduces as a multi-line RE-ANCHORING block (verbatim)
    -- drifts at +2 (only idempotent at its natural top-level column) — whole
    -- block verbatim. textRaw (multi-line docstrings, comment blocks) emits
    -- RAW at source columns, placement-stable — NOT counted (counting it kept
    -- every mutual with a multi-line-docstring'd member verbatim).
    if Lean4Fmt.Doc.hasMultilineReanchor dDoc then
      return (← Lean4Fmt.Emit.verbatim stx)
    body := body ++ sep ++ dDoc ++ trailDoc
  let some endSep := leadingSep? ((Lean4Fmt.Syntax.leading? a[2]!).getD "")
    | return (← Lean4Fmt.Emit.verbatim stx)
  return .text "mutual" ++ .nest 2 body ++ endSep ++ .text "end"

end Lean4Fmt.Emit.Command
