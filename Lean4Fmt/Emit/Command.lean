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
import Lean4Fmt.Syntax.Trivia

namespace Lean4Fmt.Emit.Command

open Lean Lean4Fmt.Doc Lean4Fmt.Emit

/-- One constructor `(/-- doc -/)? | (modifiers)? name (binders)* (: τ)?`, as a
    single line (the doc comment on its own line above). `none` on a multi-line
    piece or a structural surprise — the caller reproduces the whole
    declaration. -/
private def ctorDoc?
            (c : Lean.Syntax)
            : Option Doc := Id.run do
  if c.getKind != ``Lean.Parser.Command.ctor then return none
  let a := c.getArgs
  if a.size != 5 then return none
  let docT := (bareSrc a[0]!).trimAscii.toString
  let modsT := (bareSrc a[2]!).trimAscii.toString
  let nameT := (bareSrc a[3]!).trimAscii.toString
  if nameT.isEmpty || nameT.any (· == '\n') || modsT.any (· == '\n') then return none
  let sig := a[4]!.getArgs
  let mut parts : Array String := #[]
  for b in ((sig[0]?).map (·.getArgs)).getD #[] do
    let t := (bareSrc b).trimAscii.toString
    if t.any (· == '\n') then return none
    parts := parts.push t
  let tyT ← do
    match ((sig[1]?).map (·.getArgs)).getD #[] |>.toList with
    | [ts] =>
      let t := (bareSrc ((ts.getArgs[1]?).getD .missing)).trimAscii.toString
      if t.isEmpty || t.any (· == '\n') then return none
      pure (some t)
    | [] => pure (none : Option String)
    | _ => return none
  let line := "| " ++ (if modsT.isEmpty then "" else modsT ++ " ") ++ nameT
    ++ (parts.foldl (fun s p => s ++ " " ++ p) "")
    ++ (match tyT with | some t => " : " ++ t | none => "")
  -- the doc comment is byte-exact on its own line above (it may be multi-line;
  -- it sits at a hardline position, literal emission is the stable choice)
  let docD : Doc := if docT.isEmpty then .nil else .textRaw docT ++ .hardline
  return some (docD ++ .text line)

/-- Active layout for a `where`-style `inductive` body (the declaration node
    WITHOUT its modifiers — `Decl.emit` places those). `none` when this layout
    can't hold the input faithfully. -/
def inductiveDoc?
    (defn : Lean.Syntax)
    : Option Doc := Id.run do
  let a := defn.getArgs
  if a.size != 7 then return none
  -- head: `inductive Name <binders> (: τ)? where` — one line, token-for-token
  let idT := (bareSrc a[1]!).trimAscii.toString
  if idT.isEmpty || idT.any (· == '\n') then return none
  let sig := a[2]!.getArgs
  let mut head := "inductive " ++ idT
  for b in ((sig[0]?).map (·.getArgs)).getD #[] do
    let t := (bareSrc b).trimAscii.toString
    if t.any (· == '\n') then return none
    head := head ++ " " ++ t
  match ((sig[1]?).map (·.getArgs)).getD #[] |>.toList with
  | [ts] =>
    let t := (bareSrc ((ts.getArgs[1]?).getD .missing)).trimAscii.toString
    if t.isEmpty || t.any (· == '\n') then return none
    head := head ++ " : " ++ t
  | [] => pure ()
  | _ => return none
  -- `where` must be present (old `:=`-style bodies stay verbatim), computed
  -- fields must be absent
  if ((a[3]?.map bareSrc).getD "").trimAscii.toString != "where" then return none
  if !((a[5]?.map bareSrc).getD "").trimAscii.toString.isEmpty then return none
  -- a comment on the `where` line itself has no home in the layout
  if !((Lean4Fmt.Syntax.trailing? a[3]!).getD "").trimAscii.toString.isEmpty then return none
  head := head ++ " where"
  -- constructors, one per line at +2. The loop OWNS the inter-ctor trivia (the
  -- seam model): each ctor's leading comment/blank lines are placed
  -- structurally before it, and a same-line trailing comment is re-appended —
  -- the LAST ctor's trailing belongs to the deriving/enclosing seam. A comment
  -- INSIDE a ctor (between its tokens) has no seam — whole-decl verbatim.
  let ctors := (a[4]?.map (·.getArgs)).getD #[]
  if ctors.isEmpty then return none
  -- deriving (its leading trivia placed structurally, so blank groups before
  -- it survive), token-for-token
  let derT := ((a[6]?.map bareSrc).getD "").trimAscii.toString
  if derT.any (· == '\n') then return none
  let hasDer := !derT.isEmpty
  let some derSep :=
    (if hasDer then leadingSep? ((Lean4Fmt.Syntax.leading? a[6]!).getD "") else some Doc.nil)
    | return none
  let mut body : Doc := .nil
  for h : i in [0:ctors.size] do
    let c := ctors[i]
    if Lean4Fmt.Syntax.interiorHasLineComment c then return none
    let trailT := ((Lean4Fmt.Syntax.trailing? c).getD "").trimAscii.toString
    let last := i + 1 == ctors.size
    -- the LAST ctor's trailing belongs to the enclosing seam (Module) — unless
    -- `deriving` follows, in which case the loop owns it like any other
    let owned := !last || hasDer
    if owned && trailT.any (· == '\n') then return none
    let trailDoc : Doc := if owned && !trailT.isEmpty then .text (" " ++ trailT) else .nil
    let some sep := leadingSep? ((Lean4Fmt.Syntax.leading? c).getD "") | return none
    let some d := ctorDoc? c | return none
    body := body ++ sep ++ d ++ trailDoc
  let derD : Doc := if hasDer then derSep ++ .text derT else .nil
  return some (.text head ++ .nest 2 (body ++ derD))

/-- One structure field `(/-- doc -/)? (modifiers)? name (binders)* : τ (:= v)?`,
    as a single line (the doc comment on its own line above — it lives INSIDE
    the field's declModifiers, unlike a ctor's). `none` on a multi-line piece,
    a parenthesized field group (`structExplicitBinder`), or a structural
    surprise. -/
private def fieldDoc?
            (f : Lean.Syntax)
            : Option Doc := Id.run do
  if f.getKind != ``Lean.Parser.Command.structSimpleBinder then return none
  let a := f.getArgs
  if a.size != 4 then return none
  let margs := (a[0]?.map (·.getArgs)).getD #[]
  let docT := ((margs[0]?.map bareSrc).getD "").trimAscii.toString
  let mut modsT := ""
  for m in margs.toList.drop 1 do
    let t := (bareSrc m).trimAscii.toString
    if t.any (· == '\n') then return none
    if !t.isEmpty then modsT := modsT ++ t ++ " "
  let nameT := (bareSrc a[1]!).trimAscii.toString
  if nameT.isEmpty || nameT.any (· == '\n') then return none
  let sig := a[2]!.getArgs
  let mut parts : Array String := #[]
  for b in ((sig[0]?).map (·.getArgs)).getD #[] do
    let t := (bareSrc b).trimAscii.toString
    if t.any (· == '\n') then return none
    parts := parts.push t
  let tyT ← do
    match ((sig[1]?).map (·.getArgs)).getD #[] |>.toList with
    | [ts] =>
      let t := (bareSrc ((ts.getArgs[1]?).getD .missing)).trimAscii.toString
      if t.isEmpty || t.any (· == '\n') then return none
      pure (some t)
    | [] => pure (none : Option String)
    | _ => return none
  let defT := ((a[3]?.map bareSrc).getD "").trimAscii.toString
  if defT.any (· == '\n') then return none
  let line := modsT ++ nameT
    ++ (parts.foldl (fun s p => s ++ " " ++ p) "")
    ++ (match tyT with | some t => " : " ++ t | none => "")
    ++ (if defT.isEmpty then "" else " " ++ defT)
  let docD : Doc := if docT.isEmpty then .nil else .textRaw docT ++ .hardline
  return some (docD ++ .text line)

/-- Active layout for a `structure`/`class` declaration (WITHOUT its modifiers —
    `Decl.emit` places those): head on one line
    (`structure Name <binders> (: τ)? (extends …)? where`), one field per line
    at +2 via the seam-owning item loop, `deriving` at +2 below. `none` when
    this layout can't hold the input (an explicit `mk ::`, parenthesized field
    groups, comments in seamless zones, multi-line pieces). -/
def structureDoc?
    (defn : Lean.Syntax)
    : Option Doc := Id.run do
  let a := defn.getArgs
  if a.size != 6 then return none
  let kwT := (bareSrc a[0]!).trimAscii.toString
  if kwT.isEmpty || kwT.any (· == '\n') then return none
  let idT := (bareSrc a[1]!).trimAscii.toString
  if idT.isEmpty || idT.any (· == '\n') then return none
  let sig := a[2]!.getArgs
  let mut head := kwT ++ " " ++ idT
  for b in ((sig[0]?).map (·.getArgs)).getD #[] do
    let t := (bareSrc b).trimAscii.toString
    if t.any (· == '\n') then return none
    head := head ++ " " ++ t
  match ((sig[1]?).map (·.getArgs)).getD #[] |>.toList with
  | [ts] =>
    let t := (bareSrc ((ts.getArgs[1]?).getD .missing)).trimAscii.toString
    if t.isEmpty || t.any (· == '\n') then return none
    head := head ++ " : " ++ t
  | [] => pure ()
  | _ => return none
  let extT := ((a[3]?.map bareSrc).getD "").trimAscii.toString
  if extT.any (· == '\n') then return none
  if !extT.isEmpty then head := head ++ " " ++ extT
  -- deriving, shared with the fieldless form
  let derT := ((a[5]?.map bareSrc).getD "").trimAscii.toString
  if derT.any (· == '\n') then return none
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
  let mut body : Doc := .nil
  for h : i in [0:fields.size] do
    let f := fields[i]
    if Lean4Fmt.Syntax.interiorHasLineComment f then return none
    let trailT := ((Lean4Fmt.Syntax.trailing? f).getD "").trimAscii.toString
    let last := i + 1 == fields.size
    let owned := !last || hasDer
    if owned && trailT.any (· == '\n') then return none
    let trailDoc : Doc := if owned && !trailT.isEmpty then .text (" " ++ trailT) else .nil
    let some sep := leadingSep? ((Lean4Fmt.Syntax.leading? f).getD "") | return none
    let some d := fieldDoc? f | return none
    body := body ++ sep ++ d ++ trailDoc
  return some (.text head ++ .nest 2 (body ++ derD))

/-- Emit the Command construct rooted at `stx`, recursing via `walk`. -/
def emit
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.EmitM Doc :=

  let _ := walk
  Lean4Fmt.Emit.verbatim stx

end Lean4Fmt.Emit.Command
