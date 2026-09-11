/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // LEAN4FMT // DOC // BUILDERS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Combinators over `Doc` — the vocabulary the walker (`Emit`) speaks in. Pure.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.doc.core

namespace Lean4Fmt.Doc

/-- `a` then `b` separated by a `line` (space when flat, newline when broken). -/
def spaced (leftValue rightValue : Doc) : Doc := leftValue ++ .line ++ rightValue

/-- Intercalate `sep` between docs. -/
def sep_by (sep : Doc) (documents : Array Doc) : Doc :=
  Id.run do
    let mut output := Doc.nil
    let mut first := true
    for document in documents do
      output := if first then document else output ++ sep ++ document
      first := false
    return output

/-- `l` … `r` around `d`, as a group (breaks together). -/
def brackets (lineValue result : String) (document : Doc) : Doc :=
  .group (.text lineValue ++ .nest 2 (.softline ++ document) ++ .softline ++ .text result)

/-- Comma-and-line separated list inside `l`/`r` (breaks all-or-nothing). -/
def comma_list (lineValue result : String) (documents : Array Doc) : Doc :=
  brackets lineValue result (sep_by (.text "," ++ .line) documents)

/-- Fill-packed list inside `l`/`r`: items ride the line and wrap at the
    width (continuation at +2), the closer GLUED to the last item — the
    mathlib bracket-list shape. Items must be flat-capable (fillSep). -/
def fill_list (lineValue result : String) (documents : Array Doc) : Doc :=
  Id.run do
    if documents.isEmpty then
      return .text (lineValue ++ result)
    let mut items : Array Doc := #[]
    for idx in [0:documents.size] do
      items :=
        items.push
          (
            if idx + 1 == documents.size then
              documents[idx]! ++ .text result
            else
              documents[idx]! ++ .text ","
          )
    return .text lineValue ++ .nest 2 (.fillSep items.toList)

/-- Join with a hard newline between each (own-line items). -/
def vcat (documents : Array Doc) : Doc := sep_by .hardline documents

/-- Wrap in a group. -/
@[inline]
def grouped (document : Doc) : Doc := .group document

/-- Indent a block by `n` and put it on its own (broken) line. -/
def indented (count : Int) (document : Doc) : Doc := .nest count (.hardline ++ document)

end Lean4Fmt.Doc
