/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // LEAN4FMT // DOC // BUILDERS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Combinators over `Doc` — the vocabulary the walker (`Emit`) speaks in. Pure.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Doc.Core

namespace Lean4Fmt.Doc

/-- `a` then `b` separated by a `line` (space when flat, newline when broken). -/
def spaced (a b : Doc) : Doc := a ++ .line ++ b

/-- Intercalate `sep` between docs. -/
def sepBy
    (sep : Doc)
    (ds : Array Doc)
    : Doc :=

  Id.run
    do
      let mut acc := Doc.nil
      let mut first := true
      for d in ds do
        acc := if first then d else acc ++ sep ++ d
        first := false
      return acc

/-- `l` … `r` around `d`, as a group (breaks together). -/
def brackets
    (l r : String)
    (d : Doc)
    : Doc :=

  .group (.text l ++ .nest 2 (.softline ++ d) ++ .softline ++ .text r)

/-- Comma-and-line separated list inside `l`/`r` (breaks all-or-nothing). -/
def commaList (l r : String) (ds : Array Doc) : Doc := brackets l r (sepBy (.text "," ++ .line) ds)

/-- Fill-packed list inside `l`/`r`: items ride the line and wrap at the
    width (continuation at +2), the closer GLUED to the last item — the
    mathlib bracket-list shape. Items must be flat-capable (fillSep). -/
def fillList
    (l r : String)
    (ds : Array Doc)
    : Doc :=

  Id.run
    do
      if ds.isEmpty then return .text (l ++ r)
      let mut items : Array Doc := #[]
      for i in [0:ds.size] do
        items := items.push (if i + 1 == ds.size then ds[i]! ++ .text r else ds[i]! ++ .text ",")
      return .text l ++ .nest 2 (.fillSep items.toList)

/-- Join with a hard newline between each (own-line items). -/
def vcat (ds : Array Doc) : Doc := sepBy .hardline ds

/-- Wrap in a group. -/
@[inline]
def grouped (d : Doc) : Doc := .group d

/-- Indent a block by `n` and put it on its own (broken) line. -/
def indented (n : Int) (d : Doc) : Doc := .nest n (.hardline ++ d)

end Lean4Fmt.Doc
