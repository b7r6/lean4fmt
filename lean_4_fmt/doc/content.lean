/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // DOC // CONTENT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The content denotation of a `Doc`: the non-whitespace characters it commits
    to, in order. `Lean4Fmt/Proofs` proves the renderer emits EXACTLY this
    (`render_content`, unconditionally); the renderer itself consults it at the
    one site where content equality is a layout precondition (`alignOr`'s grid
    vs its fallback), so coherence is enforced by construction, not convention.

    Pure. Depends on Doc.Core only.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.doc.core

namespace Lean4Fmt.Doc

/-- Non-whitespace characters of a char list, in order. -/
def non_ws_l (characters : List Char) : List Char :=
  characters.filter (fun char => !char.isWhitespace)

/-- Non-whitespace characters of a string, in order. -/
def non_ws (source : String) : List Char := non_ws_l source.toList

/-- Drop trailing whitespace (the char-list twin of `trimAsciiEnd`, owned here
    so the Proofs module can reason about it by induction). -/
def trim_end_ws (characters : List Char) : List Char :=
  (characters.reverse.dropWhile Char.isWhitespace).reverse

mutual

  /-- The content a doc denotes: its visible payloads' non-whitespace characters,
    in order. Structural whitespace (`line`, indent, padding, blanks) denotes
    nothing; table rows carry their cells joined by the (possibly contentful)
    separator; `alignOr` denotes its FALLBACK — the renderer only takes the grid
    when the grid's content provably equals it. -/
  def content : Doc → List Char
    | .nil | .line | .softline | .hardline | .blank _ | .pad _ => []
    | .text textValue => non_ws textValue
    | .textRaw textValue => non_ws textValue
    | .verbatim textValue _ => non_ws textValue
    | .cat leftValue rightValue => content leftValue ++ content rightValue
    | .group document | .nest _ document | .align document | .flatten document => content document
    | .alignTable spec rows => contentRows (non_ws spec.sep) rows
    | .align_or _ _ flatBody => content flatBody
    | .fillSep items => contentList items

  def contentList : List Doc → List Char
    | [] => []
    | document :: documents => content document ++ contentList documents

  /-- One table row: cells' content joined by the separator's content (a row of
    `n` cells carries `n - 1` separators — mirroring `renderRowStr`). -/
  def contentRow (sep : List Char) : List Doc → List Char
    | [] => []
    | [document] => content document
    | document :: documents => content document ++ sep ++ contentRow sep documents

  def contentRows (sep : List Char) : List (List Doc) → List Char
    | []          => []
    | row :: rows => contentRow sep row ++ contentRows sep rows

end

end Lean4Fmt.Doc
