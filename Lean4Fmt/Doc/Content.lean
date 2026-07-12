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

import Lean4Fmt.Doc.Core

namespace Lean4Fmt.Doc

/-- Non-whitespace characters of a char list, in order. -/
def nonWsL (cs : List Char) : List Char := cs.filter (fun c => !c.isWhitespace)

/-- Non-whitespace characters of a string, in order. -/
def nonWs (s : String) : List Char := nonWsL s.toList

/-- Drop trailing whitespace (the char-list twin of `trimAsciiEnd`, owned here
    so the Proofs module can reason about it by induction). -/
def trimEndWs (cs : List Char) : List Char :=
  (cs.reverse.dropWhile Char.isWhitespace).reverse

mutual

/-- The content a doc denotes: its visible payloads' non-whitespace characters,
    in order. Structural whitespace (`line`, indent, padding, blanks) denotes
    nothing; table rows carry their cells joined by the (possibly contentful)
    separator; `alignOr` denotes its FALLBACK — the renderer only takes the grid
    when the grid's content provably equals it. -/
def content : Doc → List Char
  | .nil | .line | .softline | .hardline | .blank _ => []
  | .text s => nonWs s
  | .textRaw s => nonWs s
  | .verbatim s _ => nonWs s
  | .cat a b => content a ++ content b
  | .group d | .nest _ d | .align d | .flatten d => content d
  | .alignTable spec rows => contentRows (nonWs spec.sep) rows
  | .alignOr _ _ fb => content fb
  | .fillSep items => contentList items

def contentList : List Doc → List Char
  | [] => []
  | d :: ds => content d ++ contentList ds

/-- One table row: cells' content joined by the separator's content (a row of
    `n` cells carries `n - 1` separators — mirroring `renderRowStr`). -/
def contentRow (sep : List Char) : List Doc → List Char
  | [] => []
  | [d] => content d
  | d :: ds => content d ++ sep ++ contentRow sep ds

def contentRows (sep : List Char) : List (List Doc) → List Char
  | [] => []
  | r :: rs => contentRow sep r ++ contentRows sep rs

end

end Lean4Fmt.Doc
