/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // SYNTAX // KINDS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    SyntaxNodeKind constants and classifiers. One place for kind names so the
    walker reads declaratively and a kind rename touches one file.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import Lean4Fmt.Syntax.Trivia

namespace Lean4Fmt.Syntax

open Lean

/-- A binary-operator notation kind (`«term_+_»`, `«term_<_»`, …). -/
def isBinOp
    (kind : SyntaxNodeKind)
    : Bool :=

  let s := kind.toString
  s.startsWith "«term_" && (s.toList.filter (· == '_')).length >= 2

/-- Kinds that are inline-prone containers: flattening one that carries a line
    comment would let the comment swallow following tokens (§0.4). -/
def isInlineProneContainer
    (kind : SyntaxNodeKind)
    : Bool :=

  kind == ``Lean.Parser.Term.app || kind == ``Lean.Parser.Term.anonymousCtor
      || kind == ``Lean.Parser.Term.match
      || kind == ``Lean.Parser.Term.structInst
      || kind.toString == "«term[_]»"
      || kind.toString == "«term{_}»"

/-- Kinds whose emitters OWN their interior comment seams (the seam model
    pushed into expression space): the entry comment-guard and the value
    span-guard exempt these — their arms place inter-item comments
    structurally, and anything they can't hold falls back internally. -/
def ownsSeams
    (kind : SyntaxNodeKind)
    : Bool :=

  kind == ``Lean.Parser.Term.let || kind == ``Lean.Parser.Term.match
      || kind == ``Lean.Parser.Term.anonymousCtor
      || kind == ``Lean.Parser.Term.structInst
      || kind == ``Lean.Parser.Term.app
      -- the do statement loop owns inter-statement trivia (comments/blanks
      -- place structurally; a statement-interior comment keeps just that
      -- statement verbatim — bytes never drop). Counting do-body comments
      -- at an eqns/match ARM forced whole-decl (and enclosing-mutual)
      -- verbatim for every commented proof-shaped arm.
      || kind == ``Lean.Parser.Term.do
      || kind.toString == "«term[_]»"
      || kind.toString == "«term#[_,]»"

/-- Layout-sensitive / proof kinds that must never be inlined (§0.7 #10). -/
def isNeverInline
    (kind : SyntaxNodeKind)
    : Bool :=

  kind == ``Lean.Parser.Term.byTactic || kind == ``Lean.Parser.Term.have
      || kind == ``Lean.Parser.Term.show
      || kind == ``Lean.Parser.Term.suffices
      || kind == ``Lean.Parser.Term.letrec

/-- Comment hazard EXCLUDING seam-owning descendants: a `match`/`let`/… child
    places its own interior comments structurally (and falls back to a
    multi-line verbatim itself when it cannot — which the parent's
    hasMultilineVerbatim check catches). Counting their subtrees at the parent
    made e.g. `fun c => match … -- comment` verbatim for no reason. The tail
    token's trailing stays exempt (the enclosing seam owns it). -/
partial def hasUnownedLineComment (stx : Lean.Syntax) : Bool :=
  go stx > countLineComments ((lastTokenTrailing? stx).getD "")
where
  go (s : Lean.Syntax) : Nat :=
    match s with
    | .node _ k args =>
      if ownsSeams k then 0
      else args.foldl (fun n c => n + go c) 0
    | _ =>
      countLineComments ((leading? s).getD "")
        + countLineComments ((trailing? s).getD "")

/-- The ARM-SITE variant of the unowned-comment count: (a) the node's OWN
    leading is exempt — the arm loop places it via `leadingSep?`; (b) a
    seam-owning DESCENDANT's HEAD-leading still counts — its emitter owns
    comments BETWEEN its items, not the one before its own first token
    (a comment between `=>` and a `match` body was silently DROPPED when
    the plain ownsSeams cutoff swallowed it — found by the comment diff
    check, the gate is blind to it). -/
partial def hasUnownedInteriorComment (stx : Lean.Syntax) : Bool :=
  goI stx > countLineComments ((leading? stx).getD "")
      + countLineComments ((lastTokenTrailing? stx).getD "")
where
  goI (s : Lean.Syntax) : Nat :=
    match s with
    | .node _ k args =>
      if ownsSeams k then countLineComments ((leading? s).getD "")
      else args.foldl (fun n c => n + goI c) 0
    | _ =>
      countLineComments ((leading? s).getD "")
        + countLineComments ((trailing? s).getD "")

/-- A quotation TERM kind (`Term.quot`, `dynamicQuot`, category quots) —
    `.quot`/`…Quot` names the quotation PARSERS; name-literal kinds
    (`quotedName`) are single tokens — nothing inside them to respace — and
    must NOT poison their whole decl. -/
def isQuotTermKind (k : Lean.SyntaxNodeKind) : Bool :=
  let s := k.toString
  s.endsWith ".quot" || s.endsWith "Quot"

/-- A metaprogram COMMAND whose whole body is quotation content byte-exact
    (arm padding included — the perturber's META guard mirrors this). -/
def isQuotationCommand (k : Lean.SyntaxNodeKind) : Bool :=
  k == `Lean.Parser.Command.macro_rules
    || k == `Lean.Parser.Command.elab_rules
    || k == `Lean.Parser.Command.syntax
    || k == `Lean.Parser.Command.syntaxAbbrev
    || k == `Lean.Parser.Command.notation
    || k == `Lean.Parser.Command.macro
    || k == `Lean.Parser.Command.elab
    || k == `Lean.Parser.Command.mixfix

partial def hasQuotationKind (stx : Lean.Syntax) : Bool :=
  match stx with
  | .node _ k args =>
    isQuotTermKind k || isQuotationCommand k || args.any hasQuotationKind
  | _ => false

/-- Whether the subtree carries one of the byte-exact metaprogram COMMANDS. -/
partial def hasQuotationCommand (stx : Lean.Syntax) : Bool :=
  match stx with
  | .node _ k args => isQuotationCommand k || args.any hasQuotationCommand
  | _ => false

/-- The byte ranges of embedded quotation TERMS (outermost only — interiors
    belong to their quotation). `none` when a quotation has no position info
    (the caller must then treat the WHOLE text as content). -/
partial def quotTermRanges? (stx : Lean.Syntax) : Option (Array (Nat × Nat)) :=
  go stx (some #[])
where
  go (s : Lean.Syntax) (acc : Option (Array (Nat × Nat))) : Option (Array (Nat × Nat)) :=
    match acc with
    | none => none
    | some a =>
      match s with
      | .node _ k args =>
        if isQuotTermKind k then
          match s.getPos?, s.getTailPos? with
          | some p, some q => some (a.push (p.byteIdx, q.byteIdx))
          | _, _ => none
        else args.foldl (fun acc c => go c acc) (some a)
      | _ => some a

/-- A DSL template opener (`[ident|`) anywhere in the text — the lexical
    counterpart of the perturber's TPL_OPEN guard, for source that parses
    under custom template kinds we cannot enumerate. -/
def hasTemplateOpener (s : String) : Bool := Id.run do
  let a : Array Char := s.toList.toArray
  let n := a.size
  for i in [0:n] do
    if a[i]! == '[' && i + 1 < n && (a[i+1]!.isAlpha || a[i+1]! == '_') then
      let mut j := i + 1
      while _hj : j < n && (a[j]!.isAlphanum || a[j]! == '_' || a[j]! == '.') do
        j := j + 1
      if _hj : j < n then
        if a[j]! == '|' then return true
  return false

end Lean4Fmt.Syntax
