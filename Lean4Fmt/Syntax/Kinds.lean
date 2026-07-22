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

-- Parser-generated kinds (notation-derived — no Lean-core constant to
-- ``-reference), named ONCE here; every comparison goes through these. The
-- `#guard`s pin each Name literal to the exact string the comparisons
-- previously spelled out — drift between the two spellings is a compile
-- error, not a silent formatter regression.

/-- `[a, b]` list literals. -/
def listLitKind : SyntaxNodeKind := `«term[_]»

/-- `#[a, b]` array literals. -/
def arrayLitKind : SyntaxNodeKind := `«term#[_,]»

/-- `{a}` brace literals. -/
def braceLitKind : SyntaxNodeKind := `«term{_}»

/-- `if c then a else b`. -/
def iteKind : SyntaxNodeKind := `termIfThenElse

/-- `if h : c then a else b`. -/
def diteKind : SyntaxNodeKind := `termDepIfThenElse

#guard listLitKind.toString == "«term[_]»"
#guard arrayLitKind.toString == "«term#[_,]»"
#guard braceLitKind.toString == "«term{_}»"
#guard iteKind.toString == "termIfThenElse"
#guard diteKind.toString == "termDepIfThenElse"

/-- A binary-operator notation kind (`«term_+_»`, `«term_<_»`, …), including
    NAMESPACED scoped notations (`CategoryTheory.«term_≫_»`,
    `Quiver.«term_⟶_»` — the mathlib operator families): the pattern applies
    to the LAST name component. -/
def isBinOp
    (kind : SyntaxNodeKind)
    : Bool :=

  let s := ((kind.components.getLast?.map toString).getD "")
  s.startsWith "«term_" && (s.toList.filter (· == '_')).length >= 2

#guard isBinOp `«term_=_»
#guard isBinOp `CategoryTheory.«term_≫_»
#guard !isBinOp `Lean.Parser.Term.app

/-- A BINDER-COMMA notation (`∑ x ∈ s, body` / `⨆ i, f i` / `∀ᵐ x ∂μ, p` —
    the big-operator and measure families, namespaced or not): a prefix-op
    head, binders, then the BODY after the final comma. Recognized by name
    shape on the last component; binops are excluded (they start `«term_`).
    These all share the binder-predicate layout: head tokens canonical, body
    width-aware at the continuation. -/
def isBinderComma
    (kind : SyntaxNodeKind)
    : Bool :=

  let s := ((kind.components.getLast?.map toString).getD "")
  (s.startsWith "«term" && s.endsWith "_,_»" && !isBinOp kind)
    -- the NAMED big-operator binders (`∑ x ∈ s, body` parses as
    -- `BigOperators.bigsum`, not a «term…» spelling): same
    -- head-comma-body shape, same extended source-exact-head route
    || kind == `BigOperators.bigsum || kind == `BigOperators.bigprod

#guard isBinderComma `BigOperators.bigsum
#guard isBinderComma `Finset.«term∑_∈_,_»
#guard isBinderComma `«term⨆_,_»
#guard isBinderComma `MeasureTheory.«term∀ᵐ_∂_,_»
#guard !isBinderComma `«term_=_»
#guard !isBinderComma `Lean.Parser.Term.app

/-- Term kinds with an ACTIVE MULTI-LINE layout: their `walk` produces a
    width-aware breaking group, so a decl value of one of these may lay out
    actively even when it spans lines. `Decl.isActiveMultiline` consumes
    exactly this set; the walk router consumes `walkTermKinds`, a superset BY
    CONSTRUCTION — so "the emitter handles it but the walker never routes it"
    (the structInst/forall registration-drift class) cannot recur for a
    multi-line kind. -/
def activeMultilineTermKinds
    : Array SyntaxNodeKind :=

  #[
    iteKind,
    diteKind,
    listLitKind,
    arrayLitKind,
    ``Lean.Parser.Term.app,
    ``Lean.Parser.Term.anonymousCtor,
    ``Lean.Parser.Term.fun,
    ``Lean.Parser.Term.tuple,
    ``Lean.Parser.Term.structInst,
    ``Lean.Parser.Term.forall,
    ``Lean.Parser.Term.arrow,
    ``Lean.Parser.Term.paren,
    ``Lean.Parser.Term.let,
    ``Lean.Parser.Term.have,
    ``Lean.Parser.Term.letrec,
    ``Lean.Parser.Term.match
  ]

/-- Every term kind the walker routes to `Term.emit` (binOps ride the
    `isBinOp` predicate beside this array).

    PORTING CHECKLIST — a new term construct registers in: (1) this array —
    or `activeMultilineTermKinds` above when its layout can break (Decl's
    value gate derives from that); (2) its `Term.emit` branch; (3)
    `Tokens.gapRule` when it introduces token-adjacency rules; (4) the
    ws-canon/perturber mirrors when its layout is column-sensitive
    (`Emit/WsSensitivity`). -/
def walkTermKinds
    : Array SyntaxNodeKind :=

  activeMultilineTermKinds
      ++ #[
        `Lean.«term∀__,_»,
        `Lean.«term∃__,_»,
        `«term∃_,_»,
        `«term∀_,_»,
        `«term¬_»,
        ``Lean.Parser.Term.proj,
        ``Lean.Parser.Term.dotIdent,
        ``Lean.Parser.Term.hole,
        ``Lean.Parser.Term.letDecl,
        ``Lean.Parser.Term.letIdDecl,
        ``Lean.Parser.Term.letPatDecl,
        ``Lean.Parser.Term.letIdDeclNoBinders
      ]

/-- Kinds that are inline-prone containers: flattening one that carries a line
    comment would let the comment swallow following tokens (§0.4). -/
def isInlineProneContainer
    (kind : SyntaxNodeKind)
    : Bool :=

  kind == ``Lean.Parser.Term.app || kind == ``Lean.Parser.Term.anonymousCtor
      || kind == ``Lean.Parser.Term.match
      || kind == ``Lean.Parser.Term.structInst
      || kind == listLitKind
      || kind == braceLitKind

/-- Kinds whose emitters OWN their interior comment seams (the seam model
    pushed into expression space): the entry comment-guard and the value
    span-guard exempt these — their arms place inter-item comments
    structurally, and anything they can't hold falls back internally. -/
def ownsSeams
    (kind : SyntaxNodeKind)
    : Bool :=

  kind == ``Lean.Parser.Term.let || kind == ``Lean.Parser.Term.have
    || kind == ``Lean.Parser.Term.match
      || kind == ``Lean.Parser.Term.anonymousCtor
      || kind == ``Lean.Parser.Term.structInst
      || kind == ``Lean.Parser.Term.app
      -- the do statement loop owns inter-statement trivia (comments/blanks
      -- place structurally; a statement-interior comment keeps just that
      -- statement verbatim — bytes never drop). Counting do-body comments
      -- at an eqns/match ARM forced whole-decl (and enclosing-mutual)
      -- verbatim for every commented proof-shaped arm.
      || kind == ``Lean.Parser.Term.do
      -- by is do's proof twin: the tactic sequence loop owns inter-tactic
      -- trivia the same way (per-tactic verbatim fallback; bytes never
      -- drop). Its absence made any TERM wrapping a comment-bearing by
      -- (`fun x ↦ by …` values, the mathlib structInst-field idiom) bail
      -- wholesale at the entry guard before its handler ran.
      || kind == ``Lean.Parser.Term.byTactic
      || kind == `Lean.Parser.Term.byTactic'
      || kind == listLitKind
      || kind == arrayLitKind

/-- A `fun` whose body is a `by`/`do` block: the wrapper adds only flat head
    text before the block, so a binding seam's block-glue argument passes
    through it (`x := fun a ↦ by` + body below). The match-alternative form
    (`fun | pat => …`) is not this shape. -/
def isFunBlockValue
    (v : Lean.Syntax)
    : Bool :=

  v.getKind == ``Lean.Parser.Term.fun
      && (match v.getArgs[1]? with
      | some bf =>
        bf.getKind == ``Lean.Parser.Term.basicFun
            && (match bf.getArgs.back? with
            | some b =>
              b.getKind == ``Lean.Parser.Term.do || b.getKind == ``Lean.Parser.Term.byTactic
            | none => false)
      | none => false)

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
partial def hasUnownedLineComment
            (stx : Lean.Syntax)
            : Bool :=

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
partial def hasUnownedInteriorComment
            (stx : Lean.Syntax)
            : Bool :=

  goI stx
      > countLineComments ((leading? stx).getD "")
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
def isQuotTermKind
    (k : Lean.SyntaxNodeKind)
    : Bool :=

  let s := k.toString
  s.endsWith ".quot" || s.endsWith "Quot"

/-- A metaprogram COMMAND whose whole body is quotation content byte-exact
    (arm padding included — the perturber's META guard mirrors this). -/
def isQuotationCommand
    (k : Lean.SyntaxNodeKind)
    : Bool :=

  k == `Lean.Parser.Command.macro_rules || k == `Lean.Parser.Command.elab_rules
      || k == `Lean.Parser.Command.syntax
      || k == `Lean.Parser.Command.syntaxAbbrev
      || k == `Lean.Parser.Command.notation
      || k == `Lean.Parser.Command.macro
      || k == `Lean.Parser.Command.elab
      || k == `Lean.Parser.Command.mixfix

partial def hasQuotationKind
            (stx : Lean.Syntax)
            : Bool :=

  match stx with
  | .node _ k args => isQuotTermKind k || isQuotationCommand k || args.any hasQuotationKind
  | _              => false

/-- Whether the subtree carries one of the byte-exact metaprogram COMMANDS. -/
partial def hasQuotationCommand
            (stx : Lean.Syntax)
            : Bool :=

  match stx with
  | .node _ k args => isQuotationCommand k || args.any hasQuotationCommand
  | _              => false

/-- Bytes of CONTENT-BY-POLICY nodes (module docstrings, the header, quotation
    commands): permanently verbatim by design, NOT portable residue — the
    honest porting tail is `verbatim - policy`, and `--stats` reports the
    coverage ceiling from it. Bare-source sizes match what `verbatim` emits
    (modulo ws-canon: an accounting approximation, not an invariant). -/
partial def policyContentBytes
            (stx : Lean.Syntax)
            : Nat :=

  match stx with
  | .node _ k args =>
    if k == ``Lean.Parser.Module.header || k == `Lean.Parser.Command.moduleDoc
        || isQuotationCommand k then
      ((stx.getSubstring? false false).map (·.toString.utf8ByteSize)).getD 0
    else
      args.foldl (fun n c => n + policyContentBytes c) 0
  | _ => 0

/-- The byte ranges of embedded quotation TERMS (outermost only — interiors
    belong to their quotation). `none` when a quotation has no position info
    (the caller must then treat the WHOLE text as content). -/
partial def quotTermRanges?
            (stx : Lean.Syntax)
            : Option (Array (Nat × Nat)) :=

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
def hasTemplateOpener
    (s : String)
    : Bool :=

  Id.run do
    let a : Array Char := s.toList.toArray
    let n := a.size
    for i in [0:n] do
      if a[i]! == '[' && i + 1 < n && (a[i+1]!.isAlpha || a[i+1]! == '_') then
        let mut j := i + 1
        while _hj : j < n && (a[j]!.isAlphanum || a[j]! == '_' || a[j]! == '.') do
          j := j + 1
        if _hj : j < n then
          if a[j]! == '|' then
            return true
    return false

end Lean4Fmt.Syntax
