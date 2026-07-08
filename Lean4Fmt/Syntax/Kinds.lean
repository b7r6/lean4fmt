/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // SYNTAX // KINDS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    SyntaxNodeKind constants and classifiers. One place for kind names so the
    walker reads declaratively and a kind rename touches one file.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean

namespace Lean4Fmt.Syntax

open Lean

/-- A binary-operator notation kind (`«term_+_»`, `«term_<_»`, …). -/
def isBinOp (kind : SyntaxNodeKind) : Bool :=
  let s := kind.toString
  s.startsWith "«term_" && (s.toList.filter (· == '_')).length >= 2

/-- Kinds that are inline-prone containers: flattening one that carries a line
    comment would let the comment swallow following tokens (§0.4). -/
def isInlineProneContainer (kind : SyntaxNodeKind) : Bool :=
  kind == ``Lean.Parser.Term.app
    || kind == ``Lean.Parser.Term.anonymousCtor
    || kind == ``Lean.Parser.Term.match
    || kind == ``Lean.Parser.Term.structInst
    || kind.toString == "«term[_]»"
    || kind.toString == "«term{_}»"

/-- Layout-sensitive / proof kinds that must never be inlined (§0.7 #10). -/
def isNeverInline (kind : SyntaxNodeKind) : Bool :=
  kind == ``Lean.Parser.Term.byTactic
    || kind == ``Lean.Parser.Term.have
    || kind == ``Lean.Parser.Term.show
    || kind == ``Lean.Parser.Term.suffices
    || kind == ``Lean.Parser.Term.letrec

end Lean4Fmt.Syntax
