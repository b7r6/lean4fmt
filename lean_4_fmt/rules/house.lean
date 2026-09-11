/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // LEAN4FMT // RULES // HOUSE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Structural hazards from the Straylight systems-Lean house style. Diagnostic
    only: these identify refactor candidates; the formatter never changes program
    structure to satisfy them.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import lean_4_fmt.rules.diagnostic
import lean_4_fmt.style.options

namespace Lean4Fmt.Rules.House

open Lean
open Lean4Fmt.Style

private
def source_of? (stx : Syntax) : Option String := (stx.getSubstring? false false).map (·.toString)

private
def pos_of (stx : Syntax) : Nat := (stx.getRange?.map (·.start.byteIdx)).getD 0

private
def line_count (src : String) : Nat := (src.splitOn "\n").length

private
def occurrence_count (needle src : String) : Nat := (src.splitOn needle).length - 1

private
def stanza_break_count (src : String) : Nat :=
  let lines := src.splitOn "\n"
  let body := (lines.dropWhile (fun line => !(line.contains ":="))).drop 1
  (body.zip body.tail).foldl
    (
      fun count pair =>
        let current := pair.1.trimAscii
        let next := pair.2.trimAscii
        let structuralContinuation :=
          next.startsWith "where" || next.startsWith "termination_by"
              || next.startsWith "decreasing_by"
        if current.isEmpty && !next.isEmpty && !next.startsWith "--" && !next.startsWith "/-"
            && !structuralContinuation then
          count + 1
        else
          count
    )
    0

private partial
def first_do_seq? (stx : Syntax) : Option Syntax :=
  if stx.getKind == ``Lean.Parser.Term.doSeqIndent then
    some stx
  else
    stx.getArgs.findSome? first_do_seq?

private
def do_statement_count (stx : Syntax) : Nat :=
  match first_do_seq? stx with
  | none => 1
  | some sequence =>
    sequence.getArgs.foldl
      (
        fun count group =>
          count
              + group.getArgs.foldl
                (
                  fun inner child =>
                    if child.getKind == ``Lean.Parser.Term.doSeqItem then inner + 1 else inner
                )
                0
      )
      0

private
def is_bind_operator (stx : Syntax) : Bool := stx.isAtom && source_of? stx == some ">>="

private
def is_direct_bind_chain (stx : Syntax) : Bool := stx.getArgs.any is_bind_operator

private
def is_decl_body_kind (kind : Name) : Bool :=
  kind == ``Lean.Parser.Command.definition || kind == ``Lean.Parser.Command.theorem
      || kind == ``Lean.Parser.Command.opaque
      || kind == ``Lean.Parser.Command.abbrev
      || kind == ``Lean.Parser.Command.instance

private
def is_handler_decl_kind (kind : Name) : Bool :=
  kind == ``Lean.Parser.Command.definition || kind == ``Lean.Parser.Command.opaque

private
def is_declaration_value_kind (kind : Name) : Bool :=
  kind == ``Lean.Parser.Command.declValSimple || kind == ``Lean.Parser.Command.declValEqns
      || kind == ``Lean.Parser.Command.whereStructInst

private
def is_dispatch_kind (kind : Name) : Bool :=
  kind == ``Lean.Parser.Command.declValEqns || kind == ``termIfThenElse
      || kind == ``termDepIfThenElse
      || kind == ``Lean.Parser.Term.doIf
      || kind == ``Lean.Parser.Term.elseIf
      || kind == ``Lean.Parser.Term.doUnless
      || kind == ``Lean.Parser.Term.termUnless
      || kind == ``Lean.Parser.Term.match
      || kind == ``Lean.Parser.Term.doMatch
      || kind == ``Lean.Parser.Term.matchExpr
      || kind == ``Lean.Parser.Term.doMatchExpr
      || kind == ``Lean.Parser.Term.doFor
      || kind == ``Lean.Parser.Term.termFor
      || kind == ``Lean.Parser.Term.doWhile
      || kind == ``Lean.Parser.Term.doRepeat
      || kind == ``Lean.Parser.Term.doRepeatUntil

private
def is_nested_declaration_kind (kind : Name) : Bool :=
  is_decl_body_kind kind || kind == ``Lean.Parser.Term.letRecDecl

private partial
def branch_count (root : Syntax) (stx : Syntax) : Nat :=
  if stx != root && is_nested_declaration_kind stx.getKind then
    0
  else
    let here := if is_dispatch_kind stx.getKind then 1 else 0
    stx.getArgs.foldl (fun count child => count + branch_count root child) here

private
def declaration_branch_count (stx : Syntax) : Nat :=
  match stx.getArgs.find? (is_declaration_value_kind ·.getKind) with
  | some body => branch_count body body
  | none      => 0

private partial
def identifier_count : Syntax → Nat
  | .ident ..      => 1
  | .node _ _ args => args.foldl (fun count child => count + identifier_count child) 0
  | _              => 0

private
def binder_name_count (children : Array Syntax) : Nat :=
  (
    children.foldl
      (
        fun (count, inType) child =>
          if inType then
            (count, true)
          else
            let source := (source_of? child).getD ""
            if child.getKind == ``Lean.Parser.Term.typeSpec || source.contains ':' then
              (count, true)
            else
              (count + identifier_count child, false)
      )
      (0, false)
  ).1

private
def explicit_binder_parameter_count (binder : Syntax) : Nat :=
  if binder.isIdent then
    1
  else if binder.getKind == ``Lean.Parser.Term.explicitBinder then
    let args := binder.getArgs
    if args.size < 3 then 0 else binder_name_count (args.extract 1 (args.size - 1))
  else
    0

private
def declaration_parameter_count (stx : Syntax) : Nat :=
  match stx.getArgs.find? (·.getKind == ``Lean.Parser.Command.declSig) with
  | none => 0
  | some signature =>
    match signature.getArgs[0]? with
    | none => 0
    | some binders =>
      binders.getArgs.foldl (fun count binder => count + explicit_binder_parameter_count binder) 0

private
def lint_stanza_breaks
    (policy : Linting)
    (stx : Syntax)
    (src : String)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  let count :=
    if is_handler_decl_kind stx.getKind && policy.requireStanzaComments then
      stanza_break_count src
    else
      0
  if count == 0 then
    found
  else
    found.push
      { severity := .info,
        pos := pos_of stx,
        rule := "house/stanza-comment",
        message := s!"declaration has {count} uncommented blank-line stanza breaks; introduce each next block with a one-line imperative comment" }

private
def lint_declaration
    (policy : Linting)
    (stx : Syntax)
    (src : String)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  let lines := line_count src
  let found :=
    if lines > 60 then
      found.push
        { severity := .info,
          pos := pos_of stx,
          rule := "house/function-size",
          message := s!"declaration spans {lines} lines; extract screen-sized handlers (target ≈50)" }
    else
      found
  let parameters := declaration_parameter_count stx
  let found :=
    if is_handler_decl_kind stx.getKind && policy.handlerParameterMax > 0
        && parameters > policy.handlerParameterMax then
      found.push
        { severity := .info,
          pos := pos_of stx,
          rule := "house/handler-parameter-pack",
          message := s!"declaration has {parameters} explicit value parameters; bundle context/state or keep at most {policy.handlerParameterMax}" }
    else
      found
  let branches := declaration_branch_count stx
  let found :=
    if is_handler_decl_kind stx.getKind && policy.branchDensityMax > 0
        && branches > policy.branchDensityMax then
      found.push
        { severity := .info,
          pos := pos_of stx,
          rule := "house/branch-density",
          message := s!"executable definition has {branches} direct dispatch points; extract cohesive named handlers or keep at most {policy.branchDensityMax}" }
    else
      found
  let found := lint_stanza_breaks policy stx src found
  let muts := occurrence_count "let mut " src
  if muts ≥ 3 then
    found.push
      { severity := .info,
        pos := pos_of stx,
        rule := "house/state-bundle",
        message := s!"declaration introduces {muts} mutable locals; consider a threaded state structure" }
  else
    found

private
def lint_match_alt (stx : Syntax) (found : Array Diagnostic) : Array Diagnostic :=
  match stx.getArgs.back? with
  | some body =>
    let operations := do_statement_count body
    let found :=
      if operations > 1 then
        found.push
          { severity := .info,
            pos      := pos_of stx,
            rule     := "house/match-arm-operations",
            message  := s!"match arm contains {operations} do statements; extract a named handler" }
      else
        found
    if is_direct_bind_chain body then
      found.push
        { severity := .info,
          pos := pos_of stx,
          rule := "house/match-arm-bind-chain",
          message := "match arm uses a direct `>>=` continuation; prefer a clear `do` block or named handler" }
    else
      found
  | none => found

private partial
def visit (policy : Linting) (stx : Syntax) (found : Array Diagnostic) : Array Diagnostic :=
  let found :=
    if is_decl_body_kind stx.getKind then
      match source_of? stx with
      | some src => lint_declaration policy stx src found
      | none     => found
    else if stx.getKind == ``Lean.Parser.Term.matchAlt then lint_match_alt stx found else found
  stx.getArgs.foldl (fun result child => visit policy child result) found

/-- Structural house-style hazards over the parsed module. -/
def lint (style : Style) (stx : Syntax) : Array Diagnostic := visit style.linting stx #[]

example : stanza_break_count "def f := do\n\n  action" = 1 := by native_decide

example : stanza_break_count "def f := do\n\n  -- perform the action.\n  action" = 0 := by
  native_decide

example : stanza_break_count "def f := value\n\nwhere\n  value := 1" = 0 := by native_decide

end Lean4Fmt.Rules.House
