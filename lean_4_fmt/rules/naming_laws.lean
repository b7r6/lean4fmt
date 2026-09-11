/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // LEAN4FMT // RULES // NAMING LAWS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Focused checks for syntax-derived binding roles. Classification is policy
    input, not an exemption: patterns, match arms, and tactics remain diagnostic
    until an explicit tree-local policy changes that decision.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.rules.naming

namespace Lean4Fmt.Rules.Naming

open Lean Lean4Fmt.Style

/-- The binding manifest has one authoritative classification per parser kind. -/
example : (binding_kind_inventory.map (·.1)).Nodup := by native_decide

/-- Every manifest entry is recovered exactly by the public classifier. -/
example : binding_kind_inventory.all (fun entry => role_of_kind entry.1 == some entry.2) = true := by
  native_decide

example : role_of_kind ``Lean.Parser.Command.declId = some .declaration := by decide
example : role_of_kind ``Lean.Parser.Command.ctor = some .declaration := by decide
example : role_of_kind ``Lean.Parser.Term.explicitBinder = some .parameterBinder := by decide
example : role_of_kind ``Lean.Parser.Term.basicFun = some .lambdaBinder := by decide
example : role_of_kind ``Lean.Parser.Term.letIdDecl = some .letBinder := by decide
example : role_of_kind ``Lean.Parser.Term.letRecDecl = some .recursiveHelper := by decide
example : role_of_kind ``Lean.Parser.Term.letPatDecl = some .patternBinder := by decide
example : role_of_kind ``Lean.Parser.Term.matchAlt = some .matchBinder := by decide
example : role_of_kind ``Lean.Parser.Term.doForDecl = some .loopIndex := by decide
example : role_of_kind ``Lean.Parser.Term.instBinder = some .instanceBinder := by decide
example : role_of_kind ``Lean.Parser.Tactic.intro = some .tacticBinder := by decide
example : role_of_kind `Lean.Parser.Tactic.«tacticNext_=>_» = some .tacticBinder := by decide
example : role_of_kind `«tacticBy_cases_:_» = some .tacticBinder := by decide
example : role_of_kind `Lean.Parser.Tactic.tacticSuffices_ = some .tacticBinder := by decide
example : role_of_kind ``Lean.Parser.Tactic.generalize = some .tacticBinder := by decide
example : role_of_kind ``Lean.Parser.Tactic.inductionAltLHS = some .tacticBinder := by decide
example : role_of_kind `Lean.Parser.Tactic.rcasesPat.one = some .tacticBinder := by decide
example : role_of_kind ``Lean.Parser.Tactic.tacticHave__ = some .tacticBinder := by decide
example : role_of_kind `Lean.Parser.Tactic.tacticLet__ = some .tacticBinder := by decide
example : role_of_kind `Lean.Parser.Tactic.tacticHaveI__ = some .tacticBinder := by decide
example : role_of_kind `Lean.Parser.Tactic.tacticLetI__ = some .tacticBinder := by decide
example : role_of_kind ``Lean.Parser.Tactic.replace = some .tacticBinder := by decide
example : role_of_kind `Lean.Parser.Tactic.tacticHave' = some .tacticBinder := by decide
example : role_of_kind `Lean.Parser.Tactic.tacticLet'__ = some .tacticBinder := by decide
example : role_of_kind ``Lean.Parser.Tactic.letrec = some .tacticBinder := by decide
example : role_of_kind ``Lean.Parser.Tactic.elimTarget = some .tacticBinder := by decide
example : role_of_kind `Lean.Parser.Tactic.injection = some .tacticBinder := by decide

example : diagnostic_by_default .patternBinder = true := by decide
example : diagnostic_by_default .matchBinder = true := by decide
example : diagnostic_by_default .tacticBinder = true := by decide

example : traditional_instance_name "α" = true := by native_decide
example : traditional_instance_name "α₁" = true := by native_decide
example : traditional_instance_name "א₂" = true := by native_decide
example : traditional_instance_name "inst" = false := by native_decide
example : traditional_instance_name "αName" = false := by native_decide

private
def strict_style : Style := { (default : Style) with
  linting.symbolMinChars := 20
  linting.allowGreekSymbols := false
  linting.allowHebrewSymbols := false
  linting.allowTraditionalInstances := false
}

private
def symbol_length_count (stx : Syntax) : Nat :=
  (lint strict_style stx).foldl
    (fun count diagnostic => if diagnostic.rule == "symbol-length" then count + 1 else count)
    0

private
def role_count (stx : Syntax) (role : String) : Nat :=
  (lint strict_style stx).foldl
    (
      fun count diagnostic =>
        if diagnostic.rule == "symbol-length" && diagnostic.role == role then count + 1 else count
    )
    0

private
def semantic_pattern_style : Style :=
  { strict_style with linting.requireSemanticPatternBinders := true }

private
def semantic_pattern_rule_count (stx : Syntax) : Nat :=
  (lint semantic_pattern_style stx).foldl
    (
      fun count diagnostic =>
        if diagnostic.rule == "symbol-pattern-binder" then count + 1 else count
    )
    0

private
def semantic_recursive_helper_style : Style :=
  { strict_style with linting.requireSemanticRecursiveHelperNames := true }

private
def recursive_helper_rule_count (style : Style) (stx : Syntax) : Nat :=
  (lint style stx).foldl
    (
      fun count diagnostic =>
        if diagnostic.rule == "symbol-recursive-helper" then count + 1 else count
    )
    0

private
def generic_recursive_helper_count (style : Style) (stx : Syntax) : Nat :=
  (lint style stx).foldl
    (
      fun count diagnostic =>
        if diagnostic.rule == "symbol-length" && diagnostic.role == "recursive-helper" then
          count + 1
        else
          count
    )
    0

private
def semantic_lambda_style : Style :=
  { strict_style with linting.requireSemanticLambdaNames := true }

private
def semantic_let_style : Style := { strict_style with linting.requireSemanticLetNames := true }

private
def lambda_rule_count (style : Style) (stx : Syntax) : Nat :=
  (lint style stx).foldl
    (fun count diagnostic => if diagnostic.rule == "symbol-lambda" then count + 1 else count)
    0

private
def generic_lambda_count (style : Style) (stx : Syntax) : Nat :=
  (lint style stx).foldl
    (
      fun count diagnostic =>
        if diagnostic.rule == "symbol-length" && diagnostic.role == "lambda-binder" then
          count + 1
        else
          count
    )
    0

private
def let_rule_count (style : Style) (stx : Syntax) : Nat :=
  (lint style stx).foldl
    (fun count diagnostic => if diagnostic.rule == "symbol-let" then count + 1 else count)
    0

private
def generic_let_count (style : Style) (stx : Syntax) : Nat :=
  (lint style stx).foldl
    (
      fun count diagnostic =>
        if diagnostic.rule == "symbol-length" && diagnostic.role == "let-binder" then
          count + 1
        else
          count
    )
    0

private
def instance_style : Style := { strict_style with linting.requireTraditionalInstances := true }

private
def instance_rule_count (stx : Syntax) : Nat :=
  (lint instance_style stx).foldl
    (fun count diagnostic => if diagnostic.rule == "symbol-instance" then count + 1 else count)
    0

private
def semantic_field_style : Style := { strict_style with linting.requireSemanticFieldNames := true }

private
def semantic_field_rule_count (style : Style) (stx : Syntax) : Nat :=
  (lint style stx).foldl
    (fun count diagnostic => if diagnostic.rule == "symbol-field" then count + 1 else count)
    0

private
def packet_field_shape : Syntax := Unhygienic.run `(command| structure Packet where api : Nat)

private
def message_field_shape : Syntax := Unhygienic.run `(command| structure Message where api : Nat)

private
def semantic_field_allow_style : Style :=
  { semantic_field_style with linting.fieldAllow := [(3, ["Packet.api"])] }

private
def broad_field_allow_style : Style :=
  { semantic_field_style with linting.fieldAllow := [(3, ["api"])] }

private
def namespace_qualified_field_allow_style : Style :=
  { semantic_field_style with linting.fieldAllow := [(3, ["Example.Protocol.Packet.api"])] }

example : semantic_field_rule_count semantic_field_style packet_field_shape = 1 := by native_decide

/-- An owner-qualified exception admits only that owner's exact field. -/
example : semantic_field_rule_count semantic_field_allow_style packet_field_shape = 0 := by
  native_decide

example : semantic_field_rule_count semantic_field_allow_style message_field_shape = 1 := by
  native_decide

example : semantic_field_rule_count namespace_qualified_field_allow_style packet_field_shape = 0 := by
  native_decide

/-- Bare entries remain explicit broad compatibility exceptions. -/
example : semantic_field_rule_count broad_field_allow_style message_field_shape = 0 := by
  native_decide

private
def semantic_declaration_style : Style :=
  { strict_style with linting.requireSemanticDeclarationNames := true }

private
def semantic_declaration_rule_count (style : Style) (stx : Syntax) : Nat :=
  (lint style stx).foldl
    (fun count diagnostic => if diagnostic.rule == "symbol-declaration" then count + 1 else count)
    0

private
def short_definition_shape : Syntax := Unhygienic.run `(command| def api : Nat := 0)

private
def short_constructor_shape : Syntax :=
  Unhygienic.run `(command| inductive SemanticResultContainer where | api)

private
def other_short_constructor_shape : Syntax :=
  Unhygienic.run `(command| inductive SemanticMessageContainer where | api)

private
def qualified_definition_allow_style : Style :=
  { semantic_declaration_style with linting.declarationAllow := [(3, ["Example.Protocol.api"])] }

private
def qualified_constructor_allow_style : Style :=
  { semantic_declaration_style with
    linting.declarationAllow := [(3, ["SemanticResultContainer.api"])] }

example : semantic_declaration_rule_count semantic_declaration_style short_definition_shape = 1 := by
  native_decide

example : semantic_declaration_rule_count qualified_definition_allow_style short_definition_shape = 0 := by
  native_decide

example : semantic_declaration_rule_count semantic_declaration_style short_constructor_shape = 1 := by
  native_decide

example : semantic_declaration_rule_count qualified_constructor_allow_style short_constructor_shape = 0 := by
  native_decide

/-- A constructor exception is isolated to its syntactic owner. -/
example : semantic_declaration_rule_count qualified_constructor_allow_style other_short_constructor_shape = 1 := by
  native_decide

private
def greek_instance_shape : Syntax := Unhygienic.run `(term| fun [β₂ : Target Ty] => β₂)

/-- The binder is harvested exactly once; its type constructor and argument are references. -/
example : role_count greek_instance_shape "instance-binder" = 1 := by native_decide

example : instance_rule_count greek_instance_shape = 0 := by native_decide

private
def positional_style : Style := { strict_style with linting.requirePositionalLoopNames := true }

private
def positional_rule_count (stx : Syntax) : Nat :=
  (lint positional_style stx).foldl
    (fun count diagnostic => if diagnostic.rule == "symbol-loop-index" then count + 1 else count)
    0

private
def collection_loop_style : Style :=
  { strict_style with linting.requireSemanticCollectionLoopNames := true }

private
def collection_loop_rule_count (stx : Syntax) : Nat :=
  (lint collection_loop_style stx).foldl
    (
      fun count diagnostic =>
        if diagnostic.rule == "symbol-loop-collection" then count + 1 else count
    )
    0

private
def nested_range_shape : Syntax :=
  Unhygienic.run
    `(term| do
      for idx in [ 0 : rows ] do
        for jdx in [ 0 : columns ] do
          pure (idx, jdx))

private
def collection_loop_shape : Syntax :=
  Unhygienic.run
    `(term| do
      for semanticCollectionElement in events do
        pure semanticCollectionElement)

private
def short_collection_loop_shape : Syntax :=
  Unhygienic.run `(term| do for element in events do pure element)

private partial
def rewrite_identifier (source target : String) : Syntax → Syntax
  | .ident info raw value preResolved =>
    if raw.toString == source then
      .ident info target.toRawSubstring (Name.mkSimple target) preResolved
    else
      .ident info raw value preResolved
  | .node info kind children => .node info kind (children.map (rewrite_identifier source target))
  | otherSyntax => otherSyntax

private
def correct_range_shape : Syntax := Unhygienic.run `(term| do for idx in [ 0 : count ] do pure idx)

private
def positional_vocabulary_collection_shape : Syntax :=
  rewrite_identifier "semanticCollectionElement" "idx" collection_loop_shape

private
def wrong_range_shape : Syntax := rewrite_identifier "idx" "event" correct_range_shape

private
def destructured_collection_shape : Syntax :=
  Unhygienic.run `(term| do for (entryKey, entryValue) in entries do pure (entryKey, entryValue))

private
def semantic_destructured_collection_shape : Syntax :=
  Unhygienic.run
    `(term| do
      for (semanticCollectionKey, semanticCollectionValue) in entries do
        pure (semanticCollectionKey, semanticCollectionValue))

private
def parallel_range_shape : Syntax :=
  Unhygienic.run
    `(term| do
      for idx in [ 0 : rows ], jdx in [ 0 : columns ] do
        pure (idx, jdx))

private
def mixed_parallel_shape : Syntax :=
  Unhygienic.run
    `(term| do
      for semanticCollectionElement in events, idx in [ 0 : count ] do
        pure (semanticCollectionElement, idx))

example : positional_loop_name 0 = "idx" := by decide
example : positional_loop_name 1 = "jdx" := by decide
example : positional_loop_name 2 = "kdx" := by decide
example : positional_loop_name 7 = "kdx" := by decide

example : positional_loop_iterable (Unhygienic.run `(term| [ 0 : count ])) = true := by
  native_decide

example : positional_loop_iterable (Unhygienic.run `(term| [ 0 : 2 : count ])) = true := by
  native_decide

example : positional_loop_iterable (Unhygienic.run `(term| [ : count ])) = true := by native_decide

example : positional_loop_iterable (Unhygienic.run `(term| events)) = false := by native_decide

example : positional_loop_iterable (Unhygienic.run `(term| List.range count)) = false := by
  native_decide

example : positional_rule_count nested_range_shape = 0 := by native_decide
example : positional_rule_count collection_loop_shape = 0 := by native_decide
example : collection_loop_rule_count collection_loop_shape = 0 := by native_decide
example : collection_loop_rule_count short_collection_loop_shape = 1 := by native_decide
example : collection_loop_rule_count positional_vocabulary_collection_shape = 1 := by native_decide
example : collection_loop_rule_count correct_range_shape = 0 := by native_decide
example : positional_rule_count correct_range_shape = 0 := by native_decide
example : collection_loop_rule_count wrong_range_shape = 0 := by native_decide
example : positional_rule_count wrong_range_shape = 1 := by native_decide
example : collection_loop_rule_count destructured_collection_shape = 2 := by native_decide
example : collection_loop_rule_count semantic_destructured_collection_shape = 0 := by native_decide
example : role_count short_collection_loop_shape "collection-element" = 1 := by native_decide
example : role_count short_collection_loop_shape "loop-index" = 0 := by native_decide
example : role_count correct_range_shape "collection-element" = 0 := by native_decide
example : role_count correct_range_shape "loop-index" = 1 := by native_decide
example : positional_rule_count parallel_range_shape = 0 := by native_decide
example : collection_loop_rule_count parallel_range_shape = 0 := by native_decide
example : positional_rule_count mixed_parallel_shape = 0 := by native_decide
example : collection_loop_rule_count mixed_parallel_shape = 0 := by native_decide

private
def intro_shape : Syntax := Unhygienic.run `(term| by intro introducedName; exact introducedName)

private
def rename_shape : Syntax := Unhygienic.run `(term| by rename_i renamedName; exact renamedName)

private
def case_shape : Syntax :=
  Unhygienic.run `(term| by case constructorName branchValue => exact branchValue)

private
def next_shape : Syntax :=
  Unhygienic.run `(term| by next firstBranchValue secondBranchValue => exact firstBranchValue)

private
def injection_shape : Syntax := Unhygienic.run `(term| by injection src with lhs _ rhs; exact lhs)

private
def anonymous_injection_shape : Syntax := Unhygienic.run `(term| by injection src)

private
def by_cases_shape : Syntax :=
  Unhygienic.run `(term| by by_cases decisionProof : predicate; exact decisionProof)

private
def anonymous_by_cases_shape : Syntax := Unhygienic.run `(term| by by_cases predicate; assumption)

private
def suffices_shape : Syntax :=
  Unhygienic.run `(term| by suffices goalProof : predicate by exact goalProof)

private
def generalize_shape : Syntax :=
  Unhygienic.run
    `(term| by
      generalize equationProof : predicate = generalizedValue at h
      exact generalizedValue)

private
def cases_alternative_shape : Syntax :=
  Unhygienic.run `(term| by cases predicate with | z branchValue => exact branchValue)

private
def induction_alternative_shape : Syntax :=
  Unhygienic.run
    `(term| by
      induction predicate generalizing h with
      | z => exact h
      | source predecessor hypothesis => exact hypothesis)

private
def rcases_shape : Syntax :=
  Unhygienic.run
    `(term| by rcases predicate with ⟨leftValue, rfl, _, -, rightValue⟩; exact leftValue)

private
def rfl_prefix_shape : Syntax := Unhygienic.run `(term| by rcases predicate with rfl'; exact rfl')

private
def obtain_shape : Syntax :=
  Unhygienic.run `(term| by obtain ⟨firstValue, secondValue⟩ : q := predicate; exact firstValue)

private
def nested_obtain_shape : Syntax :=
  Unhygienic.run `(term| by obtain ⟨fst, ⟨snd, thd⟩⟩ : typ := src; exact fst)

private
def sentinel_obtain_shape : Syntax :=
  Unhygienic.run `(term| by obtain ⟨rfl, _, -⟩ := src; assumption)

private
def rintro_shape : Syntax :=
  Unhygienic.run `(term| by rintro (introducedValue : q); exact introducedValue)

private
def tactic_have_shape : Syntax :=
  Unhygienic.run `(term| by have proofName : q := predicate; exact proofName)

private
def tactic_let_shape : Syntax :=
  Unhygienic.run `(term| by let valueName : q := predicate; exact valueName)

private
def tactic_replace_shape : Syntax :=
  Unhygienic.run `(term| by replace proofName : q := predicate; exact proofName)

private
def tactic_have_instance_shape : Syntax :=
  Unhygienic.run `(term| by haveI instanceValue : q := predicate; exact predicate)

private
def tactic_let_instance_shape : Syntax :=
  Unhygienic.run `(term| by letI instanceValue : q := predicate; exact predicate)

private
def tactic_pattern_shape : Syntax :=
  Unhygienic.run `(term| by have ⟨leftValue, rightValue⟩ := predicate; exact leftValue)

private
def tactic_equation_pattern_shape : Syntax :=
  Unhygienic.run
    `(term| by
      have (eq := equationProof) ⟨leftValue, rightValue⟩ := predicate
      exact leftValue)

private
def tactic_rhs_shape : Syntax :=
  Unhygienic.run
    `(term| by
      have proofName : q := (let rhsValue := predicate; rhsValue)
      exact proofName)

private
def tactic_function_shape : Syntax :=
  Unhygienic.run
    `(term| by
      have proofFunction (inputValue : q) : q := inputValue
      exact proofFunction predicate)

private
def tactic_equations_shape : Syntax :=
  Unhygienic.run
    `(term| by
      have proofFunction : Nat → Nat
        | 0 => 0
        | remainingValue + 1 => proofFunction remainingValue
      exact proofFunction 0)

private
def anonymous_tactic_have_shape : Syntax :=
  Unhygienic.run `(term| by have : q := predicate; exact this)

private
def term_let_shape : Syntax := Unhygienic.run `(term| let localValue := predicate; localValue)

private
def short_term_let_shape : Syntax := Unhygienic.run `(term| let inputValue := predicate; inputValue)

private
def short_do_let_shape : Syntax :=
  Unhygienic.run
    `(term| do
      let inputValue := predicate
      pure inputValue)

private
def short_mutable_let_shape : Syntax :=
  Unhygienic.run
    `(term| do
      let mut inputValue := 0
      inputValue := inputValue + 1
      pure inputValue)

private
def term_have_only_shape : Syntax := Unhygienic.run `(term| have inputValue : Nat := 0; inputValue)

private
def quoted_let_only_shape : Syntax :=
  Unhygienic.run
    `(command| def quotedFixture : Syntax := Unhygienic.run `(term| let inputValue := predicate; inputValue))

private
def tactic_let_only_shape : Syntax :=
  Unhygienic.run `(term| by let inputValue := predicate; exact inputValue)

private
def tactic_letI_only_shape : Syntax :=
  Unhygienic.run `(term| by letI inputValue : Inhabited Nat := inferInstance; exact 0)

private
def pattern_let_only_shape : Syntax :=
  Unhygienic.run `(term| let (inputValue, rightValue) := (predicate, predicate); inputValue)

private
def let_allow_style : Style := { semantic_let_style with linting.letAllow := [(1, ["x"])] }

private
def shared_allow_does_not_reach_let_style : Style :=
  { semantic_let_style with linting.symbolAllow := [(1, ["x"])] }

private
def parameter_binder_shape : Syntax :=
  Unhygienic.run `(term| ∀ (inputValue : Nat), inputValue = inputValue)

private
def lambda_binder_shape : Syntax := Unhygienic.run `(term| fun lambdaFixture => lambdaFixture)

private
def lambda_allow_style : Style :=
  { semantic_lambda_style with linting.lambdaAllow := [(13, ["lambdaFixture"])] }

private
def shared_allow_does_not_reach_lambda_style : Style :=
  { semantic_lambda_style with linting.symbolAllow := [(13, ["lambdaFixture"])] }

private
def primed_have_shape : Syntax :=
  Unhygienic.run `(term| by have' proofName : q := predicate; exact proofName)

private
def primed_let_shape : Syntax :=
  Unhygienic.run `(term| by let' valueName : q := predicate; exact valueName)

private
def tactic_let_rec_shape : Syntax :=
  Unhygienic.run
    `(term| by
      let rec recursiveFunction (inputValue : Nat) : Nat :=
        let rhsValue := inputValue
        rhsValue
      exact recursiveFunction 0)

private
def tactic_mutual_let_rec_shape : Syntax :=
  Unhygienic.run
    `(term| by
      let rec firstFunction (firstInput : Nat) : Nat := secondFunction firstInput,
        secondFunction (secondInput : Nat) : Nat := firstFunction secondInput
      exact firstFunction 0)

private
def tactic_equation_let_rec_shape : Syntax :=
  Unhygienic.run
    `(term| by
      let rec recursiveFunction : Nat → Nat
        | 0 => 0
        | remainingValue + 1 => recursiveFunction remainingValue
      exact recursiveFunction 0)

private
def term_let_rec_shape : Syntax :=
  Unhygienic.run
    `(term| let rec recursiveFunction (inputValue : Nat) : Nat := inputValue; recursiveFunction 0)

private
def short_term_let_rec_shape : Syntax :=
  Unhygienic.run
    `(term| let rec recursiveFixture (inputValue : Nat) : Nat := inputValue; recursiveFixture 0)

private
def short_equation_term_let_rec_shape : Syntax :=
  Unhygienic.run
    `(term| let rec recursiveFixture : Nat → Nat
        | 0 => 0
        | remainingValue + 1 => recursiveFixture remainingValue
      recursiveFixture 0)

private
def recursive_helper_allow_style : Style :=
  { semantic_recursive_helper_style with
    linting.recursiveHelperAllow := [(16, ["recursiveFixture"])] }

private
def short_where_helper_shape : Syntax :=
  Unhygienic.run
    `(command| partial def outerFunction (value : Nat) : Nat :=
        recursiveFixture value
        where
          recursiveFixture (inputValue : Nat) : Nat := inputValue)

private
def cases_equation_shape : Syntax :=
  Unhygienic.run
    `(term| by
      cases equationProof : predicate with
      | z introducedBranchValue => exact introducedBranchValue)

private
def anonymous_cases_target_shape : Syntax :=
  Unhygienic.run
    `(term| by
      cases predicate with
      | z introducedBranchValue => exact introducedBranchValue)

private
def rcases_equation_shape : Syntax :=
  Unhygienic.run
    `(term| by
      rcases equationProof : predicate with ⟨introducedLeftPatternValue, introducedRightPatternValue⟩
      exact introducedLeftPatternValue)

private
def pattern_shape : Syntax :=
  Unhygienic.run `(term| let (leftValue, rightValue) := (1, 2); leftValue + rightValue)

private
def match_shape : Syntax :=
  Unhygienic.run `(term| match (1, 2) with | (firstValue, secondValue) => firstValue + secondValue)

private
def multiple_pattern_shape : Syntax :=
  Unhygienic.run
    `(term| match value with
      | .namespace_ _, .vm branchValue => branchValue
      | .vm _, .namespace_ otherValue => otherValue)

private
def grouped_constructor_shape : Syntax :=
  Unhygienic.run `(term| match value with | .none | .some itemValue => itemValue)

private
def qualified_constructor_shape : Syntax :=
  Unhygienic.run `(term| match value with | Option.some itemValue => itemValue)

private
def dotted_qualified_constructor_shape : Syntax :=
  Unhygienic.run `(term| match value with | .Foo.bar itemValue => itemValue)

private
def nullary_constructor_shape : Syntax := Unhygienic.run `(term| match value with | none => 0)

private
def qualified_nullary_constructor_shape : Syntax :=
  Unhygienic.run `(term| match value with | Option.none => 0)

private
def typed_pattern_shape : Syntax :=
  Unhygienic.run `(term| match value with | (itemValue : Nat) => itemValue)

private
def typed_tuple_pattern_shape : Syntax :=
  Unhygienic.run `(term| match value with | ((itemValue, otherValue) : Nat × Nat) => itemValue)

private
def named_pattern_shape : Syntax :=
  Unhygienic.run `(term| match value with | whole@some itemValue => itemValue)

private
def named_equation_pattern_shape : Syntax :=
  Unhygienic.run `(term| match value with | whole@proof:some itemValue => itemValue)

private
def named_dotted_pattern_shape : Syntax :=
  Unhygienic.run `(term| match value with | whole@(.some itemValue) => itemValue)

private
def inaccessible_pattern_shape : Syntax :=
  Unhygienic.run `(term| match value with | .(knownValue) => 0)

private
def grouped_reference_pattern_shape : Syntax :=
  Unhygienic.run `(term| match value with | some itemValue | none => 0)

/-- Tactic binders are harvested from real parser shapes; references are not. -/
example : symbol_length_count intro_shape = 1 := by native_decide

example : symbol_length_count rename_shape = 1 := by native_decide

/-- A `case` selector is not a binding site; only its introduced binder is. -/
example : symbol_length_count case_shape = 1 := by native_decide

example : role_count next_shape "tactic-binder" = 2 := by native_decide

/-- The injected equalities are binders; the injected source proof is a reference. -/
example : role_count injection_shape "tactic-binder" = 2 := by native_decide

example : role_count anonymous_injection_shape "tactic-binder" = 0 := by native_decide

/-- A named `by_cases` hypothesis is a binder; its proposition is a reference. -/
example : symbol_length_count by_cases_shape = 1 := by native_decide

/-- The anonymous form introduces no source-level name to diagnose. -/
example : symbol_length_count anonymous_by_cases_shape = 0 := by native_decide

/-- A named `suffices` goal is a binder; its type and proof references are not. -/
example : symbol_length_count suffices_shape = 1 := by native_decide

/-- `generalize` introduces its equation and value names, but not its source or location terms. -/
example : symbol_length_count generalize_shape = 2 := by native_decide

/-- Alternative selectors and the `cases` target are references; trailing names are binders. -/
example : symbol_length_count cases_alternative_shape = 1 := by native_decide

/-- `induction` targets, selectors, and `generalizing` names remain references. -/
example : symbol_length_count induction_alternative_shape = 2 := by native_decide

/-- `rcases` pattern names bind; its target and the `rfl`/`_`/`-` sentinels do not. -/
example : symbol_length_count rcases_shape = 2 := by native_decide

/-- Only exact `rfl` is special; an ordinary identifier with that prefix still binds. -/
example : symbol_length_count rfl_prefix_shape = 1 := by native_decide

/-- `obtain` pattern names bind; its type and right-hand side remain references. -/
example : symbol_length_count obtain_shape = 2 := by native_decide

/-- An `obtain` pattern owns its names exactly once under the tactic role. -/
example : role_count obtain_shape "tactic-binder" = 2 := by native_decide

example : role_count obtain_shape "pattern-binder" = 0 := by native_decide

example : role_count obtain_shape "let-binder" = 0 := by native_decide

/-- Nested tuple structure and type/RHS references are not mistaken for binders. -/
example : role_count nested_obtain_shape "tactic-binder" = 3 := by native_decide

/-- `rfl`, wildcard, and clear-pattern sentinels introduce no source-level names. -/
example : role_count sentinel_obtain_shape "tactic-binder" = 0 := by native_decide

/-- Typed `rintro` patterns expose their binder but not their annotation. -/
example : symbol_length_count rintro_shape = 1 := by native_decide

/-- Tactic declaration heads consume the ancestor's role claim exactly once. -/
example : role_count tactic_have_shape "tactic-binder" = 1 := by native_decide

example : role_count tactic_have_shape "let-binder" = 0 := by native_decide

example : role_count tactic_let_shape "tactic-binder" = 1 := by native_decide

example : role_count tactic_replace_shape "tactic-binder" = 1 := by native_decide

example : role_count tactic_have_instance_shape "tactic-binder" = 1 := by native_decide

example : role_count tactic_let_instance_shape "tactic-binder" = 1 := by native_decide

/-- Tactic declaration patterns are claimed as tactic binders, one finding per name. -/
example : role_count tactic_pattern_shape "tactic-binder" = 2 := by native_decide

/-- An equation-style pattern adds its explicit equation binder exactly once. -/
example : role_count tactic_equation_pattern_shape "tactic-binder" = 3 := by native_decide

/-- The claim is consumed at the tactic head; declarations in its RHS remain local. -/
example : role_count tactic_rhs_shape "tactic-binder" = 1 := by native_decide

example : role_count tactic_rhs_shape "let-binder" = 1 := by native_decide

/-- Function parameters nested under a tactic declaration retain their local-binder role. -/
example : role_count tactic_function_shape "tactic-binder" = 1 := by native_decide

example : role_count tactic_function_shape "parameter-binder" = 1 := by native_decide

/-- Equation declarations claim their head while arm patterns retain their match role. -/
example : role_count tactic_equations_shape "tactic-binder" = 1 := by native_decide

example : role_count tactic_equations_shape "match-binder" = 1 := by native_decide

/-- Anonymous tactic declarations introduce no source-level name to diagnose. -/
example : role_count anonymous_tactic_have_shape "tactic-binder" = 0 := by native_decide

/-- Term-mode declarations do not inherit a tactic claim. -/
example : role_count term_let_shape "let-binder" = 1 := by native_decide

example : role_count term_let_shape "tactic-binder" = 0 := by native_decide

/-- Immutable term lets and do-block lets each produce one dedicated finding at
    the declaration, while their resolved uses remain silent. -/
example : let_rule_count semantic_let_style short_term_let_shape = 1 := by native_decide

example : let_rule_count semantic_let_style short_do_let_shape = 1 := by native_decide

/-- A mutable let is harvested once at its origin; assignment targets and RHS
    references do not multiply the finding. -/
example : let_rule_count semantic_let_style short_mutable_let_shape = 1 := by native_decide

example : generic_let_count semantic_let_style short_mutable_let_shape = 0 := by native_decide

/-- Let policy is role-local in both directions. -/
example : let_rule_count let_allow_style short_term_let_shape = 0 := by native_decide

example : let_rule_count shared_allow_does_not_reach_let_style short_term_let_shape = 1 := by
  native_decide

/-- Tactic lets, tactic instances, destructuring patterns, and recursive helper
    heads remain separated from the ordinary let gate. -/
example : let_rule_count semantic_let_style tactic_let_only_shape = 0 := by native_decide

example : let_rule_count semantic_let_style tactic_letI_only_shape = 0 := by native_decide

example : let_rule_count semantic_let_style pattern_let_only_shape = 0 := by native_decide

example : let_rule_count semantic_let_style short_term_let_rec_shape = 0 := by native_decide

example : let_rule_count semantic_let_style term_have_only_shape = 0 := by native_decide

example : let_rule_count semantic_let_style quoted_let_only_shape = 0 := by native_decide

/-- The ordinary binding surface is an exact syntactic partition: parameter,
    lambda, and let sites are each harvested once under only their own role. -/
example : role_count parameter_binder_shape "parameter-binder" = 1 := by native_decide

example : role_count parameter_binder_shape "lambda-binder" = 0 := by native_decide

example : role_count parameter_binder_shape "let-binder" = 0 := by native_decide

example : role_count lambda_binder_shape "parameter-binder" = 0 := by native_decide

example : role_count lambda_binder_shape "lambda-binder" = 1 := by native_decide

example : role_count lambda_binder_shape "let-binder" = 0 := by native_decide

/-- The dedicated lambda gate replaces the generic floor finding and harvests
    one binder exactly once. -/
example : lambda_rule_count semantic_lambda_style lambda_binder_shape = 1 := by native_decide

example : generic_lambda_count semantic_lambda_style lambda_binder_shape = 0 := by native_decide

/-- Lambda allowances are role-local; the shared symbol bucket cannot admit a
    lambda binder with the same spelling. -/
example : lambda_rule_count lambda_allow_style lambda_binder_shape = 0 := by native_decide

example : lambda_rule_count shared_allow_does_not_reach_lambda_style lambda_binder_shape = 1 := by
  native_decide

example : role_count term_let_shape "parameter-binder" = 0 := by native_decide

example : role_count term_let_shape "lambda-binder" = 0 := by native_decide

/-- Primed declaration tactics share the same exact one-shot claim algebra. -/
example : role_count primed_have_shape "tactic-binder" = 1 := by native_decide

example : role_count primed_let_shape "tactic-binder" = 1 := by native_decide

/-- A recursive tactic head is claimed; its parameter and RHS declaration remain local. -/
example : role_count tactic_let_rec_shape "tactic-binder" = 1 := by native_decide

example : role_count tactic_let_rec_shape "parameter-binder" = 1 := by native_decide

example : role_count tactic_let_rec_shape "let-binder" = 1 := by native_decide

/-- Every mutual-recursion member consumes one claim, while parameters remain local. -/
example : role_count tactic_mutual_let_rec_shape "tactic-binder" = 2 := by native_decide

example : role_count tactic_mutual_let_rec_shape "parameter-binder" = 2 := by native_decide

/-- Equation-style recursive heads are tactic binders; arm patterns remain match binders. -/
example : role_count tactic_equation_let_rec_shape "tactic-binder" = 1 := by native_decide

example : role_count tactic_equation_let_rec_shape "match-binder" = 1 := by native_decide

/-- Term-mode recursion cannot inherit a tactic claim. -/
example : role_count term_let_rec_shape "tactic-binder" = 0 := by native_decide

example : role_count term_let_rec_shape "recursive-helper" = 1 := by native_decide

example : role_count term_let_rec_shape "parameter-binder" = 1 := by native_decide

/-- Term recursive heads are harvested once under their dedicated role. -/
example : role_count short_term_let_rec_shape "recursive-helper" = 1 := by native_decide

/-- Enabling the semantic helper gate replaces, rather than duplicates, the
    generic symbol-floor diagnostic. -/
example : recursive_helper_rule_count semantic_recursive_helper_style short_term_let_rec_shape = 1 := by
  native_decide

example :
    generic_recursive_helper_count semantic_recursive_helper_style short_term_let_rec_shape = 0 := by
  native_decide

/-- An exact-length helper allowance admits only the dedicated helper finding. -/
example : recursive_helper_rule_count recursive_helper_allow_style short_term_let_rec_shape = 0 := by
  native_decide

/-- Equation-style term recursion closes the alternate parser-shape coverage
    hole without claiming its arm pattern as another helper. -/
example : role_count short_equation_term_let_rec_shape "recursive-helper" = 1 := by native_decide

example :
    recursive_helper_rule_count semantic_recursive_helper_style short_equation_term_let_rec_shape
        = 1 := by native_decide

example :
    generic_recursive_helper_count semantic_recursive_helper_style short_equation_term_let_rec_shape
        = 0 := by native_decide

/-- Recursive `where` declarations share the helper role and single-report
    contract despite their distinct container syntax. -/
example : role_count short_where_helper_shape "recursive-helper" = 1 := by native_decide

example : recursive_helper_rule_count semantic_recursive_helper_style short_where_helper_shape = 1 := by
  native_decide

example :
    generic_recursive_helper_count semantic_recursive_helper_style short_where_helper_shape = 0 := by
  native_decide

/-- Elimination targets expose only their optional equation binder. -/
example : role_count cases_equation_shape "tactic-binder" = 1 := by native_decide

/-- Anonymous elimination targets introduce no source-level equation name. -/
example : role_count anonymous_cases_target_shape "tactic-binder" = 0 := by native_decide

/-- `rcases` target expressions remain references while the optional equation name binds. -/
example : role_count rcases_equation_shape "tactic-binder" = 1 := by native_decide

/-- Existing pattern and match coverage remains one finding per short binder. -/
example : symbol_length_count pattern_shape = 2 := by native_decide

example : symbol_length_count match_shape = 2 := by native_decide

example : semantic_pattern_rule_count pattern_shape = 2 := by native_decide

example : semantic_pattern_rule_count match_shape = 2 := by native_decide

/-- Each dotted constructor is excluded independently in multi-pattern arms. -/
example : semantic_pattern_rule_count multiple_pattern_shape = 2 := by native_decide

/-- Grouped dotted alternatives exclude every constructor while retaining binders. -/
example : semantic_pattern_rule_count grouped_constructor_shape = 1 := by native_decide

/-- Qualified and multi-segment dotted constructor heads remain references. -/
example : semantic_pattern_rule_count qualified_constructor_shape = 1 := by native_decide

example : semantic_pattern_rule_count dotted_qualified_constructor_shape = 1 := by native_decide

/-- Pre-resolved nullary constructors introduce no source-level binder. -/
example : semantic_pattern_rule_count nullary_constructor_shape = 0 := by native_decide

example : semantic_pattern_rule_count qualified_nullary_constructor_shape = 0 := by native_decide

/-- Type ascriptions contribute their pattern binders, never identifiers from the type. -/
example : semantic_pattern_rule_count typed_pattern_shape = 1 := by native_decide

example : semantic_pattern_rule_count typed_tuple_pattern_shape = 2 := by native_decide

/-- Named patterns bind the outer name and subpattern, plus their optional equation proof. -/
example : semantic_pattern_rule_count named_pattern_shape = 2 := by native_decide

example : semantic_pattern_rule_count named_equation_pattern_shape = 3 := by native_decide

example : semantic_pattern_rule_count named_dotted_pattern_shape = 2 := by native_decide

/-- Inaccessible terms are references and grouped nullary constructors remain references. -/
example : semantic_pattern_rule_count inaccessible_pattern_shape = 0 := by native_decide

example : semantic_pattern_rule_count grouped_reference_pattern_shape = 1 := by native_decide

end Lean4Fmt.Rules.Naming
