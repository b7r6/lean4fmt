/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // LEAN4FMT // STYLE // LAWS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Algebraic laws for tree-local style patches. Policy is a process input:
    changing a patch yields a new deterministic fixed point. These laws keep
    inheritance unsurprising as the policy vocabulary grows.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.style.patch

namespace Lean4Fmt.Style

private
theorem option_apply
        {valueType : Type}
        (base : valueType)
        (first second : Option valueType)
        : second.getD (first.getD base) = (second <|> first).getD base := by
  cases first <;> cases second <;> rfl

private
theorem option_overlay_assoc
        {valueType : Type}
        (first second third : Option valueType)
        : ((third <|> second) <|> first) = (third <|> (second <|> first)) := by
  cases first <;> cases second <;> cases third <;> rfl

/-- The empty tree-local override changes nothing. -/
theorem apply_empty (style : Style) : style.apply {} = style := by
  cases style
  rfl

/-- Resolving two directory patches is equivalent to their right-biased merge. -/
theorem apply_append
        (style : Style)
        (first second : style_patch)
        : (style.apply first).apply second = style.apply (style_patch.append first second) := by
  cases style
  cases first
  cases second
  simp only [Style.apply, style_patch.append, option_apply]

/-- Patch composition is associative, so directory-chain grouping is irrelevant. -/
theorem patch_append_assoc
        (first second third : style_patch)
        : style_patch.append (style_patch.append first second) third
            = style_patch.append first (style_patch.append second third) := by
  cases first
  cases second
  cases third
  simp only [style_patch.append, option_overlay_assoc]

/-- An empty override tree resolves to its input style. -/
theorem resolve_empty
        (style : Style)
        (path : List String)
        : override_tree.resolve style path [] = style :=
  rfl

/-- Resolving an overlay is sequential resolution. This is the central
    root-to-leaf composition law used by directory-tree discovery. -/
theorem resolve_overlay
        (style : Style)
        (path : List String)
        (earlier later : override_tree)
        : override_tree.resolve style path (override_tree.overlay earlier later)
            = override_tree.resolve (override_tree.resolve style path earlier) path later := by
  induction earlier generalizing style with
  | nil => rfl
  | cons override rest induction =>
    simp only [override_tree.overlay, List.cons_append, override_tree.resolve]
    exact induction _

/-- Tree overlay has a left identity. -/
theorem overlay_empty_left (tree : override_tree) : override_tree.overlay [] tree = tree := rfl

/-- Tree overlay has a right identity. -/
theorem overlay_empty_right (tree : override_tree) : override_tree.overlay tree [] = tree := by
  exact List.append_nil tree

/-- Tree overlay is associative; discovery may group directory chains freely. -/
theorem overlay_assoc
        (first second third : override_tree)
        : override_tree.overlay (override_tree.overlay first second) third
            = override_tree.overlay first (override_tree.overlay second third) := by
  exact List.append_assoc first second third

/-- For two matching entries, the later patch wins exactly as sequential
    `Style.apply` says; there is no map-order or filesystem-order ambiguity. -/
theorem resolve_matching_pair
        (style : Style)
        (path : List String)
        (first second : tree_override)
        (firstMatches : first.matches path = true)
        (secondMatches : second.matches path = true)
        : override_tree.resolve style path [first, second]
            = (style.apply first.patch).apply second.patch := by
  simp only [override_tree.resolve, firstMatches, secondMatches, ↓reduceIte]

/-- The same deterministic-precedence fact stated through patch composition. -/
theorem resolve_matching_pair_append
        (style : Style)
        (path : List String)
        (first second : tree_override)
        (firstMatches : first.matches path = true)
        (secondMatches : second.matches path = true)
        : override_tree.resolve style path [first, second]
            = style.apply (style_patch.append first.patch second.patch) := by
  rw [resolve_matching_pair style path first second firstMatches secondMatches]
  exact apply_append style first.patch second.patch

/-- Resolving a tree of monotone patches preserves tightening. Adding a new
    policy axis therefore reduces to proving its local patch is monotone. -/
theorem resolve_preserves_tightening
        (tightens : Tightening)
        (tree : override_tree)
        (path : List String)
        (preserves : tree.preserves_tightening tightens)
        {lowerStyle upperStyle : Style}
        (tightened : tightens lowerStyle upperStyle)
        : tightens (tree.resolve lowerStyle path) (tree.resolve upperStyle path) := by
  induction tree generalizing lowerStyle upperStyle with
  | nil => exact tightened
  | cons override rest induction =>
    simp only [override_tree.resolve]
    by_cases applies : override.matches path = true
    · simp only [applies]
      apply induction
      · intro candidate member
        exact preserves candidate (List.mem_cons_of_mem override member)
      · exact preserves override (List.mem_cons_self) lowerStyle upperStyle tightened
    · simp only [applies]
      apply induction
      · intro candidate member
        exact preserves candidate (List.mem_cons_of_mem override member)
      · exact tightened

/-- Raising the minimum symbol length is the canonical tightening order for the
    short-symbol floor. -/
def symbol_floor_tightens : Tightening := fun lowerStyle upperStyle =>
  lowerStyle.linting.symbolMinChars ≤ upperStyle.linting.symbolMinChars

/-- Group-level patches preserve the symbol-floor order: either both floors are
    left alone or both are replaced by the same linting group. -/
theorem patch_preserves_symbol_floor
        (patch : style_patch)
        : patch.preserves_tightening symbol_floor_tightens := by
  intro lowerStyle upperStyle tightened
  cases patch with
  | mk layout breaking alignment blankLines spacing imports comments naming linting =>
    cases linting with
    | none => exact tightened
    | some value => exact Nat.le_refl _

/-- Any path/tree override program is monotone for symbol-floor tightening. -/
theorem resolve_preserves_symbol_floor
        (tree : override_tree)
        (path : List String)
        {lowerStyle upperStyle : Style}
        (tightened : symbol_floor_tightens lowerStyle upperStyle)
        : symbol_floor_tightens (tree.resolve lowerStyle path) (tree.resolve upperStyle path) := by
  apply resolve_preserves_tightening symbol_floor_tightens tree path
  · intro override _
    exact patch_preserves_symbol_floor override.patch
  · exact tightened

/-- Enabling semantic collection-loop names tightens the policy; disabling the
    rule is the least element of this Boolean axis. -/
def semantic_collection_loops_tighten : Tightening := fun lowerStyle upperStyle =>
  lowerStyle.linting.requireSemanticCollectionLoopNames = true
      → upperStyle.linting.requireSemanticCollectionLoopNames = true

/-- Group-level patches preserve collection-loop tightening: the linting group
    is either untouched on both sides or replaced by the same value. -/
theorem patch_preserves_semantic_collection_loops
        (patch : style_patch)
        : patch.preserves_tightening semantic_collection_loops_tighten := by
  intro lowerStyle upperStyle tightened
  cases patch with
  | mk layout breaking alignment blankLines spacing imports comments naming linting =>
    cases linting with
    | none => exact tightened
    | some value =>
      intro enabled
      exact enabled

/-- Root-to-leaf policy resolution preserves collection-loop tightening. -/
theorem resolve_preserves_semantic_collection_loops
        (tree : override_tree)
        (path : List String)
        {lowerStyle upperStyle : Style}
        (tightened : semantic_collection_loops_tighten lowerStyle upperStyle)
        : semantic_collection_loops_tighten
          (tree.resolve lowerStyle path)
          (tree.resolve upperStyle path) := by
  apply resolve_preserves_tightening semantic_collection_loops_tighten tree path
  · intro override _
    exact patch_preserves_semantic_collection_loops override.patch
  · exact tightened

/-- Enabling semantic field names tightens the policy; disabling the rule is
    the least element of this Boolean axis. -/
def semantic_field_names_tighten : Tightening := fun lowerStyle upperStyle =>
  lowerStyle.linting.requireSemanticFieldNames = true
      → upperStyle.linting.requireSemanticFieldNames = true

/-- Group-level patches preserve semantic-field tightening by leaving both
    policies alone or replacing both linting groups with the same value. -/
theorem patch_preserves_semantic_field_names
        (patch : style_patch)
        : patch.preserves_tightening semantic_field_names_tighten := by
  intro lowerStyle upperStyle tightened
  cases patch with
  | mk layout breaking alignment blankLines spacing imports comments naming linting =>
    cases linting with
    | none => exact tightened
    | some value =>
      intro enabled
      exact enabled

/-- Root-to-leaf policy resolution preserves semantic-field tightening. -/
theorem resolve_preserves_semantic_field_names
        (tree : override_tree)
        (path : List String)
        {lowerStyle upperStyle : Style}
        (tightened : semantic_field_names_tighten lowerStyle upperStyle)
        : semantic_field_names_tighten (tree.resolve lowerStyle path) (tree.resolve upperStyle path) := by
  apply resolve_preserves_tightening semantic_field_names_tighten tree path
  · intro override _
    exact patch_preserves_semantic_field_names override.patch
  · exact tightened

/-- Enabling semantic declaration names tightens the policy; disabling the rule
    is the least element of this Boolean axis. -/
def semantic_declaration_names_tighten : Tightening := fun lowerStyle upperStyle =>
  lowerStyle.linting.requireSemanticDeclarationNames = true
      → upperStyle.linting.requireSemanticDeclarationNames = true

/-- Group-level patches preserve semantic-declaration tightening by leaving
    both policies alone or replacing both linting groups with the same value. -/
theorem patch_preserves_semantic_declaration_names
        (patch : style_patch)
        : patch.preserves_tightening semantic_declaration_names_tighten := by
  intro lowerStyle upperStyle tightened
  cases patch with
  | mk layout breaking alignment blankLines spacing imports comments naming linting =>
    cases linting with
    | none => exact tightened
    | some value =>
      intro enabled
      exact enabled

/-- Root-to-leaf policy resolution preserves semantic-declaration tightening. -/
theorem resolve_preserves_semantic_declaration_names
        (tree : override_tree)
        (path : List String)
        {lowerStyle upperStyle : Style}
        (tightened : semantic_declaration_names_tighten lowerStyle upperStyle)
        : semantic_declaration_names_tighten
          (tree.resolve lowerStyle path)
          (tree.resolve upperStyle path) := by
  apply resolve_preserves_tightening semantic_declaration_names_tighten tree path
  · intro override _
    exact patch_preserves_semantic_declaration_names override.patch
  · exact tightened

/-- The empty patch is an identity for the recursive-helper policy projection. -/
theorem recursive_helper_policy_apply_identity
        (style : Style)
        : (style.apply {}).linting.requireSemanticRecursiveHelperNames
            = style.linting.requireSemanticRecursiveHelperNames := by rw [apply_empty]

/-- Patch grouping cannot change the recursive-helper policy projection. -/
theorem recursive_helper_policy_patch_assoc
        (first second third : style_patch)
        : (style_patch.append (style_patch.append first second) third).linting
            = (style_patch.append first (style_patch.append second third)).linting := by
  rw [patch_append_assoc]

/-- Enabling semantic recursive-helper names tightens the policy; disabling the
    rule is the least element of this Boolean axis. -/
def semantic_recursive_helper_names_tighten : Tightening := fun lowerStyle upperStyle =>
  lowerStyle.linting.requireSemanticRecursiveHelperNames = true
      → upperStyle.linting.requireSemanticRecursiveHelperNames = true

/-- Group-level patches preserve recursive-helper tightening by leaving both
    policies alone or replacing both linting groups with the same value. -/
theorem patch_preserves_semantic_recursive_helper_names
        (patch : style_patch)
        : patch.preserves_tightening semantic_recursive_helper_names_tighten := by
  intro lowerStyle upperStyle tightened
  cases patch with
  | mk layout breaking alignment blankLines spacing imports comments naming linting =>
    cases linting with
    | none => exact tightened
    | some value =>
      intro enabled
      exact enabled

/-- Root-to-leaf policy resolution preserves recursive-helper tightening. -/
theorem resolve_preserves_semantic_recursive_helper_names
        (tree : override_tree)
        (path : List String)
        {lowerStyle upperStyle : Style}
        (tightened : semantic_recursive_helper_names_tighten lowerStyle upperStyle)
        : semantic_recursive_helper_names_tighten
          (tree.resolve lowerStyle path)
          (tree.resolve upperStyle path) := by
  apply resolve_preserves_tightening semantic_recursive_helper_names_tighten tree path
  · intro override _
    exact patch_preserves_semantic_recursive_helper_names override.patch
  · exact tightened

/-- The empty patch is an identity for the semantic-lambda policy projection. -/
theorem lambda_policy_apply_identity
        (style : Style)
        : (style.apply {}).linting.requireSemanticLambdaNames
            = style.linting.requireSemanticLambdaNames := by rw [apply_empty]

/-- Patch grouping cannot change the semantic-lambda policy projection. -/
theorem lambda_policy_patch_assoc
        (first second third : style_patch)
        : (style_patch.append (style_patch.append first second) third).linting
            = (style_patch.append first (style_patch.append second third)).linting := by
  rw [patch_append_assoc]

/-- Enabling semantic lambda names tightens the policy; disabling the rule is
    the least element of this Boolean axis. -/
def semantic_lambda_names_tighten : Tightening := fun lowerStyle upperStyle =>
  lowerStyle.linting.requireSemanticLambdaNames = true
      → upperStyle.linting.requireSemanticLambdaNames = true

/-- Group-level patches preserve lambda-name tightening by leaving both
    policies alone or replacing both linting groups with the same value. -/
theorem patch_preserves_semantic_lambda_names
        (patch : style_patch)
        : patch.preserves_tightening semantic_lambda_names_tighten := by
  intro lowerStyle upperStyle tightened
  cases patch with
  | mk layout breaking alignment blankLines spacing imports comments naming linting =>
    cases linting with
    | none => exact tightened
    | some value =>
      intro enabled
      exact enabled

/-- Root-to-leaf policy resolution preserves semantic-lambda tightening. -/
theorem resolve_preserves_semantic_lambda_names
        (tree : override_tree)
        (path : List String)
        {lowerStyle upperStyle : Style}
        (tightened : semantic_lambda_names_tighten lowerStyle upperStyle)
        : semantic_lambda_names_tighten
          (tree.resolve lowerStyle path)
          (tree.resolve upperStyle path) := by
  apply resolve_preserves_tightening semantic_lambda_names_tighten tree path
  · intro override _
    exact patch_preserves_semantic_lambda_names override.patch
  · exact tightened

/-- The empty patch is an identity for the semantic-let policy projection. -/
theorem let_policy_apply_identity
        (style : Style)
        : (style.apply {}).linting.requireSemanticLetNames = style.linting.requireSemanticLetNames := by
  rw [apply_empty]

/-- Patch grouping cannot change the semantic-let policy projection. -/
theorem let_policy_patch_assoc
        (first second third : style_patch)
        : (style_patch.append (style_patch.append first second) third).linting
            = (style_patch.append first (style_patch.append second third)).linting := by
  rw [patch_append_assoc]

/-- Enabling semantic let names tightens the policy; disabling the rule is the
    least element of this Boolean axis. -/
def semantic_let_names_tighten : Tightening := fun lowerStyle upperStyle =>
  lowerStyle.linting.requireSemanticLetNames = true
      → upperStyle.linting.requireSemanticLetNames = true

/-- Group-level patches preserve let-name tightening by leaving both policies
    alone or replacing both linting groups with the same value. -/
theorem patch_preserves_semantic_let_names
        (patch : style_patch)
        : patch.preserves_tightening semantic_let_names_tighten := by
  intro lowerStyle upperStyle tightened
  cases patch with
  | mk layout breaking alignment blankLines spacing imports comments naming linting =>
    cases linting with
    | none => exact tightened
    | some value =>
      intro enabled
      exact enabled

/-- Root-to-leaf policy resolution preserves semantic-let tightening. -/
theorem resolve_preserves_semantic_let_names
        (tree : override_tree)
        (path : List String)
        {lowerStyle upperStyle : Style}
        (tightened : semantic_let_names_tighten lowerStyle upperStyle)
        : semantic_let_names_tighten (tree.resolve lowerStyle path) (tree.resolve upperStyle path) := by
  apply resolve_preserves_tightening semantic_let_names_tighten tree path
  · intro override _
    exact patch_preserves_semantic_let_names override.patch
  · exact tightened

end Lean4Fmt.Style
