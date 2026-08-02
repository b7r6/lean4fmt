/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // LEAN4FMT // STYLE // CONFIG LAWS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Executable checks for named policy fragments and exact-length buckets.
    These sit beside the algebraic patch laws: syntax changes must preserve
    both the composition model and the user-facing configuration behavior.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.style.config
import lean_4_fmt.style.laws

namespace Lean4Fmt.Style

private
def traditional_config_ok : Bool :=
  match apply_config_text straylight "def lint.symbolPolicy := \"traditionalLean\"" with
  | .ok style =>
    style.linting.allowGreekSymbols && !style.linting.allowHebrewSymbols
        && style.linting.symbolMinChars == straylight.linting.symbolMinChars
  | .error _ => false

example : traditional_config_ok = true := by native_decide

private
def systems_config_ok : Bool :=
  match apply_config_text
      { straylight with
        linting.allowGreekSymbols := true
        linting.allowHebrewSymbols := true }
      "def lint.symbolPolicy := \"systems\"" with
  | .ok style => !style.linting.allowGreekSymbols && !style.linting.allowHebrewSymbols
  | .error _ => false

example : systems_config_ok = true := by native_decide

private
def rejects_wrong_bucket : Bool :=
  match apply_config_text straylight "def lint.symbolAllow.2 := \"x\"" with
  | .ok _    => false
  | .error _ => true

example : rejects_wrong_bucket = true := by native_decide

private
def field_bucket_is_local : Bool :=
  match apply_config_text straylight "def lint.fieldAllow.2 := \"st\"" with
  | .ok style =>
    style.linting.fieldAllow == [(2, ["st"])]
        && style.linting.symbolAllow == straylight.linting.symbolAllow
  | .error _ => false

example : field_bucket_is_local = true := by native_decide

private
def qualified_field_bucket_uses_leaf_length : Bool :=
  match apply_config_text straylight "def lint.fieldAllow.2 := \"Packet.id\"" with
  | .ok style => style.linting.fieldAllow == [(2, ["Packet.id"])]
  | .error _  => false

example : qualified_field_bucket_uses_leaf_length = true := by native_decide

private
def lean_valid_field_bucket_alias : Bool :=
  match apply_config_text straylight "def lint.fieldAllow2 := \"Packet.id\"" with
  | .ok style => style.linting.fieldAllow == [(2, ["Packet.id"])]
  | .error _  => false

example : lean_valid_field_bucket_alias = true := by native_decide

private
def formatted_multiline_field_bucket : Bool :=
  match apply_config_text straylight "def lint.fieldAllow2 :=\n  \"Packet.id\"" with
  | .ok style => style.linting.fieldAllow == [(2, ["Packet.id"])]
  | .error _  => false

example : formatted_multiline_field_bucket = true := by native_decide

private
def qualified_field_bucket_rejects_wrong_leaf : Bool :=
  match apply_config_text straylight "def lint.fieldAllow.2 := \"Packet.api\"" with
  | .ok _    => false
  | .error _ => true

example : qualified_field_bucket_rejects_wrong_leaf = true := by native_decide

private
def field_bucket (style : Style) (size : Nat) : List String :=
  (style.linting.fieldAllow.find? (·.1 == size)).map (·.2) |>.getD []

private
def field_bucket_replaces_exact_length : Bool :=
  let base := { straylight with linting.fieldAllow := [(1, ["x"]), (2, ["st"])] }
  match apply_config_text base "def lint.fieldAllow.2 := \"fd\"" with
  | .ok style => field_bucket style 1 == ["x"] && field_bucket style 2 == ["fd"]
  | .error _  => false

example : field_bucket_replaces_exact_length = true := by native_decide

private
def field_bucket_right_absorbs : Bool :=
  match apply_config_text
      straylight
      "def lint.fieldAllow.2 := \"st\"\ndef lint.fieldAllow.2 := \"fd\"" with
  | .ok style => field_bucket style 2 == ["fd"]
  | .error _ => false

example : field_bucket_right_absorbs = true := by native_decide

private
def field_buckets_different_lengths_commute : Bool :=
  match
      apply_config_text straylight "def lint.fieldAllow.1 := \"x\"\ndef lint.fieldAllow.2 := \"st\"",
      apply_config_text straylight "def lint.fieldAllow.2 := \"st\"\ndef lint.fieldAllow.1 := \"x\"" with
  | .ok first, .ok second =>
    field_bucket first 1 == field_bucket second 1
        && field_bucket first 2 == field_bucket second 2
  | _, _ => false

example : field_buckets_different_lengths_commute = true := by native_decide

private
def empty_field_bucket_clears : Bool :=
  match apply_config_text straylight "def lint.fieldAllow.2 := \"\"" with
  | .ok style => (field_bucket style 2).isEmpty
  | .error _  => false

example : empty_field_bucket_clears = true := by native_decide

private
def declaration_bucket (style : Style) (size : Nat) : List String :=
  (style.linting.declarationAllow.find? (·.1 == size)).map (·.2) |>.getD []

private
def declaration_bucket_is_local : Bool :=
  match apply_config_text straylight "def lint.declarationAllow.2 := \"IO\"" with
  | .ok style =>
    declaration_bucket style 2 == ["IO"]
        && style.linting.symbolAllow == straylight.linting.symbolAllow
        && style.linting.fieldAllow == straylight.linting.fieldAllow
  | .error _ => false

example : declaration_bucket_is_local = true := by native_decide

private
def qualified_declaration_bucket_uses_leaf_length : Bool :=
  match apply_config_text straylight "def lint.declarationAllow.2 := \"Protocol.IO\"" with
  | .ok style => declaration_bucket style 2 == ["Protocol.IO"]
  | .error _  => false

example : qualified_declaration_bucket_uses_leaf_length = true := by native_decide

private
def lean_valid_declaration_bucket_alias : Bool :=
  match apply_config_text straylight "def lint.declarationAllow2 := \"Protocol.IO\"" with
  | .ok style => declaration_bucket style 2 == ["Protocol.IO"]
  | .error _  => false

example : lean_valid_declaration_bucket_alias = true := by native_decide

private
def formatted_multiline_declaration_bucket : Bool :=
  match apply_config_text straylight "def lint.declarationAllow2 :=\n  \"Protocol.IO\"" with
  | .ok style => declaration_bucket style 2 == ["Protocol.IO"]
  | .error _  => false

example : formatted_multiline_declaration_bucket = true := by native_decide

private
def qualified_declaration_bucket_rejects_wrong_leaf : Bool :=
  match apply_config_text straylight "def lint.declarationAllow.2 := \"Protocol.API\"" with
  | .ok _    => false
  | .error _ => true

example : qualified_declaration_bucket_rejects_wrong_leaf = true := by native_decide

private
def declaration_bucket_replaces_exact_length : Bool :=
  let base := { straylight with linting.declarationAllow := [(1, ["X"]), (2, ["IO"])] }
  match apply_config_text base "def lint.declarationAllow.2 := \"OS\"" with
  | .ok style => declaration_bucket style 1 == ["X"] && declaration_bucket style 2 == ["OS"]
  | .error _  => false

example : declaration_bucket_replaces_exact_length = true := by native_decide

private
def declaration_bucket_right_absorbs : Bool :=
  match apply_config_text
      straylight
      "def lint.declarationAllow.2 := \"IO\"\ndef lint.declarationAllow.2 := \"OS\"" with
  | .ok style => declaration_bucket style 2 == ["OS"]
  | .error _ => false

example : declaration_bucket_right_absorbs = true := by native_decide

private
def declaration_buckets_different_lengths_commute : Bool :=
  match
      apply_config_text
        straylight
        "def lint.declarationAllow.1 := \"X\"\ndef lint.declarationAllow.2 := \"IO\"",
      apply_config_text
        straylight
        "def lint.declarationAllow.2 := \"IO\"\ndef lint.declarationAllow.1 := \"X\"" with
  | .ok first, .ok second =>
    declaration_bucket first 1 == declaration_bucket second 1
        && declaration_bucket first 2 == declaration_bucket second 2
  | _, _ => false

example : declaration_buckets_different_lengths_commute = true := by native_decide

private
def empty_declaration_bucket_clears : Bool :=
  match apply_config_text straylight "def lint.declarationAllow.2 := \"\"" with
  | .ok style => (declaration_bucket style 2).isEmpty
  | .error _  => false

example : empty_declaration_bucket_clears = true := by native_decide

private
def recursive_helper_bucket (style : Style) (size : Nat) : List String :=
  (style.linting.recursiveHelperAllow.find? (·.1 == size)).map (·.2) |>.getD []

private
def recursive_helper_bucket_is_local : Bool :=
  match apply_config_text straylight "def lint.recursiveHelperAllow.2 := \"go\"" with
  | .ok style =>
    recursive_helper_bucket style 2 == ["go"]
        && style.linting.symbolAllow == straylight.linting.symbolAllow
        && style.linting.declarationAllow == straylight.linting.declarationAllow
  | .error _ => false

example : recursive_helper_bucket_is_local = true := by native_decide

private
def recursive_helper_bucket_rejects_wrong_length : Bool :=
  match apply_config_text straylight "def lint.recursiveHelperAllow.2 := \"walk\"" with
  | .ok _    => false
  | .error _ => true

example : recursive_helper_bucket_rejects_wrong_length = true := by native_decide

private
def lean_valid_recursive_helper_bucket_alias : Bool :=
  match apply_config_text straylight "def lint.recursiveHelperAllow2 := \"go\"" with
  | .ok style => recursive_helper_bucket style 2 == ["go"]
  | .error _  => false

example : lean_valid_recursive_helper_bucket_alias = true := by native_decide

private
def formatted_multiline_recursive_helper_bucket : Bool :=
  match apply_config_text straylight "def lint.recursiveHelperAllow2 :=\n  \"go\"" with
  | .ok style => recursive_helper_bucket style 2 == ["go"]
  | .error _  => false

example : formatted_multiline_recursive_helper_bucket = true := by native_decide

private
def recursive_helper_bucket_replaces_exact_length : Bool :=
  let base := { straylight with linting.recursiveHelperAllow := [(1, ["f"]), (2, ["go"])] }
  match apply_config_text base "def lint.recursiveHelperAllow.2 := \"lp\"" with
  | .ok style =>
    recursive_helper_bucket style 1 == ["f"] && recursive_helper_bucket style 2 == ["lp"]
  | .error _ => false

example : recursive_helper_bucket_replaces_exact_length = true := by native_decide

private
def recursive_helper_bucket_right_absorbs : Bool :=
  match apply_config_text
      straylight
      "def lint.recursiveHelperAllow.2 := \"go\"\ndef lint.recursiveHelperAllow.2 := \"lp\"" with
  | .ok style => recursive_helper_bucket style 2 == ["lp"]
  | .error _ => false

example : recursive_helper_bucket_right_absorbs = true := by native_decide

private
def recursive_helper_buckets_different_lengths_commute : Bool :=
  match
      apply_config_text
        straylight
        "def lint.recursiveHelperAllow.1 := \"f\"\ndef lint.recursiveHelperAllow.2 := \"go\"",
      apply_config_text
        straylight
        "def lint.recursiveHelperAllow.2 := \"go\"\ndef lint.recursiveHelperAllow.1 := \"f\"" with
  | .ok first, .ok second =>
    recursive_helper_bucket first 1 == recursive_helper_bucket second 1
        && recursive_helper_bucket first 2 == recursive_helper_bucket second 2
  | _, _ => false

example : recursive_helper_buckets_different_lengths_commute = true := by native_decide

private
def empty_recursive_helper_bucket_clears : Bool :=
  match apply_config_text straylight "def lint.recursiveHelperAllow.2 := \"\"" with
  | .ok style => (recursive_helper_bucket style 2).isEmpty
  | .error _  => false

example : empty_recursive_helper_bucket_clears = true := by native_decide

private
def lambda_bucket (style : Style) (size : Nat) : List String :=
  (style.linting.lambdaAllow.find? (·.1 == size)).map (·.2) |>.getD []

private
def lambda_bucket_is_local : Bool :=
  match apply_config_text straylight "def lint.lambdaAllow.2 := \"fn\"" with
  | .ok style =>
    lambda_bucket style 2 == ["fn"] && style.linting.symbolAllow == straylight.linting.symbolAllow
        && style.linting.recursiveHelperAllow == straylight.linting.recursiveHelperAllow
  | .error _ => false

example : lambda_bucket_is_local = true := by native_decide

private
def lambda_bucket_rejects_wrong_length : Bool :=
  match apply_config_text straylight "def lint.lambdaAllow.2 := \"value\"" with
  | .ok _    => false
  | .error _ => true

example : lambda_bucket_rejects_wrong_length = true := by native_decide

private
def lean_valid_lambda_bucket_alias : Bool :=
  match apply_config_text straylight "def lint.lambdaAllow2 := \"fn\"" with
  | .ok style => lambda_bucket style 2 == ["fn"]
  | .error _  => false

example : lean_valid_lambda_bucket_alias = true := by native_decide

private
def formatted_multiline_lambda_bucket : Bool :=
  match apply_config_text straylight "def lint.lambdaAllow2 :=\n  \"fn\"" with
  | .ok style => lambda_bucket style 2 == ["fn"]
  | .error _  => false

example : formatted_multiline_lambda_bucket = true := by native_decide

private
def lambda_bucket_replaces_exact_length : Bool :=
  let base := { straylight with linting.lambdaAllow := [(1, ["f"]), (2, ["fn"])] }
  match apply_config_text base "def lint.lambdaAllow.2 := \"op\"" with
  | .ok style => lambda_bucket style 1 == ["f"] && lambda_bucket style 2 == ["op"]
  | .error _  => false

example : lambda_bucket_replaces_exact_length = true := by native_decide

private
def lambda_bucket_right_absorbs : Bool :=
  match apply_config_text
      straylight
      "def lint.lambdaAllow.2 := \"fn\"\ndef lint.lambdaAllow.2 := \"op\"" with
  | .ok style => lambda_bucket style 2 == ["op"]
  | .error _ => false

example : lambda_bucket_right_absorbs = true := by native_decide

private
def lambda_buckets_different_lengths_commute : Bool :=
  match
      apply_config_text straylight "def lint.lambdaAllow.1 := \"f\"\ndef lint.lambdaAllow.2 := \"fn\"",
      apply_config_text straylight "def lint.lambdaAllow.2 := \"fn\"\ndef lint.lambdaAllow.1 := \"f\"" with
  | .ok first, .ok second =>
    lambda_bucket first 1 == lambda_bucket second 1
        && lambda_bucket first 2 == lambda_bucket second 2
  | _, _ => false

example : lambda_buckets_different_lengths_commute = true := by native_decide

private
def empty_lambda_bucket_clears : Bool :=
  match apply_config_text straylight "def lint.lambdaAllow.2 := \"\"" with
  | .ok style => (lambda_bucket style 2).isEmpty
  | .error _  => false

example : empty_lambda_bucket_clears = true := by native_decide

private
def let_bucket (style : Style) (size : Nat) : List String :=
  (style.linting.letAllow.find? (·.1 == size)).map (·.2) |>.getD []

private
def let_bucket_is_local : Bool :=
  match apply_config_text straylight "def lint.letAllow.2 := \"io\"" with
  | .ok style =>
    let_bucket style 2 == ["io"] && style.linting.symbolAllow == straylight.linting.symbolAllow
        && style.linting.lambdaAllow == straylight.linting.lambdaAllow
  | .error _ => false

example : let_bucket_is_local = true := by native_decide

private
def let_bucket_rejects_wrong_length : Bool :=
  match apply_config_text straylight "def lint.letAllow.2 := \"value\"" with
  | .ok _    => false
  | .error _ => true

example : let_bucket_rejects_wrong_length = true := by native_decide

private
def lean_valid_let_bucket_alias : Bool :=
  match apply_config_text straylight "def lint.letAllow2 := \"io\"" with
  | .ok style => let_bucket style 2 == ["io"]
  | .error _  => false

example : lean_valid_let_bucket_alias = true := by native_decide

private
def let_bucket_replaces_exact_length : Bool :=
  let base := { straylight with linting.letAllow := [(1, ["x"]), (2, ["io"])] }
  match apply_config_text base "def lint.letAllow.2 := \"op\"" with
  | .ok style => let_bucket style 1 == ["x"] && let_bucket style 2 == ["op"]
  | .error _  => false

example : let_bucket_replaces_exact_length = true := by native_decide

private
def let_bucket_right_absorbs : Bool :=
  match
      apply_config_text
        straylight
        "def lint.letAllow.2 := \"io\"\ndef lint.letAllow.2 := \"op\"" with
  | .ok style => let_bucket style 2 == ["op"]
  | .error _ => false

example : let_bucket_right_absorbs = true := by native_decide

private
def let_buckets_different_lengths_commute : Bool :=
  match
      apply_config_text straylight "def lint.letAllow.1 := \"x\"\ndef lint.letAllow.2 := \"io\"",
      apply_config_text straylight "def lint.letAllow.2 := \"io\"\ndef lint.letAllow.1 := \"x\"" with
  | .ok first, .ok second =>
    let_bucket first 1 == let_bucket second 1 && let_bucket first 2 == let_bucket second 2
  | _, _ => false

example : let_buckets_different_lengths_commute = true := by native_decide

private
def empty_let_bucket_clears : Bool :=
  match apply_config_text straylight "def lint.letAllow.2 := \"\"" with
  | .ok style => (let_bucket style 2).isEmpty
  | .error _  => false

example : empty_let_bucket_clears = true := by native_decide

private
def denylist_is_local : Bool :=
  match apply_config_text straylight "def lint.symbolDeny := \"acc,tmp\"" with
  | .ok style =>
    style.linting.symbolDeny == ["acc", "tmp"]
        && style.linting.symbolAllow == straylight.linting.symbolAllow
  | .error _ => false

example : denylist_is_local = true := by native_decide

private
def handler_parameter_max_is_local : Bool :=
  match apply_config_text straylight "def lint.handlerParameterMax := 9" with
  | .ok style =>
    style.linting.handlerParameterMax == 9
        && style.linting.symbolMinChars == straylight.linting.symbolMinChars
        && style.layout.lineWidth == straylight.layout.lineWidth
  | .error _ => false

example : handler_parameter_max_is_local = true := by native_decide

private
def stanza_comments_is_local : Bool :=
  match apply_config_text straylight "def lint.requireStanzaComments := false" with
  | .ok style =>
    !style.linting.requireStanzaComments
        && style.linting.handlerParameterMax == straylight.linting.handlerParameterMax
        && style.layout.lineWidth == straylight.layout.lineWidth
  | .error _ => false

example : stanza_comments_is_local = true := by native_decide

private
def traditional_instances_is_local : Bool :=
  match apply_config_text straylight "def lint.requireTraditionalInstances := false" with
  | .ok style =>
    !style.linting.requireTraditionalInstances
        && style.linting.requireStanzaComments == straylight.linting.requireStanzaComments
        && style.layout.lineWidth == straylight.layout.lineWidth
  | .error _ => false

example : traditional_instances_is_local = true := by native_decide

private
def positional_loop_names_is_local : Bool :=
  match apply_config_text straylight "def lint.requirePositionalLoopNames := false" with
  | .ok style =>
    !style.linting.requirePositionalLoopNames
        && style.linting.requireTraditionalInstances
            == straylight.linting.requireTraditionalInstances
        && style.layout.lineWidth == straylight.layout.lineWidth
  | .error _ => false

example : positional_loop_names_is_local = true := by native_decide

private
def semantic_pattern_binders_is_local : Bool :=
  match apply_config_text straylight "def lint.requireSemanticPatternBinders := false" with
  | .ok style =>
    !style.linting.requireSemanticPatternBinders
        && style.linting.requirePositionalLoopNames == straylight.linting.requirePositionalLoopNames
        && style.layout.lineWidth == straylight.layout.lineWidth
  | .error _ => false

example : semantic_pattern_binders_is_local = true := by native_decide

private
def semantic_collection_loop_names_is_local : Bool :=
  match apply_config_text straylight "def lint.requireSemanticCollectionLoopNames := false" with
  | .ok style =>
    !style.linting.requireSemanticCollectionLoopNames
        && style.linting.requireSemanticPatternBinders
            == straylight.linting.requireSemanticPatternBinders
        && style.linting.requirePositionalLoopNames == straylight.linting.requirePositionalLoopNames
        && style.layout.lineWidth == straylight.layout.lineWidth
  | .error _ => false

example : semantic_collection_loop_names_is_local = true := by native_decide

private
def semantic_field_names_is_local : Bool :=
  match apply_config_text straylight "def lint.requireSemanticFieldNames := false" with
  | .ok style =>
    !style.linting.requireSemanticFieldNames
        && style.linting.requireSemanticCollectionLoopNames
            == straylight.linting.requireSemanticCollectionLoopNames
        && style.linting.fieldAllow == straylight.linting.fieldAllow
        && style.layout.lineWidth == straylight.layout.lineWidth
  | .error _ => false

example : semantic_field_names_is_local = true := by native_decide

private
def semantic_declaration_names_is_local : Bool :=
  match apply_config_text straylight "def lint.requireSemanticDeclarationNames := false" with
  | .ok style =>
    !style.linting.requireSemanticDeclarationNames
        && style.linting.requireSemanticFieldNames == straylight.linting.requireSemanticFieldNames
        && style.linting.declarationAllow == straylight.linting.declarationAllow
        && style.layout.lineWidth == straylight.layout.lineWidth
  | .error _ => false

example : semantic_declaration_names_is_local = true := by native_decide

private
def semantic_recursive_helper_names_is_local : Bool :=
  match apply_config_text straylight "def lint.requireSemanticRecursiveHelperNames := false" with
  | .ok style =>
    !style.linting.requireSemanticRecursiveHelperNames
        && style.linting.requireSemanticDeclarationNames
            == straylight.linting.requireSemanticDeclarationNames
        && style.linting.recursiveHelperAllow == straylight.linting.recursiveHelperAllow
        && style.layout.lineWidth == straylight.layout.lineWidth
  | .error _ => false

example : semantic_recursive_helper_names_is_local = true := by native_decide

private
def semantic_lambda_names_is_local : Bool :=
  match apply_config_text straylight "def lint.requireSemanticLambdaNames := false" with
  | .ok style =>
    !style.linting.requireSemanticLambdaNames
        && style.linting.requireSemanticRecursiveHelperNames
            == straylight.linting.requireSemanticRecursiveHelperNames
        && style.linting.lambdaAllow == straylight.linting.lambdaAllow
        && style.layout.lineWidth == straylight.layout.lineWidth
  | .error _ => false

example : semantic_lambda_names_is_local = true := by native_decide

private
def semantic_let_names_is_local : Bool :=
  match apply_config_text straylight "def lint.requireSemanticLetNames := false" with
  | .ok style =>
    !style.linting.requireSemanticLetNames
        && style.linting.requireSemanticLambdaNames == straylight.linting.requireSemanticLambdaNames
        && style.linting.letAllow == straylight.linting.letAllow
        && style.layout.lineWidth == straylight.layout.lineWidth
  | .error _ => false

example : semantic_let_names_is_local = true := by native_decide

example : ({} : Linting).requireSemanticLetNames = false := rfl

example : straylight.linting.requireSemanticLetNames = true := rfl

private
def branch_density_max_is_local : Bool :=
  match apply_config_text straylight "def lint.branchDensityMax := 17" with
  | .ok style =>
    style.linting.branchDensityMax == 17
        && style.linting.handlerParameterMax == straylight.linting.handlerParameterMax
        && style.layout.lineWidth == straylight.layout.lineWidth
  | .error _ => false

example : branch_density_max_is_local = true := by native_decide

private
def systems_linting : Linting := { straylight.linting with
  allowGreekSymbols := false
  allowHebrewSymbols := false
}

private
def traditional_linting : Linting := { straylight.linting with
  allowGreekSymbols := true
  allowHebrewSymbols := false
}

/-- Recommended policy families are values in one override program; consumers
    may choose different roots without adding a new resolver mechanism. -/
private
def representative_policy_tree : override_tree :=
  [
    { root := [], patch := { linting := some systems_linting } },
    { root := ["vendor", "lean"], patch := { linting := some traditional_linting } }
  ]

example :
    (representative_policy_tree.resolve straylight ["src", "systems"]).linting.allowGreekSymbols
        = false :=
  rfl

example :
    (representative_policy_tree.resolve straylight ["vendor", "lean", "Mathlib"]).linting.allowGreekSymbols
        = true :=
  rfl

end Lean4Fmt.Style
