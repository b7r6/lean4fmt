/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // LEAN4FMT // STYLE // CONFIG LAWS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Executable checks for named policy fragments and exact-length buckets.
    These sit beside the algebraic patch laws: syntax changes must preserve
    both the composition model and the user-facing configuration behavior.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Style.Config
import Lean4Fmt.Style.Laws

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
        && style.linting.requirePositionalLoopNames
            == straylight.linting.requirePositionalLoopNames
        && style.layout.lineWidth == straylight.layout.lineWidth
  | .error _ => false

example : semantic_pattern_binders_is_local = true := by native_decide

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
