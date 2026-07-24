/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // STYLE // CONFIG
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `fmt.lean` — the project configuration DSL (DESIGN_V2 §5). A fmt.lean sits
    next to a lakefile; nested fmt.lean files inherit and override field-wise
    along the directory chain (root → leaf, later wins). The file is VALID LEAN
    (editors highlight it) but is interpreted DECLARATIVELY — parsed, never
    elaborated or executed: safer than a lakefile, zero env cost, and no
    version coupling for target repos.

    Grammar (line-oriented; full-line `--` comments and blanks are skipped):

        def preset := "straylight"
        def layout.lineWidth := 100
        def breaking.binders := "onePerLine"
        def alignment.matchArms := "whenShort"
        def spacing.afterComma := true

    `preset` RESETS the whole style to the named preset — put it first; every
    other key patches one field. Unknown keys and bad values are LOUD errors
    (the file fails to format), never silently ignored.

    Pure (parse + apply). Discovery/IO lives in Driver.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Style.Options
import Lean4Fmt.Style.Preset

namespace Lean4Fmt.Style

/-- One configuration entry: a dotted key and its literal value (as written). -/
structure config_entry where
  key  : String
  val  : String
  line : Nat
  deriving Repr, Inhabited

/-- Parse a literal value token: `"str"` → str, bare token kept as-is
    (numbers, `true`/`false`, bare enum names all arrive as their token). -/
private
def unquote (v : String) : String :=
  let v := v.trimAscii.toString
  if v.length ≥ 2 && v.startsWith "\"" && v.endsWith "\"" then
    ((v.drop 1).dropRight 1).toString
  else
    v

/-- Parse fmt.lean text into entries. Accepted lines: blank, full-line `--`
    comment, or `def <dotted.key> := <literal>`. Anything else is an error —
    the DSL is deliberately small; taste lives in the keys, not the syntax. -/
def parse_config (text : String) : Except String (List config_entry) := do
  let mut out : List config_entry := []
  let mut n := 0
  for line in text.splitOn "\n" do
    n := n + 1
    let t := line.trimAscii.toString
    if t.isEmpty || t.startsWith "--" then continue
    if !t.startsWith "def " then
      throw s!"line {n}: expected `def <key> := <value>` (got: {t})"
    match ((t.drop 4).toString).splitOn ":=" with
    | [k, v] =>
      let key := k.trimAscii.toString
      if key.isEmpty || key.any (fun c => c == ' ') then
        throw s!"line {n}: bad key `{key}`"
      out := out ++ [({ key, val := unquote v, line := n } : config_entry)]
    | _ => throw s!"line {n}: expected `def <key> := <value>` (got: {t})"
  return out

private
def as_nat (e : config_entry) : Except String Nat :=
  match e.val.toNat? with
  | some n => pure n
  | none   => throw s!"line {e.line}: `{e.key}` expects a number (got `{e.val}`)"

private
def as_bool (e : config_entry) : Except String Bool :=
  match e.val with
  | "true"  => pure true
  | "false" => pure false
  | _       => throw s!"line {e.line}: `{e.key}` expects true/false (got `{e.val}`)"

private
def as_align (e : config_entry) : Except String align_mode :=
  match align_mode.of_string? e.val with
  | some m => pure m
  | none   => throw s!"line {e.line}: `{e.key}` expects always/whenShort/never (got `{e.val}`)"

private
def as_case (e : config_entry) : Except String Lean4Fmt.Casing.Case :=
  match Lean4Fmt.Casing.Case.of_string? e.val with
  | some c => pure c
  | none =>
    throw s!"line {e.line}: `{e.key}` expects snake/camel/upperCamel/preserve (got `{e.val}`)"

/-- Apply one entry to a style. The single source of truth for the key space —
    an unknown key is an error here, which is what makes a typo'd axis LOUD. -/
def apply_entry (s : Style) (e : config_entry) : Except String Style := do
  match e.key with
  | "preset" =>
    match by_name? e.val with
    | some p => pure p
    | none => throw s!"line {e.line}: unknown preset `{e.val}`"
  | "layout.lineWidth" => pure { s with layout.lineWidth := ← as_nat e }
  | "layout.indent" => pure { s with layout.indent := ← as_nat e }
  | "layout.continuationIndent" => pure { s with layout.continuationIndent := ← as_nat e }
  | "layout.bodyFitWidth" => pure { s with layout.bodyFitWidth := ← as_nat e }
  | "breaking.colon" =>
    match colon_placement.of_string? e.val with
    | some v => pure { s with breaking.colon := v }
    | none => throw s!"line {e.line}: `{e.key}` expects breakBefore/breakAfter"
  | "breaking.binders" =>
    match binder_layout.of_string? e.val with
    | some v => pure { s with breaking.binders := v }
    | none => throw s!"line {e.line}: `{e.key}` expects oneLine/onePerLine/fill/adaptive"
  | "breaking.attributesOwnLine" => pure { s with breaking.attributesOwnLine := ← as_bool e }
  | "breaking.visibilityOwnLine" => pure { s with breaking.visibilityOwnLine := ← as_bool e }
  | "breaking.bodyOwnLine" => pure { s with breaking.bodyOwnLine := ← as_bool e }
  | "breaking.bodyAlwaysBreak" => pure { s with breaking.bodyAlwaysBreak := ← as_bool e }
  | "breaking.preserveLineBreaks" => pure { s with breaking.preserveLineBreaks := ← as_bool e }
  | "breaking.compactDo" => pure { s with breaking.compactDo := ← as_bool e }
  | "breaking.elseIfChain" => pure { s with breaking.elseIfChain := ← as_bool e }
  | "breaking.inlineBranches" => pure { s with breaking.inlineBranches := ← as_bool e }
  | "breaking.guardIfOwnLine" => pure { s with breaking.guardIfOwnLine := ← as_bool e }
  | "breaking.ctorsOneLine" => pure { s with breaking.ctorsOneLine := ← as_bool e }
  | "breaking.glueFun" => pure { s with breaking.glueFun := ← as_bool e }
  | "breaking.listFill" => pure { s with breaking.listFill := ← as_bool e }
  | "breaking.solveDefs" => pure { s with breaking.solveDefs := ← as_bool e }
  | "breaking.opBreak" =>
    match op_break.of_string? e.val with
    | some v => pure { s with breaking.opBreak := v }
    | none => throw s!"line {e.line}: `{e.key}` expects leading/trailing"
  | "alignment.structFields" => pure { s with alignment.structFields := ← as_align e }
  | "alignment.matchArms" => pure { s with alignment.matchArms := ← as_align e }
  | "alignment.letBlocks" => pure { s with alignment.letBlocks := ← as_align e }
  | "alignment.recordFields" => pure { s with alignment.recordFields := ← as_align e }
  | "alignment.trailingComments" => pure { s with alignment.trailingComments := ← as_align e }
  | "alignment.binderGroups" => pure { s with alignment.binderGroups := ← as_align e }
  | "alignment.maxDelta" => pure { s with alignment.maxDelta := ← as_nat e }
  | "blankLines.policy" =>
    match blank_policy.of_string? e.val with
    | some v => pure { s with blankLines.policy := v }
    | none => throw s!"line {e.line}: `{e.key}` expects preserve/impose/normalize"
  | "blankLines.betweenTopLevelDecls" =>
    pure { s with blankLines.betweenTopLevelDecls := ← as_nat e }
  | "blankLines.betweenImportGroups" => pure { s with blankLines.betweenImportGroups := ← as_nat e }
  | "blankLines.afterNamespaceOpen" => pure { s with blankLines.afterNamespaceOpen := ← as_nat e }
  | "blankLines.beforeNamespaceEnd" => pure { s with blankLines.beforeNamespaceEnd := ← as_nat e }
  | "blankLines.beforeDocComment" => pure { s with blankLines.beforeDocComment := ← as_nat e }
  | "blankLines.beforeSectionBanner" => pure { s with blankLines.beforeSectionBanner := ← as_nat e }
  | "blankLines.afterSectionBanner" => pure { s with blankLines.afterSectionBanner := ← as_nat e }
  | "blankLines.betweenDeclKinds" => pure { s with blankLines.betweenDeclKinds := ← as_bool e }
  | "blankLines.aroundBlockComments" => pure { s with blankLines.aroundBlockComments := ← as_nat e }
  | "blankLines.insideDoPhases" => pure { s with blankLines.insideDoPhases := ← as_bool e }
  | "blankLines.maxConsecutive" => pure { s with blankLines.maxConsecutive := ← as_nat e }
  | "spacing.aroundOperators" => pure { s with spacing.aroundOperators := ← as_bool e }
  | "spacing.insideBrackets" => pure { s with spacing.insideBrackets := ← as_bool e }
  | "spacing.afterComma" => pure { s with spacing.afterComma := ← as_bool e }
  | "spacing.preserveBinders" => pure { s with spacing.preserveBinders := ← as_bool e }
  | "imports.group" => pure { s with imports.group := ← as_bool e }
  | "imports.sort" => pure { s with imports.sort := ← as_bool e }
  | "comments.spaceAfterDashes" => pure { s with comments.spaceAfterDashes := ← as_bool e }
  | "naming.namespaces" => pure { s with naming.namespaces := ← as_case e }
  | "naming.types" => pure { s with naming.types := ← as_case e }
  | "naming.theorems" => pure { s with naming.theorems := ← as_case e }
  | "naming.terms" => pure { s with naming.terms := ← as_case e }
  | k => throw s!"line {e.line}: unknown option `{k}`"

/-- Apply a whole config (one fmt.lean) onto a base style, in entry order. -/
def apply_config (s : Style) (entries : List config_entry) : Except String Style :=
  entries.foldlM apply_entry s

/-- Parse + apply in one step (the per-file unit the resolver folds). -/
def apply_config_text (s : Style) (text : String) : Except String Style := do
  apply_config s (← parse_config text)

end Lean4Fmt.Style
