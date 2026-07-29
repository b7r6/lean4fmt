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
  let value := v.trimAscii.toString
  if value.length ≥ 2 && value.startsWith "\"" && value.endsWith "\"" then
    ((value.drop 1).dropRight 1).toString
  else
    value

private
def config_entry_of_parts (rawKey value : String) (line : Nat) : Except String config_entry := do
  let key := rawKey.trimAscii.toString
  if key.isEmpty || key.any (fun character => character == ' ') then
    throw s!"line {line}: bad key `{key}`"
  pure { key, val := unquote value, line }

private
def parse_config_entry (text : String) (line : Nat) : Except String config_entry :=
  match ((text.drop 4).toString).splitOn ":=" with
  | [rawKey, value] => config_entry_of_parts rawKey value line
  | _               => throw s!"line {line}: expected `def <key> := <value>` (got: {text})"

/-- State threaded through the line-oriented configuration parser. -/
private
structure config_parse_state where
  entries : List config_entry := []
  line    : Nat := 0
  pending : Option (String × Nat) := none

private
def consume_pending_config_line
    (state : config_parse_state)
    (text header : String)
    (headerLine : Nat)
    : Except String config_parse_state := do
  if text.startsWith "def " then
    throw s!"line {headerLine}: expected a literal after `:=`"
  let entry ← parse_config_entry s!"{header} {text}" headerLine
  return { state with entries := state.entries ++ [entry], pending := none }

private
def consume_fresh_config_line
    (state : config_parse_state)
    (text : String)
    : Except String config_parse_state := do
  if !text.startsWith "def " then
    throw s!"line {state.line}: expected `def <key> := <value>` (got: {text})"
  if text.endsWith ":=" then
    return { state with pending := some (text, state.line) }
  let entry ← parse_config_entry text state.line
  return { state with entries := state.entries ++ [entry] }

private
def consume_config_line
    (state : config_parse_state)
    (line : String)
    : Except String config_parse_state := do
  let state := { state with line := state.line + 1 }
  let text := line.trimAscii.toString
  if text.isEmpty || text.startsWith "--" then
    return state
  match state.pending with
  | some (header, headerLine) => consume_pending_config_line state text header headerLine
  | none => consume_fresh_config_line state text

/-- Parse fmt.lean text into entries. Accepted forms are a one-line definition
    or the formatter's canonical two-line form with the literal on the next
    nonblank line. Anything else is an error — the DSL is deliberately small;
    taste lives in the keys, not the syntax. -/
def parse_config (text : String) : Except String (List config_entry) := do
  let mut state : config_parse_state := {}
  for line in text.splitOn "\n" do
    state ← consume_config_line state line
  match state.pending with
  | some (_, headerLine) => throw s!"line {headerLine}: expected a literal after `:=`"
  | none => return state.entries

private
def as_nat (e : config_entry) : Except String Nat :=
  match e.val.toNat? with
  | some count => pure count
  | none       => throw s!"line {e.line}: `{e.key}` expects a number (got `{e.val}`)"

private
def as_bool (e : config_entry) : Except String Bool :=
  match e.val with
  | "true"  => pure true
  | "false" => pure false
  | _       => throw s!"line {e.line}: `{e.key}` expects true/false (got `{e.val}`)"

private
def as_align (e : config_entry) : Except String align_mode :=
  match align_mode.of_string? e.val with
  | some candidate => pure candidate
  | none => throw s!"line {e.line}: `{e.key}` expects always/whenShort/never (got `{e.val}`)"

private
def as_case (e : config_entry) : Except String Lean4Fmt.Casing.Case :=
  match Lean4Fmt.Casing.Case.of_string? e.val with
  | some headChar => pure headChar
  | none =>
    throw s!"line {e.line}: `{e.key}` expects snake/camel/upperCamel/preserve (got `{e.val}`)"

private
def symbol_allow (s : Style) (e : config_entry) (size : Nat) : Except String Style := do
  let names :=
    if e.val.trimAscii.isEmpty then [] else (e.val.splitOn ",").map (·.trimAscii.toString)
  for name in names do
    if name.isEmpty || name.length != size then
      throw s!"line {e.line}: `{e.key}` entries must have exactly {size} characters (got `{name}`)"
  let allow := (s.linting.symbolAllow.filter (·.1 != size)) ++ [(size, names)]
  pure { s with linting.symbolAllow := allow }

private
def field_allow (s : Style) (e : config_entry) (size : Nat) : Except String Style := do
  let names :=
    if e.val.trimAscii.isEmpty then [] else (e.val.splitOn ",").map (·.trimAscii.toString)
  for name in names do
    let segments := name.splitOn "."
    let leaf := segments.getLast!
    if name.isEmpty || segments.any (·.isEmpty) || leaf.length != size then
      throw
        s!"line {e.line}: `{e.key}` entries must have a leaf with exactly {size} characters (got `{name}`)"
  let allow := (s.linting.fieldAllow.filter (·.1 != size)) ++ [(size, names)]
  pure { s with linting.fieldAllow := allow }

private
def declaration_allow (s : Style) (e : config_entry) (size : Nat) : Except String Style := do
  let names :=
    if e.val.trimAscii.isEmpty then [] else (e.val.splitOn ",").map (·.trimAscii.toString)
  for name in names do
    let segments := name.splitOn "."
    let leaf := segments.getLast!
    if name.isEmpty || segments.any (·.isEmpty) || leaf.length != size then
      throw
        s!"line {e.line}: `{e.key}` entries must have a leaf with exactly {size} characters (got `{name}`)"
  let allow := (s.linting.declarationAllow.filter (·.1 != size)) ++ [(size, names)]
  pure { s with linting.declarationAllow := allow }

private
def recursive_helper_allow (s : Style) (e : config_entry) (size : Nat) : Except String Style := do
  let names :=
    if e.val.trimAscii.isEmpty then [] else (e.val.splitOn ",").map (·.trimAscii.toString)
  for name in names do
    if name.isEmpty || name.length != size then
      throw s!"line {e.line}: `{e.key}` entries must have exactly {size} characters (got `{name}`)"
  let allow := (s.linting.recursiveHelperAllow.filter (·.1 != size)) ++ [(size, names)]
  pure { s with linting.recursiveHelperAllow := allow }

private
def lambda_allow (s : Style) (e : config_entry) (size : Nat) : Except String Style := do
  let names :=
    if e.val.trimAscii.isEmpty then [] else (e.val.splitOn ",").map (·.trimAscii.toString)
  for name in names do
    if name.isEmpty || name.length != size then
      throw s!"line {e.line}: `{e.key}` entries must have exactly {size} characters (got `{name}`)"
  let allow := (s.linting.lambdaAllow.filter (·.1 != size)) ++ [(size, names)]
  pure { s with linting.lambdaAllow := allow }

private
def let_allow (s : Style) (e : config_entry) (size : Nat) : Except String Style := do
  let names :=
    if e.val.trimAscii.isEmpty then [] else (e.val.splitOn ",").map (·.trimAscii.toString)
  for name in names do
    if name.isEmpty || name.length != size then
      throw s!"line {e.line}: `{e.key}` entries must have exactly {size} characters (got `{name}`)"
  let allow := (s.linting.letAllow.filter (·.1 != size)) ++ [(size, names)]
  pure { s with linting.letAllow := allow }

private
def apply_bucket_alias?
    (style : Style)
    (entry : config_entry)
    (key aliasPrefix : String)
    (applyBucket : Style → config_entry → Nat → Except String Style)
    : Option (Except String Style) :=
  if key.startsWith aliasPrefix then
    some do
      let some size := (key.drop aliasPrefix.length).toString.toNat?
          | throw s!"line {entry.line}: `{key}` expects a numeric exact-length suffix"
      applyBucket style entry size
  else
    none

private
def apply_dotted_bucket_entry?
    (style : Style)
    (entry : config_entry)
    (key : String)
    : Option (Except String Style) :=
  apply_bucket_alias? style entry key "lint.symbolAllow." symbol_allow
      <|> apply_bucket_alias? style entry key "lint.fieldAllow." field_allow
      <|> apply_bucket_alias? style entry key "lint.declarationAllow." declaration_allow
      <|> apply_bucket_alias? style entry key "lint.recursiveHelperAllow." recursive_helper_allow
      <|> apply_bucket_alias? style entry key "lint.lambdaAllow." lambda_allow
      <|> apply_bucket_alias? style entry key "lint.letAllow." let_allow

private
def apply_lean_bucket_entry?
    (style : Style)
    (entry : config_entry)
    (key : String)
    : Option (Except String Style) :=
  apply_bucket_alias? style entry key "lint.symbolAllow" symbol_allow
      <|> apply_bucket_alias? style entry key "lint.fieldAllow" field_allow
      <|> apply_bucket_alias? style entry key "lint.declarationAllow" declaration_allow
      <|> apply_bucket_alias? style entry key "lint.recursiveHelperAllow" recursive_helper_allow
      <|> apply_bucket_alias? style entry key "lint.lambdaAllow" lambda_allow
      <|> apply_bucket_alias? style entry key "lint.letAllow" let_allow

private
def apply_dynamic_entry (s : Style) (e : config_entry) (key : String) : Except String Style :=
  match apply_dotted_bucket_entry? s e key with
  | some result => result
  | none =>
    match apply_lean_bucket_entry? s e key with
    | some result => result
    | none        => throw s!"line {e.line}: unknown option `{key}`"

private
def apply_layout_or_breaking_entry (s : Style) (e : config_entry) : Except String Style := do
  match e.key with
  | "layout.lineWidth" => pure { s with layout.lineWidth := ← as_nat e }
  | "layout.indent" => pure { s with layout.indent := ← as_nat e }
  | "layout.continuationIndent" => pure { s with layout.continuationIndent := ← as_nat e }
  | "layout.bodyFitWidth" => pure { s with layout.bodyFitWidth := ← as_nat e }
  | "breaking.colon" =>
    match colon_placement.of_string? e.val with
    | some value => pure { s with breaking.colon := value }
    | none => throw s!"line {e.line}: `{e.key}` expects breakBefore/breakAfter"
  | "breaking.binders" =>
    match binder_layout.of_string? e.val with
    | some value => pure { s with breaking.binders := value }
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
    | some value => pure { s with breaking.opBreak := value }
    | none => throw s!"line {e.line}: `{e.key}` expects leading/trailing"
  | key => throw s!"line {e.line}: unknown option `{key}`"

private
def apply_symbol_policy (s : Style) (e : config_entry) : Except String Style :=
  match e.val with
  | "systems" =>
    pure { s with linting.allowGreekSymbols := false, linting.allowHebrewSymbols := false }
  | "traditionalLean" =>
    pure { s with linting.allowGreekSymbols := true, linting.allowHebrewSymbols := false }
  | _ => throw s!"line {e.line}: `{e.key}` expects systems/traditionalLean"

private
def apply_symbol_deny (s : Style) (e : config_entry) : Style :=
  let names :=
    if e.val.trimAscii.isEmpty then [] else (e.val.splitOn ",").map (·.trimAscii.toString)
  { s with linting.symbolDeny := names }

private
def apply_lint_entry (s : Style) (e : config_entry) : Except String Style := do
  match e.key with
  | "lint.symbolMinChars" => pure { s with linting.symbolMinChars := ← as_nat e }
  | "lint.branchDensityMax" => pure { s with linting.branchDensityMax := ← as_nat e }
  | "lint.handlerParameterMax" => pure { s with linting.handlerParameterMax := ← as_nat e }
  | "lint.requireStanzaComments" => pure { s with linting.requireStanzaComments := ← as_bool e }
  | "lint.symbolDeny" => pure (apply_symbol_deny s e)
  | "lint.symbolPolicy" => apply_symbol_policy s e
  | "lint.allowGreekSymbols" => pure { s with linting.allowGreekSymbols := ← as_bool e }
  | "lint.allowHebrewSymbols" => pure { s with linting.allowHebrewSymbols := ← as_bool e }
  | "lint.allowTraditionalInstances" =>
    pure { s with linting.allowTraditionalInstances := ← as_bool e }
  | "lint.requireTraditionalInstances" =>
    pure { s with linting.requireTraditionalInstances := ← as_bool e }
  | "lint.requirePositionalLoopNames" =>
    pure { s with linting.requirePositionalLoopNames := ← as_bool e }
  | "lint.requireSemanticPatternBinders" =>
    pure { s with linting.requireSemanticPatternBinders := ← as_bool e }
  | "lint.requireSemanticCollectionLoopNames" =>
    pure { s with linting.requireSemanticCollectionLoopNames := ← as_bool e }
  | "lint.requireSemanticFieldNames" =>
    pure { s with linting.requireSemanticFieldNames := ← as_bool e }
  | "lint.requireSemanticDeclarationNames" =>
    pure { s with linting.requireSemanticDeclarationNames := ← as_bool e }
  | "lint.requireSemanticRecursiveHelperNames" =>
    pure { s with linting.requireSemanticRecursiveHelperNames := ← as_bool e }
  | "lint.requireSemanticLambdaNames" =>
    pure { s with linting.requireSemanticLambdaNames := ← as_bool e }
  | "lint.requireSemanticLetNames" => pure { s with linting.requireSemanticLetNames := ← as_bool e }
  | key => apply_dynamic_entry s e key

/-- Apply one entry to a style. The single source of truth for the key space —
    an unknown key is an error here, which is what makes a typo'd axis LOUD. -/
def apply_entry (s : Style) (e : config_entry) : Except String Style := do
  if e.key.startsWith "layout." || e.key.startsWith "breaking." then
    return ← apply_layout_or_breaking_entry s e
  if e.key.startsWith "lint." then
    return ← apply_lint_entry s e
  match e.key with
  | "preset" =>
    match by_name? e.val with
    | some pathValue => pure pathValue
    | none => throw s!"line {e.line}: unknown preset `{e.val}`"
  | "alignment.structFields" => pure { s with alignment.structFields := ← as_align e }
  | "alignment.matchArms" => pure { s with alignment.matchArms := ← as_align e }
  | "alignment.letBlocks" => pure { s with alignment.letBlocks := ← as_align e }
  | "alignment.recordFields" => pure { s with alignment.recordFields := ← as_align e }
  | "alignment.trailingComments" => pure { s with alignment.trailingComments := ← as_align e }
  | "alignment.binderGroups" => pure { s with alignment.binderGroups := ← as_align e }
  | "alignment.maxDelta" => pure { s with alignment.maxDelta := ← as_nat e }
  | "blankLines.policy" =>
    match blank_policy.of_string? e.val with
    | some value => pure { s with blankLines.policy := value }
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
  | key => throw s!"line {e.line}: unknown option `{key}`"

/-- Apply a whole config (one fmt.lean) onto a base style, in entry order. -/
def apply_config (s : Style) (entries : List config_entry) : Except String Style :=
  entries.foldlM apply_entry s

/-- Parse + apply in one step (the per-file unit the resolver folds). -/
def apply_config_text (s : Style) (text : String) : Except String Style := do
  apply_config s (← parse_config text)

end Lean4Fmt.Style
