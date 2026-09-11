/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // STYLE // CONFIG
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `fmt.lean` — the project configuration DSL (doc/design.md §7). A fmt.lean sits
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

import lean_4_fmt.style.options
import lean_4_fmt.style.preset

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
def unquote (value : String) : String :=
  let value := value.trimAscii.toString
  if value.length ≥ 2 && value.startsWith "\"" && value.endsWith "\"" then
    ((value.drop 1).dropRight 1).toString
  else
    value

private
def config_entry_of_parts (rawKey value : String) (line : Nat) : Except String config_entry := do
  let key := rawKey.trimAscii.toString
  if key.isEmpty || key.any (fun character => character == ' ') then
    throw
      s!
          "line {line}: bad key `{key}`"
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
    throw
      s!
          "line {headerLine}: expected a literal after `:=`"
  let entry ← parse_config_entry
    s!
      "{header} {text}"
    headerLine
  return { state with entries := state.entries ++ [entry], pending := none }

private
def consume_fresh_config_line
    (state : config_parse_state)
    (text : String)
    : Except String config_parse_state := do
  if !text.startsWith "def " then
    throw
      s!
          "line {state.line}: expected `def <key> := <value>` (got: {text})"
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
  | some (_, headerLine) =>
    throw
      s!
          "line {headerLine}: expected a literal after `:=`"
  | none => return state.entries

private
def as_nat (element : config_entry) : Except String Nat :=
  match element.val.toNat? with
  | some count => pure count
  | none => throw s!"line {element.line}: `{element.key}` expects a number (got `{element.val}`)"

private
def as_bool (element : config_entry) : Except String Bool :=
  match element.val with
  | "true" => pure true
  | "false" => pure false
  | _ => throw s!"line {element.line}: `{element.key}` expects true/false (got `{element.val}`)"

private
def as_align (element : config_entry) : Except String align_mode :=
  match align_mode.of_string? element.val with
  | some candidate => pure candidate
  | none =>
    throw
      s!"line {element.line}: `{element.key}` expects always/whenShort/never (got `{element.val}`)"

private
def as_case (element : config_entry) : Except String Lean4Fmt.Casing.Case :=
  match Lean4Fmt.Casing.Case.of_string? element.val with
  | some headChar => pure headChar
  | none =>
    throw
      s!"line {element.line}: `{element.key}` expects snake/camel/upperCamel/preserve (got `{element.val}`)"

private
def symbol_allow (source : Style) (element : config_entry) (size : Nat) : Except String Style := do
  let names :=
    if element.val.trimAscii.isEmpty then
      []
    else
      (element.val.splitOn ",").map (·.trimAscii.toString)
  for name in names do
    if name.isEmpty || name.length != size then
      throw
        s!
              "line {element.line}: `{element.key}` entries must have exactly {size} characters (got `{name}`)"
  let allow := (source.linting.symbolAllow.filter (·.1 != size)) ++ [(size, names)]
  pure { source with linting.symbolAllow := allow }

private
def field_allow (source : Style) (element : config_entry) (size : Nat) : Except String Style := do
  let names :=
    if element.val.trimAscii.isEmpty then
      []
    else
      (element.val.splitOn ",").map (·.trimAscii.toString)
  for name in names do
    let segments := name.splitOn "."
    let leaf := segments.getLast!
    if name.isEmpty || segments.any (·.isEmpty) || leaf.length != size then
      throw
        s!
              "line {element.line}: `{element.key}` entries must have a leaf with exactly {size} characters (got `{name}`)"
  let allow := (source.linting.fieldAllow.filter (·.1 != size)) ++ [(size, names)]
  pure { source with linting.fieldAllow := allow }

private
def declaration_allow
    (source : Style)
    (element : config_entry)
    (size : Nat)
    : Except String Style := do
  let names :=
    if element.val.trimAscii.isEmpty then
      []
    else
      (element.val.splitOn ",").map (·.trimAscii.toString)
  for name in names do
    let segments := name.splitOn "."
    let leaf := segments.getLast!
    if name.isEmpty || segments.any (·.isEmpty) || leaf.length != size then
      throw
        s!
              "line {element.line}: `{element.key}` entries must have a leaf with exactly {size} characters (got `{name}`)"
  let allow := (source.linting.declarationAllow.filter (·.1 != size)) ++ [(size, names)]
  pure { source with linting.declarationAllow := allow }

private
def recursive_helper_allow
    (source : Style)
    (element : config_entry)
    (size : Nat)
    : Except String Style := do
  let names :=
    if element.val.trimAscii.isEmpty then
      []
    else
      (element.val.splitOn ",").map (·.trimAscii.toString)
  for name in names do
    if name.isEmpty || name.length != size then
      throw
        s!
              "line {element.line}: `{element.key}` entries must have exactly {size} characters (got `{name}`)"
  let allow := (source.linting.recursiveHelperAllow.filter (·.1 != size)) ++ [(size, names)]
  pure { source with linting.recursiveHelperAllow := allow }

private
def lambda_allow (source : Style) (element : config_entry) (size : Nat) : Except String Style := do
  let names :=
    if element.val.trimAscii.isEmpty then
      []
    else
      (element.val.splitOn ",").map (·.trimAscii.toString)
  for name in names do
    if name.isEmpty || name.length != size then
      throw
        s!
              "line {element.line}: `{element.key}` entries must have exactly {size} characters (got `{name}`)"
  let allow := (source.linting.lambdaAllow.filter (·.1 != size)) ++ [(size, names)]
  pure { source with linting.lambdaAllow := allow }

private
def let_allow (source : Style) (element : config_entry) (size : Nat) : Except String Style := do
  let names :=
    if element.val.trimAscii.isEmpty then
      []
    else
      (element.val.splitOn ",").map (·.trimAscii.toString)
  for name in names do
    if name.isEmpty || name.length != size then
      throw
        s!
              "line {element.line}: `{element.key}` entries must have exactly {size} characters (got `{name}`)"
  let allow := (source.linting.letAllow.filter (·.1 != size)) ++ [(size, names)]
  pure { source with linting.letAllow := allow }

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
def apply_dynamic_entry
    (source : Style)
    (element : config_entry)
    (key : String)
    : Except String Style :=
  match apply_dotted_bucket_entry? source element key with
  | some result => result
  | none =>
    match apply_lean_bucket_entry? source element key with
    | some result => result
    | none        => throw s!"line {element.line}: unknown option `{key}`"

private
def apply_layout_or_breaking_entry
    (source : Style)
    (element : config_entry)
    : Except String Style := do
  match element.key with
  | "layout.lineWidth" => pure { source with layout.lineWidth := ← as_nat element }
  | "layout.indent" => pure { source with layout.indent := ← as_nat element }
  | "layout.continuationIndent" =>
    pure { source with layout.continuationIndent := ← as_nat element }
  | "layout.bodyFitWidth" => pure { source with layout.bodyFitWidth := ← as_nat element }
  | "breaking.colon" =>
    match colon_placement.of_string? element.val with
    | some value => pure { source with breaking.colon := value }
    | none =>
      throw
        s!
              "line {element.line}: `{element.key}` expects breakBefore/breakAfter"
  | "breaking.binders" =>
    match binder_layout.of_string? element.val with
    | some value => pure { source with breaking.binders := value }
    | none =>
      throw
        s!
              "line {element.line}: `{element.key}` expects oneLine/onePerLine/fill/adaptive"
  | "breaking.attributesOwnLine" =>
    pure { source with breaking.attributesOwnLine := ← as_bool element }
  | "breaking.visibilityOwnLine" =>
    pure { source with breaking.visibilityOwnLine := ← as_bool element }
  | "breaking.bodyOwnLine" => pure { source with breaking.bodyOwnLine := ← as_bool element }
  | "breaking.bodyAlwaysBreak" => pure { source with breaking.bodyAlwaysBreak := ← as_bool element }
  | "breaking.preserveLineBreaks" =>
    pure { source with breaking.preserveLineBreaks := ← as_bool element }
  | "breaking.compactDo" => pure { source with breaking.compactDo := ← as_bool element }
  | "breaking.elseIfChain" => pure { source with breaking.elseIfChain := ← as_bool element }
  | "breaking.inlineBranches" => pure { source with breaking.inlineBranches := ← as_bool element }
  | "breaking.guardIfOwnLine" => pure { source with breaking.guardIfOwnLine := ← as_bool element }
  | "breaking.ctorsOneLine" => pure { source with breaking.ctorsOneLine := ← as_bool element }
  | "breaking.glueFun" => pure { source with breaking.glueFun := ← as_bool element }
  | "breaking.listFill" => pure { source with breaking.listFill := ← as_bool element }
  | "breaking.solveDefs" => pure { source with breaking.solveDefs := ← as_bool element }
  | "breaking.opBreak" =>
    match op_break.of_string? element.val with
    | some value => pure { source with breaking.opBreak := value }
    | none =>
      throw
        s!
              "line {element.line}: `{element.key}` expects leading/trailing"
  | key =>
    throw
      s!
          "line {element.line}: unknown option `{key}`"

private
def apply_symbol_policy (source : Style) (element : config_entry) : Except String Style :=
  match element.val with
  | "systems" =>
    pure { source with linting.allowGreekSymbols := false, linting.allowHebrewSymbols := false }
  | "traditionalLean" =>
    pure { source with linting.allowGreekSymbols := true, linting.allowHebrewSymbols := false }
  | _ => throw s!"line {element.line}: `{element.key}` expects systems/traditionalLean"

private
def apply_symbol_deny (source : Style) (element : config_entry) : Style :=
  let names :=
    if element.val.trimAscii.isEmpty then
      []
    else
      (element.val.splitOn ",").map (·.trimAscii.toString)
  { source with linting.symbolDeny := names }

private
def apply_lint_entry (source : Style) (element : config_entry) : Except String Style := do
  match element.key with
  | "lint.symbolMinChars" => pure { source with linting.symbolMinChars := ← as_nat element }
  | "lint.branchDensityMax" => pure { source with linting.branchDensityMax := ← as_nat element }
  | "lint.handlerParameterMax" =>
    pure { source with linting.handlerParameterMax := ← as_nat element }
  | "lint.requireStanzaComments" =>
    pure { source with linting.requireStanzaComments := ← as_bool element }
  | "lint.symbolDeny" => pure (apply_symbol_deny source element)
  | "lint.symbolPolicy" => apply_symbol_policy source element
  | "lint.allowGreekSymbols" => pure { source with linting.allowGreekSymbols := ← as_bool element }
  | "lint.allowHebrewSymbols" =>
    pure { source with linting.allowHebrewSymbols := ← as_bool element }
  | "lint.allowTraditionalInstances" =>
    pure { source with linting.allowTraditionalInstances := ← as_bool element }
  | "lint.requireTraditionalInstances" =>
    pure { source with linting.requireTraditionalInstances := ← as_bool element }
  | "lint.requirePositionalLoopNames" =>
    pure { source with linting.requirePositionalLoopNames := ← as_bool element }
  | "lint.requireSemanticPatternBinders" =>
    pure { source with linting.requireSemanticPatternBinders := ← as_bool element }
  | "lint.requireSemanticCollectionLoopNames" =>
    pure { source with linting.requireSemanticCollectionLoopNames := ← as_bool element }
  | "lint.requireSemanticFieldNames" =>
    pure { source with linting.requireSemanticFieldNames := ← as_bool element }
  | "lint.requireSemanticDeclarationNames" =>
    pure { source with linting.requireSemanticDeclarationNames := ← as_bool element }
  | "lint.requireSemanticRecursiveHelperNames" =>
    pure { source with linting.requireSemanticRecursiveHelperNames := ← as_bool element }
  | "lint.requireSemanticLambdaNames" =>
    pure { source with linting.requireSemanticLambdaNames := ← as_bool element }
  | "lint.requireSemanticLetNames" =>
    pure { source with linting.requireSemanticLetNames := ← as_bool element }
  | key => apply_dynamic_entry source element key

/-- Resolve a preset entry or report its source line. -/
private
def apply_preset_entry (entry : config_entry) : Except String Style :=
  match by_name? entry.val with
  | some preset => pure preset
  | none        => throw s!"line {entry.line}: unknown preset `{entry.val}`"

/-- Apply one entry to a style. The single source of truth for the key space —
    an unknown key is an error here, which is what makes a typo'd axis LOUD. -/
def apply_entry (style : Style) (entry : config_entry) : Except String Style := do
  if entry.key.startsWith "layout." || entry.key.startsWith "breaking." then
    return ← apply_layout_or_breaking_entry style entry
  if entry.key.startsWith "lint." then
    return ← apply_lint_entry style entry
  match entry.key with
  | "preset" => apply_preset_entry entry
  | "alignment.structFields" => pure { style with alignment.structFields := ← as_align entry }
  | "alignment.matchArms" => pure { style with alignment.matchArms := ← as_align entry }
  | "alignment.letBlocks" => pure { style with alignment.letBlocks := ← as_align entry }
  | "alignment.recordFields" => pure { style with alignment.recordFields := ← as_align entry }
  | "alignment.trailingComments" =>
    pure { style with alignment.trailingComments := ← as_align entry }
  | "alignment.binderGroups" => pure { style with alignment.binderGroups := ← as_align entry }
  | "alignment.maxDelta" => pure { style with alignment.maxDelta := ← as_nat entry }
  | "blankLines.policy" =>
    match blank_policy.of_string? entry.val with
    | some value => pure { style with blankLines.policy := value }
    | none =>
      throw
        s!
              "line {entry.line}: `{entry.key}` expects preserve/impose/normalize"
  | "blankLines.betweenTopLevelDecls" =>
    pure { style with blankLines.betweenTopLevelDecls := ← as_nat entry }
  | "blankLines.betweenImportGroups" =>
    pure { style with blankLines.betweenImportGroups := ← as_nat entry }
  | "blankLines.afterNamespaceOpen" =>
    pure { style with blankLines.afterNamespaceOpen := ← as_nat entry }
  | "blankLines.beforeNamespaceEnd" =>
    pure { style with blankLines.beforeNamespaceEnd := ← as_nat entry }
  | "blankLines.beforeDocComment" =>
    pure { style with blankLines.beforeDocComment := ← as_nat entry }
  | "blankLines.beforeSectionBanner" =>
    pure { style with blankLines.beforeSectionBanner := ← as_nat entry }
  | "blankLines.afterSectionBanner" =>
    pure { style with blankLines.afterSectionBanner := ← as_nat entry }
  | "blankLines.betweenDeclKinds" =>
    pure { style with blankLines.betweenDeclKinds := ← as_bool entry }
  | "blankLines.aroundBlockComments" =>
    pure { style with blankLines.aroundBlockComments := ← as_nat entry }
  | "blankLines.insideDoPhases" => pure { style with blankLines.insideDoPhases := ← as_bool entry }
  | "blankLines.maxConsecutive" => pure { style with blankLines.maxConsecutive := ← as_nat entry }
  | "spacing.aroundOperators" => pure { style with spacing.aroundOperators := ← as_bool entry }
  | "spacing.insideBrackets" => pure { style with spacing.insideBrackets := ← as_bool entry }
  | "spacing.afterComma" => pure { style with spacing.afterComma := ← as_bool entry }
  | "spacing.preserveBinders" => pure { style with spacing.preserveBinders := ← as_bool entry }
  | "imports.group" => pure { style with imports.group := ← as_bool entry }
  | "imports.sort" => pure { style with imports.sort := ← as_bool entry }
  | "comments.spaceAfterDashes" => pure { style with comments.spaceAfterDashes := ← as_bool entry }
  | "naming.namespaces" => pure { style with naming.namespaces := ← as_case entry }
  | "naming.types" => pure { style with naming.types := ← as_case entry }
  | "naming.theorems" => pure { style with naming.theorems := ← as_case entry }
  | "naming.terms" => pure { style with naming.terms := ← as_case entry }
  | key =>
    throw
      s!
          "line {entry.line}: unknown option `{key}`"

/-- Apply a whole config (one fmt.lean) onto a base style, in entry order. -/
def apply_config (source : Style) (entries : List config_entry) : Except String Style :=
  entries.foldlM apply_entry source

/-- Parse + apply in one step (the per-file unit the resolver folds). -/
def apply_config_text (source : Style) (text : String) : Except String Style := do
  apply_config source (← parse_config text)

end Lean4Fmt.Style
