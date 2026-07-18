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
structure ConfigEntry where
  key : String
  val : String
  line : Nat
  deriving Repr, Inhabited

/-- Parse a literal value token: `"str"` → str, bare token kept as-is
    (numbers, `true`/`false`, bare enum names all arrive as their token). -/
private def unquote (v : String) : String :=
  let v := v.trimAscii.toString
  if v.length ≥ 2 && v.startsWith "\"" && v.endsWith "\"" then
    ((v.drop 1).dropRight 1).toString
  else v

/-- Parse fmt.lean text into entries. Accepted lines: blank, full-line `--`
    comment, or `def <dotted.key> := <literal>`. Anything else is an error —
    the DSL is deliberately small; taste lives in the keys, not the syntax. -/
def parseConfig (text : String) : Except String (List ConfigEntry) := do
  let mut out : List ConfigEntry := []
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
      out := out ++ [({ key, val := unquote v, line := n } : ConfigEntry)]
    | _ => throw s!"line {n}: expected `def <key> := <value>` (got: {t})"
  return out

private def asNat (e : ConfigEntry) : Except String Nat :=
  match e.val.toNat? with
  | some n => pure n
  | none => throw s!"line {e.line}: `{e.key}` expects a number (got `{e.val}`)"

private def asBool (e : ConfigEntry) : Except String Bool :=
  match e.val with
  | "true" => pure true
  | "false" => pure false
  | _ => throw s!"line {e.line}: `{e.key}` expects true/false (got `{e.val}`)"

private def asAlign (e : ConfigEntry) : Except String AlignMode :=
  match AlignMode.ofString? e.val with
  | some m => pure m
  | none => throw s!"line {e.line}: `{e.key}` expects always/whenShort/never (got `{e.val}`)"

/-- Apply one entry to a style. The single source of truth for the key space —
    an unknown key is an error here, which is what makes a typo'd axis LOUD. -/
def applyEntry (s : Style) (e : ConfigEntry) : Except String Style := do
  match e.key with
  | "preset" =>
    match byName? e.val with
    | some p => pure p
    | none => throw s!"line {e.line}: unknown preset `{e.val}`"
  | "layout.lineWidth" => pure { s with layout.lineWidth := ← asNat e }
  | "layout.indent" => pure { s with layout.indent := ← asNat e }
  | "layout.continuationIndent" => pure { s with layout.continuationIndent := ← asNat e }
  | "layout.bodyFitWidth" => pure { s with layout.bodyFitWidth := ← asNat e }
  | "breaking.colon" =>
    match ColonPlacement.ofString? e.val with
    | some v => pure { s with breaking.colon := v }
    | none => throw s!"line {e.line}: `{e.key}` expects breakBefore/breakAfter"
  | "breaking.binders" =>
    match BinderLayout.ofString? e.val with
    | some v => pure { s with breaking.binders := v }
    | none => throw s!"line {e.line}: `{e.key}` expects oneLine/onePerLine/fill"
  | "breaking.attributesOwnLine" => pure { s with breaking.attributesOwnLine := ← asBool e }
  | "breaking.bodyOwnLine" => pure { s with breaking.bodyOwnLine := ← asBool e }
  | "breaking.bodyAlwaysBreak" => pure { s with breaking.bodyAlwaysBreak := ← asBool e }
  | "breaking.preserveLineBreaks" => pure { s with breaking.preserveLineBreaks := ← asBool e }
  | "breaking.compactDo" => pure { s with breaking.compactDo := ← asBool e }
  | "breaking.elseIfChain" => pure { s with breaking.elseIfChain := ← asBool e }
  | "alignment.structFields" => pure { s with alignment.structFields := ← asAlign e }
  | "alignment.matchArms" => pure { s with alignment.matchArms := ← asAlign e }
  | "alignment.letBlocks" => pure { s with alignment.letBlocks := ← asAlign e }
  | "alignment.recordFields" => pure { s with alignment.recordFields := ← asAlign e }
  | "alignment.trailingComments" => pure { s with alignment.trailingComments := ← asAlign e }
  | "alignment.binderGroups" => pure { s with alignment.binderGroups := ← asAlign e }
  | "alignment.maxDelta" => pure { s with alignment.maxDelta := ← asNat e }
  | "blankLines.policy" =>
    match BlankPolicy.ofString? e.val with
    | some v => pure { s with blankLines.policy := v }
    | none => throw s!"line {e.line}: `{e.key}` expects preserve/impose/normalize"
  | "blankLines.betweenTopLevelDecls" => pure { s with blankLines.betweenTopLevelDecls := ← asNat e }
  | "blankLines.betweenImportGroups" => pure { s with blankLines.betweenImportGroups := ← asNat e }
  | "blankLines.afterNamespaceOpen" => pure { s with blankLines.afterNamespaceOpen := ← asNat e }
  | "blankLines.beforeNamespaceEnd" => pure { s with blankLines.beforeNamespaceEnd := ← asNat e }
  | "blankLines.beforeDocComment" => pure { s with blankLines.beforeDocComment := ← asNat e }
  | "blankLines.beforeSectionBanner" => pure { s with blankLines.beforeSectionBanner := ← asNat e }
  | "blankLines.afterSectionBanner" => pure { s with blankLines.afterSectionBanner := ← asNat e }
  | "blankLines.betweenDeclKinds" => pure { s with blankLines.betweenDeclKinds := ← asBool e }
  | "blankLines.aroundBlockComments" => pure { s with blankLines.aroundBlockComments := ← asNat e }
  | "blankLines.insideDoPhases" => pure { s with blankLines.insideDoPhases := ← asBool e }
  | "blankLines.maxConsecutive" => pure { s with blankLines.maxConsecutive := ← asNat e }
  | "spacing.aroundOperators" => pure { s with spacing.aroundOperators := ← asBool e }
  | "spacing.insideBrackets" => pure { s with spacing.insideBrackets := ← asBool e }
  | "spacing.afterComma" => pure { s with spacing.afterComma := ← asBool e }
  | "spacing.preserveBinders" => pure { s with spacing.preserveBinders := ← asBool e }
  | "imports.group" => pure { s with imports.group := ← asBool e }
  | "imports.sort" => pure { s with imports.sort := ← asBool e }
  | "comments.spaceAfterDashes" => pure { s with comments.spaceAfterDashes := ← asBool e }
  | k => throw s!"line {e.line}: unknown option `{k}`"

/-- Apply a whole config (one fmt.lean) onto a base style, in entry order. -/
def applyConfig (s : Style) (entries : List ConfigEntry) : Except String Style :=
  entries.foldlM applyEntry s

/-- Parse + apply in one step (the per-file unit the resolver folds). -/
def applyConfigText (s : Style) (text : String) : Except String Style := do
  applyConfig s (← parseConfig text)

end Lean4Fmt.Style
