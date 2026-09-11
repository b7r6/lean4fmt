/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // LEAN4FMT // STYLE // OPTIONS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The fully-resolved `Style` the renderer reads (doc/design.md §7), grouped into
    sub-records so --help / docs / presets stay navigable. Choice-knobs are enums
    with FromString so config parse and `--set group.key=value` are mechanical.

    Pure. Depends only on `Casing` (the `Case` enum).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.casing

namespace Lean4Fmt.Style

-- ── choice knobs ──────────────────────────────────────────────────────────────

inductive colon_placement
  | breakBefore
  | breakAfter
  deriving Repr, Inhabited, BEq

inductive align_mode
  | always
  | whenShort
  | never
  deriving Repr, Inhabited, BEq

inductive blank_policy
  | preserve
  | impose
  | normalize
  deriving Repr, Inhabited, BEq

inductive binder_layout
  | oneLine
  | onePerLine
  | fill
  /-- The constraint solver chooses per-declaration (`Solve.sigOneLineFits`):
      a broken sig rides ONE line (`oneLine`) while its binders fit the keyword
      line, and stacks (`onePerLine`) once they do not — so a short-binder def
      no longer explodes just because its BODY forced the break. Requires
      `solveDefs`. -/
  | adaptive
  deriving Repr, Inhabited, BEq

/-- Where a broken operator chain puts the operator: `leading` starts the
    continuation line with it (house); `trailing` ends the previous line with
    it (mathlib arrows). clang-format's BreakBeforeBinaryOperators. -/
inductive op_break
  | leading
  | trailing
  deriving Repr, Inhabited, BEq

def align_mode.of_string? : String → Option align_mode
  | "always"    => some .always
  | "whenShort" => some .whenShort
  | "never"     => some .never
  | _           => none

def blank_policy.of_string? : String → Option blank_policy
  | "preserve"  => some .preserve
  | "impose"    => some .impose
  | "normalize" => some .normalize
  | _           => none

def colon_placement.of_string? : String → Option colon_placement
  | "breakBefore" => some .breakBefore
  | "breakAfter"  => some .breakAfter
  | _             => none

def binder_layout.of_string? : String → Option binder_layout
  | "oneLine"    => some .oneLine
  | "onePerLine" => some .onePerLine
  | "fill"       => some .fill
  | "adaptive"   => some .adaptive
  | _            => none

def op_break.of_string? : String → Option op_break
  | "leading"  => some .leading
  | "trailing" => some .trailing
  | _          => none

-- ── grouped sub-records ───────────────────────────────────────────────────────

structure Layout where
  lineWidth          : Nat := 100
  indent             : Nat := 2
  continuationIndent : Nat := 4
  /-- Softer width for the WHOLE-DECL inline form (`sig := body` on one
      line): inline only when the total fits BOTH this and lineWidth; past
      it the body breaks to its own line even though the line would fit.
      Mathlib-shaped corpora inline short decls but break bodies well before
      the hard width. Default = effectively off. -/
  bodyFitWidth : Nat := 1000
  deriving Repr, Inhabited

structure breaking where
  colon : colon_placement := .breakAfter
  binders : binder_layout := .oneLine
  attributesOwnLine : Bool := false -- `@[…]` on its own line above the keyword
  /-- `private`/`protected`/`noncomputable`/… on their OWN line above the
      keyword. The keyword then starts at column 0, so `onePerLine` binders
      (aligned under the name) hang at a uniform +4 instead of deep under
      `private def `. Requires `attributesOwnLine`. -/
  visibilityOwnLine : Bool := false
  bodyOwnLine     : Bool := false -- broken decls: `:=` ends the sig, blank, body at indent
  bodyAlwaysBreak : Bool := false -- body on its own line even when it fits inline (purtell)
  /-- Author line breaks are load-bearing: a construct written multi-line
      stays multi-line (no width-collapse); single-line stays byte-exact. -/
  preserveLineBreaks : Bool := false
  compactDo   : Bool := true
  elseIfChain : Bool := true
  /-- A single clean branch statement rides inline after its keyword when it
      fits (`if ok then pure true`); off = always on its own line. -/
  inlineBranches : Bool := true
  /-- A `do`-position if whose branch is CONTROL FLOW (`return`/`throw`)
      keeps the branch on its own line even when it fits — the guard
      ladder reads vertically. Effect branches still inline by width. -/
  guardIfOwnLine : Bool := false
  /-- Bare (typeless, docless) inductive constructors join on ONE line when
      they fit (`| GET | POST | PUT`); off = one per line. -/
  ctorsOneLine : Bool := false
  /-- `:= fun … =>` GLUES to the signature line (the lambda head rides the
      decl, its body breaks below) — the mathlib idiom; off = the fun is an
      ordinary body (inline when it fits, else its own line). -/
  glueFun : Bool := false
  /-- Operator position when a binop/arrow chain breaks (see `OpBreak`). -/
  opBreak : op_break := .leading
  /-- Over-width bracket lists (`simp only [...]`, `rw [...]`) FILL — items
      pack per line and wrap at the width, the closer glued to the last item
      (the mathlib shape); off = the all-or-nothing commaList (one item per
      line when broken). -/
  listFill : Bool := false
  /-- Route a `def`'s inline-vs-break layout decision through the constraint
      solver (`Solve.Layout`) — the measure-algebra `bestUnder` (hard-width
      filter then cost argmin) instead of an ad-hoc width test. Byte-identical
      on flat sigs today (feasibility is the whole story); the seam the rung
      ladder + preference weights widen. Off = the classic `total ≤ width`. -/
  solveDefs : Bool := false
  deriving Repr, Inhabited

structure alignment where
  structFields     : align_mode := .whenShort
  matchArms        : align_mode := .whenShort
  letBlocks        : align_mode := .never
  recordFields     : align_mode := .whenShort
  trailingComments : align_mode := .never
  binderGroups     : align_mode := .never
  maxDelta         : Nat := 8
  deriving Repr, Inhabited

structure blank_lines where
  policy               : blank_policy := .normalize
  betweenTopLevelDecls : Nat := 1
  betweenImportGroups  : Nat := 1
  afterNamespaceOpen   : Nat := 1
  beforeNamespaceEnd   : Nat := 1
  beforeDocComment     : Nat := 1
  beforeSectionBanner  : Nat := 1
  afterSectionBanner   : Nat := 1
  betweenDeclKinds     : Bool := false
  aroundBlockComments  : Nat := 1
  insideDoPhases       : Bool := false
  maxConsecutive       : Nat := 1
  deriving Repr, Inhabited

structure spacing where
  aroundOperators : Bool := true
  insideBrackets  : Bool := true
  afterComma      : Bool := true
  /-- Reproduce binder interiors byte-exact (`(s: String)` stays) instead of
      single-space token normalization (`(s : String)`). -/
  preserveBinders : Bool := false
  deriving Repr, Inhabited

structure imports where
  group : Bool := true
  sort  : Bool := false
  deriving Repr, Inhabited

structure comments where
  spaceAfterDashes : Bool := true -- `--foo` → `-- foo`
  deriving Repr, Inhabited

/-- Identifier casing per declaration AXIS — the rename policy. Code default is
    `preserve` (inert); the packaged preset (straylight) carries the house policy.
    A rename CHANGES tokens, so this rides a build-validated project pass, NOT the
    token-preserving formatter — there is no degrade-to-identity floor here. -/
structure Naming where
  namespaces : Lean4Fmt.Casing.Case := .preserve -- namespace / module names
  types      : Lean4Fmt.Casing.Case := .preserve -- structure / inductive / class
  theorems   : Lean4Fmt.Casing.Case := .preserve -- theorem / lemma / axiom (Prop-valued)
  terms      : Lean4Fmt.Casing.Case := .preserve -- def / abbrev / instance / fields
  deriving Repr, Inhabited

/-- Diagnostic-only policy for short bound names. `symbolAllow` is keyed by
    EXACT character count: an entry at 2 never exempts a one-character name.
    A zero floor disables the rule, which keeps non-house styles inert. -/
structure Linting where
  symbolMinChars : Nat := 0
  /-- Maximum direct control-flow dispatch points in an executable definition.
      Zero disables the rule. -/
  branchDensityMax : Nat := 0
  /-- Maximum explicit value parameters on one declaration. Zero disables the
      rule. Implicit/strict-implicit and instance binders do not consume it. -/
  handlerParameterMax : Nat := 0
  /-- Require every blank-line stanza break inside an executable definition to
      introduce the next block with an immediately following comment. -/
  requireStanzaComments : Bool := false
  symbolAllow : List (Nat × List String) := []
  symbolDeny : List String := []
  declarationAllow : List (Nat × List String) := []
  fieldAllow : List (Nat × List String) := []
  recursiveHelperAllow : List (Nat × List String) := []
  lambdaAllow : List (Nat × List String) := []
  letAllow : List (Nat × List String) := []
  allowGreekSymbols : Bool := false
  allowHebrewSymbols : Bool := false
  allowTraditionalInstances : Bool := true
  /-- Require every named instance binder to use a Greek or Hebrew base letter
      followed only by Unicode modifier/subscript characters. -/
  requireTraditionalInstances : Bool := false
  /-- Require positional bracket-range loop binders to follow the HFT
      `idx`/`jdx`/`kdx` convention by positional nesting depth. -/
  requirePositionalLoopNames : Bool := false
  /-- Require pattern and match-arm binders to meet the configured semantic
      symbol floor; pattern position grants no blanket short-name exemption. -/
  requireSemanticPatternBinders : Bool := false
  /-- Require non-range collection loops to use semantic element names rather
      than the positional `idx`/`jdx`/`kdx` counter vocabulary. -/
  requireSemanticCollectionLoopNames : Bool := false
  /-- Require structure and class fields to use semantic names, subject to the
      exact-length `fieldAllow` exception buckets. -/
  requireSemanticFieldNames : Bool := false
  /-- Require source-level declarations and constructors to use semantic names,
      subject to exact-length `declarationAllow` exception buckets. -/
  requireSemanticDeclarationNames : Bool := false
  /-- Require local recursive helper declarations to use semantic names, subject
      to exact-length `recursiveHelperAllow` exception buckets. -/
  requireSemanticRecursiveHelperNames : Bool := false
  /-- Require lambda binders to use semantic names, subject to exact-length
      `lambdaAllow` exception buckets. -/
  requireSemanticLambdaNames : Bool := false
  /-- Require let binders to use semantic names, subject to exact-length
      `letAllow` exception buckets. -/
  requireSemanticLetNames : Bool := false
  deriving Repr, Inhabited

/-- The fully-resolved style. -/
structure Style where
  layout     : Layout := {}
  breaking   : breaking := {}
  alignment  : alignment := {}
  blankLines : blank_lines := {}
  spacing    : spacing := {}
  imports    : imports := {}
  comments   : comments := {}
  naming     : Naming := {}
  linting    : Linting := {}
  deriving Repr, Inhabited

end Lean4Fmt.Style
