/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // LEAN4FMT // STYLE // OPTIONS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The fully-resolved `Style` the renderer reads (DESIGN_V2 §5), grouped into
    sub-records so --help / docs / presets stay navigable. Choice-knobs are enums
    with FromString so config parse and `--set group.key=value` are mechanical.

    Pure. Depends on nothing.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Lean4Fmt.Style

-- ── choice knobs ────────────────────────────────────────────────────────────

inductive ColonPlacement | breakBefore | breakAfter
  deriving Repr, Inhabited, BEq

inductive AlignMode | always | whenShort | never
  deriving Repr, Inhabited, BEq

inductive BlankPolicy | preserve | impose | normalize
  deriving Repr, Inhabited, BEq

inductive BinderLayout | oneLine | onePerLine | fill
  deriving Repr, Inhabited, BEq

def AlignMode.ofString? : String → Option AlignMode
  | "always" => some .always | "whenShort" => some .whenShort
  | "never" => some .never | _ => none

def BlankPolicy.ofString? : String → Option BlankPolicy
  | "preserve" => some .preserve | "impose" => some .impose
  | "normalize" => some .normalize | _ => none

def ColonPlacement.ofString? : String → Option ColonPlacement
  | "breakBefore" => some .breakBefore | "breakAfter" => some .breakAfter | _ => none

def BinderLayout.ofString? : String → Option BinderLayout
  | "oneLine" => some .oneLine | "onePerLine" => some .onePerLine
  | "fill" => some .fill | _ => none

-- ── grouped sub-records ─────────────────────────────────────────────────────

structure Layout where
  lineWidth          : Nat := 100
  indent             : Nat := 2
  continuationIndent : Nat := 4
  deriving Repr, Inhabited

structure Breaking where
  colon            : ColonPlacement := .breakAfter
  binders          : BinderLayout := .oneLine
  attributesOwnLine : Bool := false   -- `@[…]` on its own line above the keyword
  bodyOwnLine      : Bool := false   -- broken decls: `:=` ends the sig, blank, body at indent
  bodyAlwaysBreak  : Bool := false   -- body on its own line even when it fits inline (purtell)
  /-- Author line breaks are load-bearing: a construct written multi-line
      stays multi-line (no width-collapse); single-line stays byte-exact. -/
  preserveLineBreaks : Bool := false
  compactDo        : Bool := true
  elseIfChain      : Bool := true
  /-- A single clean branch statement rides inline after its keyword when it
      fits (`if ok then pure true`); off = always on its own line. -/
  inlineBranches   : Bool := true
  /-- Bare (typeless, docless) inductive constructors join on ONE line when
      they fit (`| GET | POST | PUT`); off = one per line. -/
  ctorsOneLine     : Bool := false
  deriving Repr, Inhabited

structure Alignment where
  structFields     : AlignMode := .whenShort
  matchArms        : AlignMode := .whenShort
  letBlocks        : AlignMode := .never
  recordFields     : AlignMode := .whenShort
  trailingComments : AlignMode := .never
  binderGroups     : AlignMode := .never
  maxDelta         : Nat := 8
  deriving Repr, Inhabited

structure BlankLines where
  policy               : BlankPolicy := .normalize
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

structure Spacing where
  aroundOperators : Bool := true
  insideBrackets  : Bool := true
  afterComma      : Bool := true
  /-- Reproduce binder interiors byte-exact (`(s: String)` stays) instead of
      single-space token normalization (`(s : String)`). -/
  preserveBinders : Bool := false
  deriving Repr, Inhabited

structure Imports where
  group : Bool := true
  sort  : Bool := false
  deriving Repr, Inhabited

structure Comments where
  spaceAfterDashes : Bool := true   -- `--foo` → `-- foo`
  deriving Repr, Inhabited

/-- The fully-resolved style. -/
structure Style where
  layout     : Layout := {}
  breaking   : Breaking := {}
  alignment  : Alignment := {}
  blankLines : BlankLines := {}
  spacing    : Spacing := {}
  imports    : Imports := {}
  comments   : Comments := {}
  deriving Repr, Inhabited

end Lean4Fmt.Style
