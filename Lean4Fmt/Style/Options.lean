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

-- ── grouped sub-records ─────────────────────────────────────────────────────

structure Layout where
  lineWidth          : Nat := 100
  indent             : Nat := 2
  continuationIndent : Nat := 4
  deriving Repr, Inhabited

structure Breaking where
  colon        : ColonPlacement := .breakAfter
  binders      : BinderLayout := .oneLine
  compactDo    : Bool := true
  elseIfChain  : Bool := true
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
