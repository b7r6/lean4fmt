/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        // LEAN4FMT // EMITTER
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean

namespace Lean4Fmt

open Lean

-- the emitNode dispatch is a very long if/else chain; give the elaborator room
set_option maxRecDepth 100000

structure style_config where
  lineWidth       : Nat := 100
  indent          : Nat := 2
  maxBlankLines   : Nat := 1
  trailingNewline : Bool := true
  deriving Repr, Inhabited

inductive severity where
  | warning
  | error
  deriving Repr, Inhabited

structure Diagnostic where
  severity : severity
  pos      : Nat
  message  : String
  deriving Repr, Inhabited

structure emitter_state where
  output          : String := ""
  column          : Nat := 0
  indentLevel     : Nat := 0
  pendingNewlines : Nat := 0
  pendingSpace    : Bool := false
  /-- When true, suppress newlines (for inline expressions like match arm bodies) -/
  inlineMode : Bool := false
  lints : Array Diagnostic := #[]
  deriving Repr, Inhabited

abbrev emitter_m := ReaderT style_config (StateM emitter_state)

namespace emitter_m

def run
    (valueType : Type)
    (config : style_config)
    (modeValue : emitter_m valueType)
    : valueType × emitter_state :=
  StateT.run (ReaderT.run modeValue config) {}

def get_config : emitter_m style_config := read
def get_state : emitter_m emitter_state := get
def modify_state (transform : emitter_state → emitter_state) : emitter_m Unit := modify transform

def emit (source : String) : emitter_m Unit := do
  if source.isEmpty then
    return
  let config ← get_config
  let state ← get_state
  let mut out := state.output
  let mut col := state.column
  for _ in [:state.pendingNewlines] do out := out.push '\n'; col := 0
  if col == 0 && state.indentLevel > 0 then
    let spaces := String.ofList (List.replicate (state.indentLevel * config.indent) ' ')
    out := out ++ spaces; col := spaces.length
  if state.pendingSpace && col > 0 then out := out.push ' '; col := col + 1
  out := out ++ source
  for character in source.toList do
    if character == '\n' then col := 0
    else col := col + 1
  set { state with output := out, column := col, pendingNewlines := 0, pendingSpace := false }

def newline : emitter_m Unit := do
  let state ← get_state
  if state.inlineMode then
    return -- suppress newlines in inline mode
  let config ← get_config
  modify_state fun state =>
    { state with
      pendingNewlines := min (state.pendingNewlines + 1) (config.maxBlankLines + 1),
      pendingSpace := false }

def blank_line : emitter_m Unit := do newline; newline
def space : emitter_m Unit := modify_state fun state => { state with pendingSpace := true }

def indent : emitter_m Unit :=
  modify_state fun state => { state with indentLevel := state.indentLevel + 1 }

def dedent : emitter_m Unit :=
  modify_state fun state => { state with indentLevel := state.indentLevel - 1 }

/-- Run an action in inline mode (suppresses newlines) -/
def with_inline {valueType : Type} (modeValue : emitter_m valueType) : emitter_m valueType := do
  let oldInline := (← get_state).inlineMode
  modify_state fun state => { state with inlineMode := true }
  let result ← modeValue
  modify_state fun state => { state with inlineMode := oldInline }
  return result

/-- Emit a block of pre-rendered source text, RE-ANCHORED to the current indent:
    the block's own minimum indentation becomes the current indent level, and
    internal relative indentation is preserved. This is what makes verbatim
    reproduction safe for indentation-sensitive constructs (tactic blocks,
    `let rec`, `where`) even when the surrounding signature has been reflowed. -/
def emit_verbatim_str (source : String) : emitter_m Unit := do
  let nonblank (line : String) : Bool := line.any (· != ' ')
  -- split; drop leading/trailing blank lines
  let mut lines := source.splitOn "\n"
  lines := lines.dropWhile (fun line => !nonblank line)
  lines := (lines.reverse.dropWhile (fun line => !nonblank line)).reverse
  if lines.isEmpty then
    return
  let indentOf (lineValue : String) : Nat := (lineValue.toList.takeWhile (· == ' ')).length
  let base :=
    (lines.filter nonblank).foldl (fun minimum line => Nat.min minimum (indentOf line)) 1000000
  let base := if base == 1000000 then 0 else base
  let state ← get_state
  let mut first := true
  for line in lines do
    let ded := if line.length ≥ base then String.ofList (line.toList.drop base) else line
    if first then
      emit ded; first := false
    else if state.inlineMode then
      -- inline context: fold newlines into single spaces (best-effort)
      space; emit (ded.trimAsciiStart).toString
    else
      modify_state fun state =>
        { state with pendingNewlines := state.pendingNewlines + 1, pendingSpace := false }
      emit ded

private
def emit_verbatim_source (source : String) : emitter_m Unit := do

  -- Strip only trailing whitespace; KEEP the first line's leading indentation
  -- so `emitVerbatimStr`'s base-indent computation (and thus re-anchoring) is a
  -- fixed point across reformat passes. `t` (both ends) is only for the
  -- emptiness / multi-line tests.
  let sTrim := (source.trimAsciiEnd).toString
  let trimmed := (source.trimAscii).toString
  if trimmed.isEmpty then
    return
  if (trimmed.any (· == '\n')) && !(← get_state).inlineMode then
    -- ensure a fresh line, but do NOT add a blank if a newline is already
    -- pending (avoids splitting a `let`/expression body from its head).
    -- Emit at the CURRENT indent level (no extra nesting): a verbatim body
    -- must stay column-aligned with its enclosing let-chain / continuation,
    -- which some column-sensitive custom syntaxes require.
    modify_state fun state =>
      { state with pendingNewlines := Nat.max state.pendingNewlines 1, pendingSpace := false }
    emit_verbatim_str sTrim
  else emit_verbatim_str sTrim

/-- Reproduce a syntax node's original source text (never mangles unhandled
    constructs). Multi-line blocks start on a fresh, indented line and are
    re-anchored; single-line blocks are emitted inline. -/
def emit_verbatim (stx : Syntax) : emitter_m Unit := do

  -- Prefer reprint; fall back to the exact original source slice (reliable even
  -- when reprint is unavailable, e.g. some nodes after `updateLeading`).
  let src? : Option String :=
    match stx.reprint with
    | some textValue => some textValue
    | none           => (stx.getSubstring? true false).map (·.toString)
  match src? with
  | some source => emit_verbatim_source source
  | none => pure ()

def get_leading (stx : Syntax) : Option String :=
  match stx.getHeadInfo with
  | .original leading .. => some (Substring.Raw.toString leading)
  | _ => none

def has_comment (source : String) : Bool := source.toList.any (· == '-')
def count_newlines (source : String) : Nat := source.toList.filter (· == '\n') |>.length

end emitter_m

namespace Emitter

open emitter_m

def process_leading (stx : Syntax) : emitter_m Unit := do
  if let some leading := get_leading stx then
    if leading.isEmpty then
      return
    let state ← get_state
    -- In inline mode, don't process leading whitespace
    if state.inlineMode then
      return
    let atStart := state.output.isEmpty && state.pendingNewlines == 0
    let newlines := count_newlines leading
    if has_comment leading then
      -- trim BOTH ends: keep the comment text, drop surrounding whitespace so
      -- trailing newlines can't accumulate across reformat passes (idempotency)
      let trimmed := (leading.trimAscii).toString
      if !trimmed.isEmpty then
        -- Don't add blank lines at file start
        if !atStart then
          -- Only add newlines if we don't already have pending ones
          -- (or if trivia has MORE newlines than we have pending)
          if newlines > state.pendingNewlines then
            if newlines > 1 then blank_line
            else newline
        emit trimmed
        newline
    else
      -- Just whitespace — convert to newlines (but not at start, and not if already pending)
      if !atStart && state.pendingNewlines == 0 then
        if newlines > 1 then blank_line
        else if newlines > 0 then newline

/-- Check if a syntax kind is a binary operator (like «term_+_», «term_<_», etc.) -/
def is_bin_op (kind : SyntaxNodeKind) : Bool :=
  let spelling := kind.toString
  spelling.startsWith "«term_" && (spelling.toList.filter (· == '_')).length >= 2

/-- True if any token in the subtree carries a line comment (`-- …`) in its
    trivia. Such subtrees must never be inlined/flattened: the comment would
    swallow the rest of the line (e.g. an `else` branch or a match-arm body). -/
partial
def has_line_comment (stx : Syntax) : Bool :=
  let inTrivia (info : SourceInfo) : Bool :=
    match info with
    | .original leading _ trailing _ =>
      let leadingText := Substring.Raw.toString leading
      let trailingText := Substring.Raw.toString trailing
      (leadingText.splitOn "--").length > 1 || (trailingText.splitOn "--").length > 1
    | _ => false
  match stx with
  | .atom info _      => inTrivia info
  | .ident info _ _ _ => inTrivia info
  | .node info _ args => inTrivia info || args.any has_line_comment
  | .missing          => false

/-- Check if a syntax should be emitted inline (simple expressions without control flow) -/
partial
def is_simple_expr (stx : Syntax) : Bool :=
  if has_line_comment stx then
    false
  else
    match stx with
    | .missing => true
    | .atom _ _ => true
    | .ident _ _ _ _ => true
    | .node _ kind args =>
      -- Complex control flow / layout-sensitive - not simple (must not be inlined)
      if kind == ``Lean.Parser.Term.doIf || kind == ``Lean.Parser.Term.doMatch ||
         kind == ``Lean.Parser.Term.do || kind == ``Lean.Parser.Term.let ||
         kind == ``Lean.Parser.Term.doLet || kind == ``Lean.Parser.Term.doFor ||
         kind == ``Lean.Parser.Term.doSeqIndent || kind == ``Lean.Parser.Term.doSeqItem ||
         kind == ``Lean.Parser.Term.byTactic || kind == ``Lean.Parser.Term.have ||
         kind == ``Lean.Parser.Term.show || kind == ``Lean.Parser.Term.suffices ||
         kind == ``Lean.Parser.Term.letrec then false
      -- Match is only simple if it has few arms and simple bodies
      else if kind == ``Lean.Parser.Term.match then
        -- Allow simple matches (<=3 arms with simple bodies)
        if args.size > 0 then
          let altsOpt := args.back?
          match altsOpt with
          | some alts =>
            let altsArr := alts.getArgs
            altsArr.size <= 3 && altsArr.all fun alt =>
              let altArgs := alt.getArgs
              altArgs.size > 3 && is_simple_expr altArgs[3]!
          | none => false
        else false
      -- Other nodes are simple if all children are simple
      else args.all is_simple_expr

private
inductive NodeDispatch where
  | handled
  | unhandled
  deriving Inhabited

private
abbrev NodeHandler := Syntax → SyntaxNodeKind → Array Syntax → emitter_m NodeDispatch

mutual

partial
def emit_syntax (stx : Syntax) : emitter_m Unit := do
  match stx with
  | .missing => pure ()
  | .atom _info val => emitAtom stx val
  | .ident _info _rawVal name _ => emitIdent stx name
  | .node _info kind args => emitNode stx kind args

private partial
def emitAtom (stx : Syntax) (value : String) : emitter_m Unit := do
    process_leading stx
    emit value

private partial
def emitIdent (stx : Syntax) (name : Name) : emitter_m Unit := do
    process_leading stx
    emit name.toString

private partial
def dispatchNodeTop
    (stx : Syntax)
    (kind : SyntaxNodeKind)
    (args : Array Syntax)
    : emitter_m NodeDispatch := do
  let inlineProne :=
    kind == ``Lean.Parser.Term.app || kind == ``Lean.Parser.Term.anonymousCtor
      || kind == ``Lean.Parser.Term.match || kind == ``Lean.Parser.Term.structInst
      || kind.toString == "«term[_]»" || kind.toString == "«term{_}»"
  if inlineProne && has_line_comment stx then emit_verbatim stx; return .handled
  if is_bin_op kind && args.size == 3 then emitBinOp args; return .handled
  if kind == ``Lean.Parser.Module.module then emitModule args; return .handled
  if kind == ``Lean.Parser.Module.header then emitHeader args; return .handled
  if kind == ``Lean.Parser.Module.import then emitImport args; return .handled
  if kind == ``Lean.Parser.Command.open then emitOpen args; return .handled
  if kind == ``Lean.Parser.Command.namespace then emitNamespace args; return .handled
  if kind == ``Lean.Parser.Command.end then emitEnd args; return .handled
  return .unhandled

private partial
def dispatchNodeDeclaration
    (_stx : Syntax)
    (kind : SyntaxNodeKind)
    (args : Array Syntax)
    : emitter_m NodeDispatch := do
  if kind == ``Lean.Parser.Command.declaration then emitDeclaration args; return .handled
  if kind == ``Lean.Parser.Command.declModifiers then emitDeclModifiers args; return .handled
  if kind == ``Lean.Parser.Command.partial then emitModifierKeyword "partial" args; return .handled
  if kind == ``Lean.Parser.Command.noncomputable then
    emitModifierKeyword "noncomputable" args; return .handled
  if kind == ``Lean.Parser.Command.unsafe then emitModifierKeyword "unsafe" args; return .handled
  if kind == ``Lean.Parser.Command.private then emitModifierKeyword "private" args; return .handled
  if kind == ``Lean.Parser.Command.protected then
    emitModifierKeyword "protected" args; return .handled
  if kind == ``Lean.Parser.Command.opaque then emitKeywordDecl "opaque" args; return .handled
  if kind == ``Lean.Parser.Command.axiom then emitKeywordDecl "axiom" args; return .handled
  if kind == ``Lean.Parser.Command.definition then emitKeywordDecl "def" args; return .handled
  if kind == ``Lean.Parser.Command.theorem then emitKeywordDecl "theorem" args; return .handled
  if kind == ``Lean.Parser.Command.abbrev then emitKeywordDecl "abbrev" args; return .handled
  return .unhandled

private partial
def dispatchNodeStructure
    (stx : Syntax)
    (kind : SyntaxNodeKind)
    (args : Array Syntax)
    : emitter_m NodeDispatch := do
  if kind == ``Lean.Parser.Command.structure then emitStructure args; return .handled
  if kind == ``Lean.Parser.Command.inductive then emitInductive args; return .handled
  if kind == ``Lean.Parser.Command.structureTk then emit_syntax args[0]!; return .handled
  if kind == ``Lean.Parser.Command.ctor then emitCtor args; return .handled
  if kind == ``Lean.Parser.Command.structFields then
    for arg in args do emit_syntax arg
    return .handled
  if kind == ``Lean.Parser.Command.structSimpleBinder then emitStructField args; return .handled
  if kind == ``Lean.Parser.Command.optDeriving then emitDeriving args; return .handled
  if kind == ``Lean.Parser.Command.derivingClass then emitDerivingClass args; return .handled
  return .unhandled

private partial
def dispatchNodeInstance
    (stx : Syntax)
    (kind : SyntaxNodeKind)
    (args : Array Syntax)
    : emitter_m NodeDispatch := do
  if kind == ``Lean.Parser.Command.instance then emitInstance args; return .handled
  if kind == ``Lean.Parser.Command.whereStructInst then space; emit_verbatim stx; return .handled
  if kind == ``Lean.Parser.Term.structInstFields then
    for arg in args do emit_syntax arg
    return .handled
  if kind == ``Lean.Parser.Term.structInstField then emitStructInstField args; return .handled
  if kind == ``Lean.Parser.Term.structInstLVal then emitStructInstLVal args; return .handled
  if kind == ``Lean.Parser.Term.structInstFieldDef then emitStructInstFieldDef args; return .handled
  return .unhandled

private partial
def dispatchNodeSignature
    (stx : Syntax)
    (kind : SyntaxNodeKind)
    (args : Array Syntax)
    : emitter_m NodeDispatch := do
  if kind == ``Lean.Parser.Command.declValSimple then emitDeclValSimple args; return .handled
  if kind == ``Lean.Parser.Command.declValEqns then emit_verbatim stx; return .handled
  if kind == ``Lean.Parser.Term.binderDefault then emitBinderDefault args; return .handled
  if kind == ``Lean.Parser.Command.declSig
      || kind == ``Lean.Parser.Command.optDeclSig then emitDeclSig args; return .handled
  if kind == ``Lean.Parser.Command.declId then emitDeclId args; return .handled
  if kind == ``Lean.Parser.Command.docComment then emitDocComment args; return .handled
  if kind == ``Lean.Parser.Term.attributes then emitAttributes args; return .handled
  if kind == ``Lean.Parser.Term.typeSpec then emitTypeSpec args; return .handled
  if kind == ``Lean.Parser.Term.explicitBinder then emitExplicitBinder args; return .handled
  if kind == ``Lean.Parser.Term.implicitBinder then emitImplicitBinder args; return .handled
  return .unhandled

private partial
def dispatchNodeTerm
    (stx : Syntax)
    (kind : SyntaxNodeKind)
    (args : Array Syntax)
    : emitter_m NodeDispatch := do
  if kind == ``Lean.Parser.Term.app then emitApp stx args; return .handled
  if kind == ``Lean.Parser.Term.anonymousCtor then emitAnonCtor args; return .handled
  if kind == ``Lean.Parser.Term.forall then emitForall args; return .handled
  if kind == ``Lean.Parser.Term.arrow then emitArrow args; return .handled
  if kind.toString == "«term∃_,_»" then emitExists args; return .handled
  if kind == ``Lean.Parser.Term.match then emitMatch args; return .handled
  if kind == ``Lean.Parser.Term.doMatch then emitDoMatch args; return .handled
  if kind == ``Lean.Parser.Term.matchAlt then emitMatchAlt args; return .handled
  if kind == ``Lean.Parser.Term.matchAlts then emitMatchAlts args; return .handled
  if kind == ``Lean.Parser.Term.matchDiscr then emitMatchDiscr args; return .handled
  if kind == ``Lean.Parser.Term.paren then emitParen args; return .handled
  if kind == ``Lean.Parser.Term.dotIdent then emitDotIdent args; return .handled
  return .unhandled

private partial
def dispatchNodeStructural
    (_stx : Syntax)
    (kind : SyntaxNodeKind)
    (args : Array Syntax)
    : emitter_m NodeDispatch := do
  if kind == ``Lean.Parser.Term.pipeProj then emitPipeProj args; return .handled
  if kind == ``Lean.Parser.Term.structInst then emitStructInst args; return .handled
  if kind == ``Lean.Parser.Term.proj then emitProj args; return .handled
  if kind == ``Lean.Parser.Term.cdot then emit "·"; return .handled
  if kind == `hygieneInfo then return .handled
  if kind == ``Lean.Parser.Term.hygienicLParen then emit "("; return .handled
  if kind == ``Lean.Parser.Term.fun then emitFun args; return .handled
  if kind == ``Lean.Parser.Term.basicFun then emitBasicFun args; return .handled
  return .unhandled

private partial
def dispatchNodeDo
    (_stx : Syntax)
    (kind : SyntaxNodeKind)
    (args : Array Syntax)
    : emitter_m NodeDispatch := do
  if kind == ``Lean.Parser.Term.do then emitDo args; return .handled
  if kind == ``Lean.Parser.Term.doSeqBracketed then emitDoSeqBracketed args; return .handled
  if kind == ``Lean.Parser.Term.doSeqIndent then emitDoSeqIndent args; return .handled
  if kind == ``Lean.Parser.Term.doSeqItem then emitDoSeqItem args; return .handled
  if kind == ``Lean.Parser.Term.doLetArrow then emitDoLetArrow args; return .handled
  if kind == ``Lean.Parser.Term.doReturn then emitDoReturn args; return .handled
  if kind == ``Lean.Parser.Term.doFor then emitDoFor args; return .handled
  if kind == ``Lean.Parser.Term.doExpr then emitDoExpr args; return .handled
  return .unhandled

private partial
def dispatchNodeControl
    (stx : Syntax)
    (kind : SyntaxNodeKind)
    (args : Array Syntax)
    : emitter_m NodeDispatch := do
  if kind == ``Lean.Parser.Term.let then emitLet args; return .handled
  if kind == ``Lean.Parser.Term.doLet then emitDoLet args; return .handled
  if kind == ``Lean.Parser.Term.letDecl then emitLetDecl args; return .handled
  if kind == ``Lean.Parser.Term.letIdDecl then emitLetIdDecl args; return .handled
  if kind == ``Lean.Parser.Term.letId then emitLetId args; return .handled
  if kind == ``Lean.Parser.Term.letConfig then return .handled
  return .unhandled

private partial
def dispatchNodeConditional
    (stx : Syntax)
    (kind : SyntaxNodeKind)
    (args : Array Syntax)
    : emitter_m NodeDispatch := do
  if kind == ``Lean.Parser.Term.doIf then emitDoIf args; return .handled
  if kind == ``Lean.Parser.Term.doIfProp then emitDoIfProp args; return .handled
  if kind == ``Lean.Parser.Term.doIfLet then emitDoIfLet args; return .handled
  if kind == ``Lean.Parser.Term.doIfLetPure then emitDoIfLetPure args; return .handled
  if kind.toString == "termIfThenElse" then
    if has_line_comment stx then emit_verbatim stx else emitTermIf args
    return .handled
  if kind == `group then emitGroup args; return .handled
  return .unhandled

private partial
def dispatchNodeLiteral
    (_stx : Syntax)
    (kind : SyntaxNodeKind)
    (args : Array Syntax)
    : emitter_m NodeDispatch := do
  if kind == `str then emitStr args; return .handled
  if kind.toString == "termS!_" then emitSInterp args; return .handled
  if kind == `interpolatedStrKind then emitInterpStr args; return .handled
  if kind == `interpolatedStrLitKind then
    for arg in args do emit_syntax arg
    return .handled
  return .unhandled

private partial
def dispatchNodeCollection
    (_stx : Syntax)
    (kind : SyntaxNodeKind)
    (args : Array Syntax)
    : emitter_m NodeDispatch := do
  if kind.toString == "«term[_]»" then emitListLit args; return .handled
  if kind.toString == "«term_[_]»" then emitIndexAccess args; return .handled
  if kind.toString == "«term_[_]!»" then emitIndexBang args; return .handled
  if kind.toString == "«term_[_]?»" then emitIndexQuestion args; return .handled
  if kind.toString == "«term{_}»" then emitAnonStruct args; return .handled
  if kind == ``Lean.Parser.Term.hole then emit "_"; return .handled
  if kind == `choice then
    if h : 0 < args.size then emit_syntax args[0]!
    return .handled
  if kind == `null then
    for arg in args do emit_syntax arg
    return .handled
  return .unhandled

private partial
def emitNode (stx : Syntax) (kind : SyntaxNodeKind) (args : Array Syntax) : emitter_m Unit := do
    let handlers : List NodeHandler :=
      [
        dispatchNodeTop,
        dispatchNodeDeclaration,
        dispatchNodeStructure,
        dispatchNodeInstance,
        dispatchNodeSignature,
        dispatchNodeTerm,
        dispatchNodeStructural,
        dispatchNodeDo,
        dispatchNodeControl,
        dispatchNodeConditional,
        dispatchNodeLiteral,
        dispatchNodeCollection
      ]
    routeNode handlers stx kind args

private partial
def routeNode
    (handlers : List NodeHandler)
    (stx : Syntax)
    (kind : SyntaxNodeKind)
    (args : Array Syntax)
    : emitter_m Unit := do
  let some handler := handlers.head? | return (← emit_verbatim stx)
  match ← handler stx kind args with
  | .handled => pure ()
  | .unhandled => routeNode handlers.tail stx kind args

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Binary operators
  -- ─────────────────────────────────────────────────────────────────────────────

private partial
def emitBinOp (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = left, args[1] = operator atom, args[2] = right
    emit_syntax args[0]!
    space
    emit_syntax args[1]!
    space
    emit_syntax args[2]!

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Top-level
  -- ─────────────────────────────────────────────────────────────────────────────

private partial
def emitModule (args : Array Syntax) : emitter_m Unit := do
    if h : 0 < args.size then emit_syntax args[0]
    if h : 1 < args.size then for cmd in args[1].getArgs do emit_syntax cmd; newline

private partial
def emitHeader (args : Array Syntax) : emitter_m Unit := do
    for arg in args do emit_syntax arg

private partial
def emitImport (args : Array Syntax) : emitter_m Unit := do
    -- Module.import = [_, _, ATOM "import", _, IDENT path, _] (plus optional modifiers)
    let mut firstAtom := true
    for argument in args do
      match argument with
      | .atom _ value => firstAtom ← emitImportAtom firstAtom argument value
      | .ident .. => emitImportIdent argument
      | _ => pure ()  -- skip empty null modifier slots
    newline

private partial
def emitImportIdent (stx : Syntax) : emitter_m Unit := do
    space
    emit_syntax stx

private partial
def emitImportAtom (firstAtom : Bool) (stx : Syntax) (value : String) : emitter_m Bool := do
    if firstAtom then process_leading stx else space
    emit value
    return false

private partial
def emitOpen (args : Array Syntax) : emitter_m Unit := do
    -- Command.open = [ATOM "open", openSimple | openOnly | openHiding | ...]
    if h : 0 < args.size then process_leading args[0]!
    emit "open"
    for idx in [1:args.size] do
      let argument := args[idx]!
      if argument.getKind == ``Lean.Parser.Command.openSimple then
        -- null node of namespace idents; space-separate them
        for sub in argument.getArgs do
          for identifier in sub.getArgs do space; emit_syntax identifier
      else if !argument.isNone then
        space; emit_syntax argument
    newline

private partial
def emitNamespace (args : Array Syntax) : emitter_m Unit := do
    process_leading args[0]!; emit "namespace"; space; emit_syntax args[1]!; newline; blank_line

private partial
def emitEnd (args : Array Syntax) : emitter_m Unit := do
    blank_line; process_leading args[0]!; emit "end"
    if args.size > 1 then
      let argument := args[1]!
      if !argument.isNone then space; emit_syntax argument
    newline

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Declarations
  -- ─────────────────────────────────────────────────────────────────────────────

private partial
def emitDeclaration (args : Array Syntax) : emitter_m Unit := do
    if h : 0 < args.size then emit_syntax args[0]
    if h : 1 < args.size then emit_syntax args[1]

private partial
def emitDeclModifiers (args : Array Syntax) : emitter_m Unit := do
    for arg in args do if !arg.isNone then emit_syntax arg

private partial
def emitModifierKeyword (keyword : String) (_args : Array Syntax) : emitter_m Unit := do
    emit keyword
    space

private partial
def emitKeywordDecl (keyword : String) (args : Array Syntax) : emitter_m Unit := do
    process_leading args[0]!; emit keyword; space
    for idx in [1:args.size] do emit_syntax args[idx]!

private partial
def emitDocComment (args : Array Syntax) : emitter_m Unit := do
    process_leading args[0]!; emit "/--"
    if h : 1 < args.size then
      match args[1]! with
      | .atom _ value => emitDocText value
      | other => emit_syntax other
    newline

private partial
def emitDocText (value : String) : emitter_m Unit := do
    if value.length > 0 then
      let first := value.toList.head!
      if first != ' ' && first != '\n' then emit " "
    emit value

private partial
def emitAttributes (args : Array Syntax) : emitter_m Unit := do
    process_leading args[0]!; emit "@["
    if h : 1 < args.size then
      let attrs := args[1]!.getArgs
      for idx in [:attrs.size] do
        if idx > 0 then emit ", "
        emitAttrInstance attrs[idx]!
    emit "]"; newline

private partial
def emitAttrInstance (stx : Syntax) : emitter_m Unit := do
    let args := stx.getArgs
    if h : 1 < args.size then emitAttr args[1]!

private partial
def emitAttr (stx : Syntax) : emitter_m Unit := do
    match stx with
    | .node _ kind args =>
      if kind == ``Lean.Parser.Attr.extern then
        emit "extern"
        if h : 1 < args.size then for entry in args[1]!.getArgs do emitExternEntry entry
      else for arg in args do emit_syntax arg
    | other => emit_syntax other

private partial
def emitExternEntry (stx : Syntax) : emitter_m Unit := do
    let args := stx.getArgs
    if h : 2 < args.size then space; emit_syntax args[2]!

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Signatures
  -- ─────────────────────────────────────────────────────────────────────────────

private partial
def emitDeclId (args : Array Syntax) : emitter_m Unit := do
    if h : 0 < args.size then emit_syntax args[0]
    if h : 1 < args.size then
      let argument := args[1]!
      if !argument.isNone then emit_syntax argument

private partial
def emitDeclSig (args : Array Syntax) : emitter_m Unit := do
    if h : 0 < args.size then for binder in args[0]!.getArgs do space; emit_syntax binder
    if h : 1 < args.size then space; emit_syntax args[1]

private partial
def emitTypeSpec (args : Array Syntax) : emitter_m Unit := do
    emit ":"; space
    if h : 1 < args.size then emit_syntax args[1]

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Binders
  -- ─────────────────────────────────────────────────────────────────────────────

private partial
def emitExplicitBinder (args : Array Syntax) : emitter_m Unit := do
    -- args[0]="(", args[1]=names, args[2]=type?, args[3]=default?, args[4]=")"
    emit "("
    if h : 1 < args.size then
      let names := args[1]!.getArgs
      for idx in [:names.size] do
        if idx > 0 then space
        emit_syntax names[idx]!
    if h : 2 < args.size then
      let typeAsc := args[2]!
      if !typeAsc.isNone then
        -- Type ascription is null node with [":"] [Type]
        let typeArgs := typeAsc.getArgs
        if typeArgs.size >= 2 then
          space
          emit ":"
          space
          emit_syntax typeArgs[1]!
    -- Default value (binderDefault)
    if h : 3 < args.size then
      let defaultNode := args[3]!
      if !defaultNode.isNone then
        emit_syntax defaultNode
    emit ")"

private partial
def emitImplicitBinder (args : Array Syntax) : emitter_m Unit := do
    emit "{"
    if h : 1 < args.size then
      let names := args[1]!.getArgs
      for idx in [:names.size] do
        if idx > 0 then space
        emit_syntax names[idx]!
    if h : 2 < args.size then
      let typeAsc := args[2]!
      if !typeAsc.isNone then
        let typeArgs := typeAsc.getArgs
        if typeArgs.size >= 2 then
          space
          emit ":"
          space
          emit_syntax typeArgs[1]!
    emit "}"

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Terms
  -- ─────────────────────────────────────────────────────────────────────────────

private partial
def emitApp (stx : Syntax) (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = fn, args[1] = null of argument terms
    let function := if h : 0 < args.size then args[0]! else Syntax.missing
    let argList := if h : 1 < args.size then args[1]!.getArgs else #[]
    -- If every part is simple, flatten to a single line (suppressing any stray
    -- source newlines). Otherwise reproduce verbatim so a complex argument's
    -- own layout (do/match/tactic) is preserved and never mangled.
    if is_simple_expr function && argList.all is_simple_expr then
      with_inline do
        emit_syntax function
        for arg in argList do space; emit_syntax arg
    else
      emit_verbatim stx

private partial
def emitAnonCtor (args : Array Syntax) : emitter_m Unit := do
    emit "⟨"
    if h : 1 < args.size then
      let vals := args[1]!.getArgs
      let mut first := true
      for value in vals do
        if value.isAtom then continue  -- skip existing comma separators
        if !first then emit ", "
        first := false
        emit_syntax value
    emit "⟩"

private partial
def emitForall (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "∀", args[1] = binders (null), args[2] = type? (null), args[3] = ",", args[4] = body
    emit "∀"
    space
    -- Emit binders (space-separated)
    if h : 1 < args.size then
      let binders := args[1]!.getArgs
      for idx in [:binders.size] do
        if idx > 0 then space
        emit_syntax binders[idx]!
    -- Type ascription if present (skip empty null)
    if h : 2 < args.size then
      let typeAsc := args[2]!
      if typeAsc.getArgs.size > 0 then
        space
        emit_syntax typeAsc
    emit ","
    space
    -- Body is args[4] when comma is args[3]
    if args.size > 4 then
      emit_syntax args[4]!

private partial
def emitArrow (args : Array Syntax) : emitter_m Unit := do
    -- A → B: args[0] = A, args[1] = "→", args[2] = B
    if h : 0 < args.size then emit_syntax args[0]
    space
    emit "→"
    space
    if h : 2 < args.size then emit_syntax args[2]!

private partial
def emitExists (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "∃", args[1] = binders, args[2] = ",", args[3] = body
    emit "∃"
    space
    if h : 1 < args.size then emit_syntax args[1]!
    emit ","
    space
    if h : 3 < args.size then emit_syntax args[3]!

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Structure and Inductive
  -- ─────────────────────────────────────────────────────────────────────────────

private partial
def emitStructure (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = structureTk, args[1] = declId, args[2] = optDeclSig,
    -- args[3] = extends?, args[4] = whereBody?, args[5] = optDeriving
    process_leading args[0]!
    -- emit the actual keyword (`structure` OR `class` — never hardcode)
    let keyword := (args[0]!.getArgs.findSome? fun child =>
      match child with | .atom _ value => some value | _ => none).getD "structure"
    emit keyword
    space
    if h : 1 < args.size then emit_syntax args[1]!  -- name
    if h : 2 < args.size then emit_syntax args[2]!  -- optDeclSig
    -- args[3] is extends (often empty)
    if h : 3 < args.size then
      let extension := args[3]!
      if !extension.isNone then emit_syntax extension
    -- args[4] is where body
    if h : 4 < args.size then
      let whereBody := args[4]!
      if !whereBody.isNone then
        let whereArgs := whereBody.getArgs
        if whereArgs.size > 0 then
          space
          emit "where"
          newline
          -- Fields are in whereArgs[2] (structFields)
          if whereArgs.size > 2 then
            emit_syntax whereArgs[2]!
          -- args[5] is deriving - emit indented
          if h : 5 < args.size then
            emit "  "
            emit_syntax args[5]!
    blank_line

private partial
def emitInductive (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "inductive", args[1] = declId, args[2] = optDeclSig,
    -- args[3] = where?, args[4] = ctors, args[5..] = other
    process_leading args[0]!
    emit "inductive"
    space
    if h : 1 < args.size then emit_syntax args[1]!  -- name
    if h : 2 < args.size then emit_syntax args[2]!  -- optDeclSig
    -- where
    if h : 3 < args.size then
      let whereOpt := args[3]!
      if !whereOpt.isNone then
        space
        emit "where"
        newline
    -- constructors
    if h : 4 < args.size then
      for ctor in args[4]!.getArgs do
        emit_syntax ctor
        newline
    -- deriving (args[5] or later) - indented
    if h : 5 < args.size then
      emit "  "
      for idx in [5:args.size] do emit_syntax args[idx]!
    blank_line

private partial
def emitCtor (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = docComment?, args[1] = "|", args[2] = modifiers, args[3] = name, args[4] = sig
    -- Don't process leading - we control inductive ctor layout
    emit "  | "
    -- Emit name without triggering processLeading
    if h : 3 < args.size then
      let nameNode := args[3]!
      if let .ident _ _ name _ := nameNode then
        emit name.toString
    if h : 4 < args.size then emit_syntax args[4]!  -- sig

private partial
def emitStructField (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = modifiers (with docComment), args[1] = name, args[2] = optDeclSig, args[3] = default?
    -- Emit doc comment from modifiers (if present)
    if h : 0 < args.size then
      let mods := args[0]!
      if mods.getArgs.size > 0 then
        let docOpt := mods.getArgs[0]!  -- null node containing docComment
        if !docOpt.isNone && docOpt.getArgs.size > 0 then
          -- docOpt.getArgs[0] is the actual docComment
          let docComment := docOpt.getArgs[0]!
          let docArgs := docComment.getArgs
          if docArgs.size >= 2 then
            emit "  /--"
            match docArgs[1]! with
            | .atom _ value => emitDocText value
            | other => emit_syntax other
            newline
    -- Emit field name without triggering processLeading
    emit "  "  -- indent
    if h : 1 < args.size then
      let nameNode := args[1]!
      if let .ident _ _ name _ := nameNode then
        emit name.toString
    -- Emit type
    if h : 2 < args.size then emit_syntax args[2]!
    -- Emit default
    if h : 3 < args.size then
      let default := args[3]!
      if !default.isNone then emit_syntax default
    newline

private partial
def emitDeriving (args : Array Syntax) : emitter_m Unit := do
    -- args[0] is null containing [deriving, classes]
    if args.size > 0 then
      let inner := args[0]!.getArgs
      if inner.size >= 2 then
        -- Don't use processLeading - we control the formatting
        emit "deriving"
        space
        -- inner[1] has the classes
        let classes := inner[1]!.getArgs
        for idx in [:classes.size] do
          let cls := classes[idx]!
          if cls.isAtom then emit ", "  -- comma separator
          else emit_syntax cls
        newline

private partial
def emitDerivingClass (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = optional stuff, args[1] = class name
    if h : 1 < args.size then emit_syntax args[1]!

private partial
def emitInstance (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = attrKind, args[1] = "instance", args[2] = priority?, args[3] = name?,
    -- args[4] = sig, args[5] = whereStructInst
    if args.size > 1 then process_leading args[1]!
    emit "instance"
    -- Emit sig (typeSpec)
    if h : 4 < args.size then emit_syntax args[4]!
    -- Emit where body
    if h : 5 < args.size then emit_syntax args[5]!
    blank_line

private partial
def emitStructInstField (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = structInstLVal (field name), args[1] = null with [binders?, type?, fieldDef]
    emit "  "  -- indent
    -- Emit field name without processing leading (we control layout)
    if h : 0 < args.size then
      let lval := args[0]!
      -- structInstLVal: args[0] = ident, args[1] = suffix?
      if lval.getArgs.size > 0 then
        let fieldName := lval.getArgs[0]!
        if let .ident _ _ name _ := fieldName then
          emit name.toString
    if h : 1 < args.size then
      let rest := args[1]!.getArgs
      -- rest[0] = binders (null with idents), rest[1] = type?, rest[2] = fieldDef
      if rest.size > 0 then
        let binders := rest[0]!
        if !binders.isNone then
          for binder in binders.getArgs do
            space
            if let .ident _ _ name _ := binder then emit name.toString
            else emit_syntax binder
      if rest.size > 2 then
        emit_syntax rest[2]!  -- fieldDef
    newline

private partial
def emitStructInstLVal (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = ident, args[1] = suffix?
    if h : 0 < args.size then emit_syntax args[0]!

private partial
def emitStructInstFieldDef (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = ":=", args[1] = optional, args[2] = value
    space
    emit ":="
    space
    if h : 2 < args.size then emit_syntax args[2]!

private partial
def emitDeclValSimple (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = ":=", args[1] = body, args[2] = termination?, args[3] = where?
    space
    emit ":="
    space
    if h : 1 < args.size then emit_syntax args[1]!
    -- termination_by / decreasing_by suffix (verbatim, indentation-sensitive)
    if h : 2 < args.size then
      let termination := args[2]!
      if !termination.isNone && !(termination.reprint.getD "").trimAscii.toString.isEmpty then
        space
        emit_verbatim termination
    -- where clause (verbatim, indentation-sensitive)
    if h : 3 < args.size then
      let whereClause := args[3]!
      if !whereClause.isNone && !(whereClause.reprint.getD "").trimAscii.toString.isEmpty then
        space
        emit_verbatim whereClause

private partial
def emitDeclValEqns (args : Array Syntax) : emitter_m Unit := do
    -- equation-style body: `| pat => e | pat => e`
    -- args[0] = matchAltsWhereDecls ([matchAlts, termination, where?])
    newline
    indent
    for arg in args do emit_syntax arg
    dedent

private partial
def emitBinderDefault (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = ":=", args[1] = value
    space
    emit ":="
    space
    if h : 1 < args.size then emit_syntax args[1]!

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Match
  -- ─────────────────────────────────────────────────────────────────────────────

private partial
def emitMatch (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "match", args[1..] = opt stuff, scrutinees, "with", alts
    process_leading args[0]!
    emit "match"
    space
    -- Emit scrutinees and alts
    let state ← get_state
    for idx in [1:args.size] do
      let arg := args[idx]!
      if arg.isAtom then
        if let .atom _ val := arg then
          if val == "with" then
            space
            emit "with"
            if state.inlineMode then space else newline
      else if !arg.isNone then emit_syntax arg

private partial
def emitDoMatch (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "match", args[1..] = opt stuff, scrutinees, "with", alts
    emit "match"
    space
    let state ← get_state
    -- Skip the opt null nodes, find the discriminant and alts
    for idx in [1:args.size] do
      let arg := args[idx]!
      if arg.isAtom then
        if let .atom _ val := arg then
          if val == "with" then
            space
            emit "with"
            if state.inlineMode then space else newline
      else if !arg.isNone then emit_syntax arg

private partial
def emitMatchDiscr (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = opt h:, args[1] = expr
    if h : 1 < args.size then emit_syntax args[1]!

private partial
def emitMatchAlts (args : Array Syntax) : emitter_m Unit := do
    -- args is typically a single null node containing the alts
    let state ← get_state
    for arg in args do
      match arg with
      | .node _ _ alts => emitMatchAltNodes state.inlineMode alts
      | _ => emit_syntax arg

private partial
def emitMatchAltNodes (inlineMode : Bool) (alts : Array Syntax) : emitter_m Unit := do
    let mut first := true
    for alt in alts do
      if !first && inlineMode then space
      first := false
      emit_syntax alt

private partial
def emitMatchAlt (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "|", args[1] = patterns, args[2] = "=>", args[3] = body
    -- Don't process leading - we control match arm layout
    emit "| "
    if h : 1 < args.size then with_inline (emit_syntax args[1]!)
    emit " => "
    -- Only inline simple expressions; complex ones get their own line
    if h : 3 < args.size then
      let body := args[3]!
      if is_simple_expr body then
        with_inline (emit_syntax body)
      else
        newline
        indent
        emit_syntax body
        dedent
    newline

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Parens and structural
  -- ─────────────────────────────────────────────────────────────────────────────

private partial
def emitParen (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "(", args[1] = content, args[2] = ")"
    emit "("
    if h : 1 < args.size then emit_syntax args[1]!
    emit ")"

private partial
def emitDotIdent (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = ".", args[1] = ident
    emit "."
    if h : 1 < args.size then emit_syntax args[1]!

private partial
def emitPipeProj (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = expr, args[1] = "|>." or "|>", args[2] = func, args[3..] = more
    if h : 0 < args.size then emit_syntax args[0]!
    space
    if h : 1 < args.size then emit_syntax args[1]!
    if h : 2 < args.size then emit_syntax args[2]!
    -- args[3] is often empty null, args[4] has actual args
    if h : 4 < args.size then
      for arg in args[4]!.getArgs do
        space
        emit_syntax arg

private partial
def emitStructInst (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "{", args[1] = opt(base with), args[2] = fields, args[3] = ellipsis?, args[4] = opt, args[5] = "}"
    emit "{ "
    -- Check for "base with"
    if h : 1 < args.size then
      let baseWith := args[1]!
      if !baseWith.isNone && baseWith.getArgs.size > 0 then
        -- args[1].getArgs[0] is null containing base, [1] is "with"
        let baseInner := baseWith.getArgs[0]!
        if !baseInner.isNone && baseInner.getArgs.size > 0 then
          emit_syntax baseInner.getArgs[0]!
          emit " with "
    -- Emit fields
    if h : 2 < args.size then
      let fieldsNode := args[2]!
      if fieldsNode.getArgs.size > 0 then
        let fields := fieldsNode.getArgs[0]!
        let fieldArr := fields.getArgs
        let mut first := true
        for field in fieldArr do
          -- Skip null separator nodes
          match field with
          | .node _ kind _ =>
            if kind == ``Lean.Parser.Term.structInstField then
              if !first then emit ", "
              first := false
              emitStructInstFieldInline field
          | _ => pure ()
    emit " }"

private partial
def emitStructInstFieldInline (stx : Syntax) : emitter_m Unit := do
    -- structInstField: args[0] = lval, args[1] = null with [binders?, type?, fieldDef]
    let args := stx.getArgs
    if h : 0 < args.size then
      let lval := args[0]!
      if lval.getArgs.size > 0 then
        let fieldName := lval.getArgs[0]!
        if let .ident _ _ name _ := fieldName then
          emit name.toString
    if h : 1 < args.size then
      let rest := args[1]!.getArgs
      if rest.size > 2 then
        -- fieldDef
        let fieldDef := rest[2]!
        emit_syntax fieldDef

private partial
def emitProj (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = expr, args[1] = ".", args[2] = field (ident or fieldIdx node)
    if h : 0 < args.size then emit_syntax args[0]!
    emit "."
    if h : 2 < args.size then
      let fieldNode := args[2]!
      match fieldNode with
      | .ident _ _ name _ => emit name.toString
      | .node _ kind fieldArgs =>
        -- fieldIdx: args[0] = number atom
        if kind.toString == "fieldIdx" && fieldArgs.size > 0 then
          emit_syntax fieldArgs[0]!
        else emit_syntax fieldNode
      | _ => emit_syntax fieldNode

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Fun (lambda)
  -- ─────────────────────────────────────────────────────────────────────────────

private partial
def emitFun (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "fun", args[1] = funBody
    process_leading args[0]!
    emit "fun"
    space
    if h : 1 < args.size then emit_syntax args[1]!

private partial
def emitBasicFun (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = binders (null), args[1] = type? (null), args[2] = "=>", args[3] = body
    -- Emit binders (idents, holes `_`, typed `(x : T)`, etc.) via emitSyntax
    if h : 0 < args.size then
      let binders := args[0]!.getArgs
      for idx in [:binders.size] do
        if idx > 0 then space
        emit_syntax binders[idx]!
    -- optional return-type ascription
    if h : 1 < args.size then
      let returnType := args[1]!
      if !returnType.isNone then space; emit_syntax returnType
    space
    emit "=>"
    space
    if h : 3 < args.size then emit_syntax args[3]!

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Do notation
  -- ─────────────────────────────────────────────────────────────────────────────

private partial
def emitDo (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "do", args[1] = doSeq
    process_leading args[0]!
    emit "do"
    newline
    indent
    if h : 1 < args.size then emit_syntax args[1]!
    dedent

private partial
def emitDoSeqBracketed (args : Array Syntax) : emitter_m Unit := do
    for arg in args do emit_syntax arg

private partial
def emitDoSeqIndent (args : Array Syntax) : emitter_m Unit := do
    for arg in args do emit_syntax arg

private partial
def emitDoSeqItem (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = content, args[1] = optional semicolon
    -- Indentation is handled by the emit function based on indentLevel
    if h : 0 < args.size then emit_syntax args[0]!
    newline

private partial
def emitDoLetArrow (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "let", args[1] = null, args[2] = letConfig, args[3] = doPatDecl
    emit "let"
    space
    -- doPatDecl: args[0] = pattern, args[1] = opt, args[2] = "←", args[3] = value
    if h : 3 < args.size then
      let patDecl := args[3]!
      let patArgs := patDecl.getArgs
      if patArgs.size > 0 then emit_syntax patArgs[0]!  -- pattern
      space
      emit "←"
      space
      if patArgs.size > 3 then emit_syntax patArgs[3]!  -- value (doExpr)

private partial
def emitDoReturn (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "return", args[1] = value (null containing expr)
    emit "return"
    space
    if h : 1 < args.size then
      for value in args[1]!.getArgs do emit_syntax value

private partial
def emitDoFor (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "for", args[1] = decls (null), args[2] = "do", args[3] = body
    emit "for"
    space
    if h : 1 < args.size then
      -- decls is null containing doForDecl nodes
      let decls := args[1]!
      for decl in decls.getArgs do
        emitDoForDecl decl
    space
    emit "do"
    newline
    indent
    if h : 3 < args.size then emit_syntax args[3]!
    dedent

private partial
def emitDoForDecl (stx : Syntax) : emitter_m Unit := do
    -- doForDecl: args[0] = opt h:, args[1] = pattern, args[2] = "in", args[3] = expr
    let args := stx.getArgs
    if h : 1 < args.size then emit_syntax args[1]!  -- pattern
    space
    emit "in"
    space
    if h : 3 < args.size then emit_syntax args[3]!  -- collection

private partial
def emitDoExpr (args : Array Syntax) : emitter_m Unit := do
    -- doExpr wraps an expression
    for arg in args do emit_syntax arg

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Let and If
  -- ─────────────────────────────────────────────────────────────────────────────

private partial
def emitLet (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "let", args[1] = letConfig, args[2] = letDecl, args[3] = null, args[4] = body
    process_leading args[0]!
    emit "let"
    space
    -- letDecl
    if h : 2 < args.size then emit_syntax args[2]!
    -- body (continuation): always on its own line. A newline here is safe —
    -- processLeading on the continuation no-ops when a newline is already
    -- pending, so this can't double, and it can't merge when the separating
    -- newline lived in the value's trailing trivia.
    if h : 4 < args.size then
      newline
      emit_syntax args[4]!

private partial
def emitDoLet (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "let", args[1] = opt "mut", args[2] = config, args[3] = letDecl
    emit "let"
    space
    -- optional `mut` modifier — must not be dropped (mutation depends on it)
    if h : 1 < args.size then
      let opt := args[1]!
      if !opt.isNone then emit_syntax opt; space
    if h : 3 < args.size then emit_syntax args[3]!

private partial
def emitLetDecl (args : Array Syntax) : emitter_m Unit := do
    for arg in args do emit_syntax arg

private partial
def emitLetIdDecl (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = letId (contains name), args[1] = binders?, args[2] = type?, args[3] = ":=", args[4] = value
    if h : 0 < args.size then emit_syntax args[0]!  -- letId
    -- binders
    if h : 1 < args.size then
      for binder in args[1]!.getArgs do space; emit_syntax binder
    -- type
    if h : 2 < args.size then
      let typeOpt := args[2]!
      if !typeOpt.isNone then space; emit_syntax typeOpt
    space
    emit ":="
    space
    if h : 4 < args.size then emit_syntax args[4]!

private partial
def emitLetId (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = ident
    if h : 0 < args.size then
      let nameNode := args[0]!
      if let .ident _ _ name _ := nameNode then
        emit name.toString

private partial
def emitDoIf (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "if", args[1] = condition (doIfProp or doIfLet), args[2] = "then", args[3] = thenBr
    -- args[4] = elseif/else chains, args[5] = final else
    emit "if"
    space
    if h : 1 < args.size then emit_syntax args[1]!  -- condition
    space
    emit "then"
    newline
    indent
    if h : 3 < args.size then emit_syntax args[3]!  -- then branch
    dedent
    -- Handle else-if chains
    if h : 4 < args.size then
      for elseif in args[4]!.getArgs do emit_syntax elseif
    -- Handle final else
    if h : 5 < args.size then
      let finalElse := args[5]!
      if !finalElse.isNone && finalElse.getArgs.size > 0 then
        emit "else"
        newline
        indent
        if finalElse.getArgs.size > 1 then
          emit_syntax finalElse.getArgs[1]!
        dedent

private partial
def emitDoIfProp (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = opt h:, args[1] = condition expr
    if h : 1 < args.size then emit_syntax args[1]!

private partial
def emitDoIfLet (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "let", args[1] = pattern, args[2] = ":="/"<-" and value
    emit "let"
    space
    if h : 1 < args.size then emit_syntax args[1]!
    if h : 2 < args.size then emit_syntax args[2]!

private partial
def emitDoIfLetPure (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = ":=", args[1] = value
    space
    emit ":="
    space
    if h : 1 < args.size then emit_syntax args[1]!

private partial
def emitTermIf (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "if", args[1] = cond, args[2] = "then", args[3] = thenBr, args[4] = "else", args[5] = elseBr
    emit "if"
    space
    if h : 1 < args.size then emit_syntax args[1]!
    space
    emit "then"
    space
    if h : 3 < args.size then emit_syntax args[3]!
    space
    emit "else"
    space
    if h : 5 < args.size then emit_syntax args[5]!

private partial
def emitGroup (args : Array Syntax) : emitter_m Unit := do
    -- This handles "else if" chains in doIf
    -- Structure: group [group ["else", "if"], condition, "then", body]
    if args.size >= 2 then
      let first := args[0]!
      match first with
      | .node _ _ firstArgs =>
        if firstArgs.size >= 2 then
          -- "else" "if" combo
          emit "else"
          space
          emit "if"
          space
      | _ => pure ()
    -- Emit condition (args[1]), then "then" (args[2]), then body (args[3])
    for idx in [1:args.size] do
      let arg := args[idx]!
      if arg.isAtom then
        if let .atom _ val := arg then
          if val == "then" then
            space
            emit "then"
            newline
            indent
      else
        emit_syntax arg
        -- After emitting the body (which is the doSeqIndent), dedent
        if idx == args.size - 1 then dedent

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Strings and literals
  -- ─────────────────────────────────────────────────────────────────────────────

private partial
def emitStr (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = the string literal atom
    if h : 0 < args.size then emit_syntax args[0]!

private partial
def emitSInterp (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "s!", args[1] = interpolatedStrKind
    emit "s!"
    if h : 1 < args.size then emit_syntax args[1]!

private partial
def emitInterpStr (args : Array Syntax) : emitter_m Unit := do
    -- Children are alternating string literals and expressions
    for arg in args do emit_syntax arg

private partial
def emitListLit (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "[", args[1] = items (null with elements and commas), args[2] = "]"
    emit "["
    if h : 1 < args.size then
      let items := args[1]!.getArgs
      let mut first := true
      for item in items do
        -- Skip comma atoms
        if item.isAtom then continue
        if !first then emit ", "
        first := false
        emit_syntax item
    emit "]"

private partial
def emitIndexAccess (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = array, args[1] = "[", args[2] = index, args[3] = "]"
    if h : 0 < args.size then emit_syntax args[0]!
    emit "["
    if h : 2 < args.size then emit_syntax args[2]!
    emit "]"

private partial
def emitIndexBang (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = array, args[1] = "[", args[2] = index, args[3] = "]!"
    if h : 0 < args.size then emit_syntax args[0]!
    emit "["
    if h : 2 < args.size then emit_syntax args[2]!
    emit "]!"

private partial
def emitIndexQuestion (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = array, args[1] = "[", args[2] = index, args[3] = "]?"
    if h : 0 < args.size then emit_syntax args[0]!
    emit "["
    if h : 2 < args.size then emit_syntax args[2]!
    emit "]?"

private partial
def emitAnonStruct (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "{", args[1] = items (null with elements and commas), args[2] = "}"
    emit "{ "
    if h : 1 < args.size then
      let items := args[1]!.getArgs
      let mut first := true
      for item in items do
        -- Skip comma atoms
        if item.isAtom then continue
        if !first then emit ", "
        first := false
        emit_syntax item
    emit " }"

end

end Emitter

def format (stx : Syntax) (config : style_config := {}) : String × Array Diagnostic :=
  let ((), state) := emitter_m.run Unit config (Emitter.emit_syntax stx)
  let output :=
    if config.trailingNewline && !state.output.endsWith "\n" then
      state.output ++ "\n"
    else
      state.output
  (output, state.lints)

end Lean4Fmt
