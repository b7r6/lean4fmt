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

def run (α : Type) (config : style_config) (m : emitter_m α) : α × emitter_state :=
  StateT.run (ReaderT.run m config) {}

def get_config : emitter_m style_config := read
def get_state : emitter_m emitter_state := get
def modify_state (f : emitter_state → emitter_state) : emitter_m Unit := modify f

def emit (s : String) : emitter_m Unit := do
  if s.isEmpty then
    return
  let config ← get_config
  let st ← get_state
  let mut out := st.output
  let mut col := st.column
  for _ in [:st.pendingNewlines] do out := out.push '\n'; col := 0
  if col == 0 && st.indentLevel > 0 then
    let spaces := String.ofList (List.replicate (st.indentLevel * config.indent) ' ')
    out := out ++ spaces; col := spaces.length
  if st.pendingSpace && col > 0 then out := out.push ' '; col := col + 1
  out := out ++ s
  for c in s.toList do
    if c == '\n' then col := 0
    else col := col + 1
  set { st with output := out, column := col, pendingNewlines := 0, pendingSpace := false }

def newline : emitter_m Unit := do
  let st ← get_state
  if st.inlineMode then
    return -- suppress newlines in inline mode
  let config ← get_config
  modify_state fun st =>
    { st with
      pendingNewlines := min (st.pendingNewlines + 1) (config.maxBlankLines + 1),
      pendingSpace := false }

def blank_line : emitter_m Unit := do newline; newline
def space : emitter_m Unit := modify_state fun st => { st with pendingSpace := true }
def indent : emitter_m Unit := modify_state fun st => { st with indentLevel := st.indentLevel + 1 }
def dedent : emitter_m Unit := modify_state fun st => { st with indentLevel := st.indentLevel - 1 }

/-- Run an action in inline mode (suppresses newlines) -/
def with_inline {α : Type} (m : emitter_m α) : emitter_m α := do
  let oldInline := (← get_state).inlineMode
  modify_state fun st => { st with inlineMode := true }
  let result ← m
  modify_state fun st => { st with inlineMode := oldInline }
  return result

/-- Emit a block of pre-rendered source text, RE-ANCHORED to the current indent:
    the block's own minimum indentation becomes the current indent level, and
    internal relative indentation is preserved. This is what makes verbatim
    reproduction safe for indentation-sensitive constructs (tactic blocks,
    `let rec`, `where`) even when the surrounding signature has been reflowed. -/
def emit_verbatim_str (s : String) : emitter_m Unit := do
  let nonblank (l : String) : Bool := l.any (· != ' ')
  -- split; drop leading/trailing blank lines
  let mut ls := s.splitOn "\n"
  ls := ls.dropWhile (fun l => !nonblank l)
  ls := (ls.reverse.dropWhile (fun l => !nonblank l)).reverse
  if ls.isEmpty then
    return
  let indentOf (l : String) : Nat := (l.toList.takeWhile (· == ' ')).length
  let base := (ls.filter nonblank).foldl (fun m l => Nat.min m (indentOf l)) 1000000
  let base := if base == 1000000 then 0 else base
  let st ← get_state
  let mut first := true
  for l in ls do
    let ded := if l.length ≥ base then String.ofList (l.toList.drop base) else l
    if first then
      emit ded; first := false
    else if st.inlineMode then
      -- inline context: fold newlines into single spaces (best-effort)
      space; emit (ded.trimAsciiStart).toString
    else
      modify_state fun s => { s with pendingNewlines := s.pendingNewlines + 1, pendingSpace := false }
      emit ded

/-- Reproduce a syntax node's original source text (never mangles unhandled
    constructs). Multi-line blocks start on a fresh, indented line and are
    re-anchored; single-line blocks are emitted inline. -/
def emit_verbatim (stx : Syntax) : emitter_m Unit := do

  -- Prefer reprint; fall back to the exact original source slice (reliable even
  -- when reprint is unavailable, e.g. some nodes after `updateLeading`).
  let src? : Option String :=
    match stx.reprint with
    | some s => some s
    | none   => (stx.getSubstring? true false).map (·.toString)
  match src? with
  | some s =>
    -- Strip only trailing whitespace; KEEP the first line's leading indentation
    -- so `emitVerbatimStr`'s base-indent computation (and thus re-anchoring) is a
    -- fixed point across reformat passes. `t` (both ends) is only for the
    -- emptiness / multi-line tests.
    let sTrim := (s.trimAsciiEnd).toString
    let t := (s.trimAscii).toString
    if t.isEmpty then
      return
    if (t.any (· == '\n')) && !(← get_state).inlineMode then
      -- ensure a fresh line, but do NOT add a blank if a newline is already
      -- pending (avoids splitting a `let`/expression body from its head).
      -- Emit at the CURRENT indent level (no extra nesting): a verbatim body
      -- must stay column-aligned with its enclosing let-chain / continuation,
      -- which some column-sensitive custom syntaxes require.
      modify_state fun st =>
        { st with pendingNewlines := Nat.max st.pendingNewlines 1, pendingSpace := false }
      emit_verbatim_str sTrim
    else emit_verbatim_str sTrim
  | none => pure ()

def get_leading (stx : Syntax) : Option String :=
  match stx.getHeadInfo with
  | .original leading .. => some (Substring.Raw.toString leading)
  | _ => none

def has_comment (s : String) : Bool := s.toList.any (· == '-')
def count_newlines (s : String) : Nat := s.toList.filter (· == '\n') |>.length

end emitter_m

namespace Emitter

open emitter_m

def process_leading (stx : Syntax) : emitter_m Unit := do
  if let some leading := get_leading stx then
    if leading.isEmpty then
      return
    let st ← get_state
    -- In inline mode, don't process leading whitespace
    if st.inlineMode then
      return
    let atStart := st.output.isEmpty && st.pendingNewlines == 0
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
          if newlines > st.pendingNewlines then
            if newlines > 1 then blank_line
            else newline
        emit trimmed
        newline
    else
      -- Just whitespace — convert to newlines (but not at start, and not if already pending)
      if !atStart && st.pendingNewlines == 0 then
        if newlines > 1 then blank_line
        else if newlines > 0 then newline

/-- Check if a syntax kind is a binary operator (like «term_+_», «term_<_», etc.) -/
def is_bin_op (kind : SyntaxNodeKind) : Bool :=
  let s := kind.toString
  s.startsWith "«term_" && (s.toList.filter (· == '_')).length >= 2

/-- True if any token in the subtree carries a line comment (`-- …`) in its
    trivia. Such subtrees must never be inlined/flattened: the comment would
    swallow the rest of the line (e.g. an `else` branch or a match-arm body). -/
partial
def has_line_comment (stx : Syntax) : Bool :=
  let inTrivia (info : SourceInfo) : Bool :=
    match info with
    | .original l _ t _ =>
      let ls := Substring.Raw.toString l
      let ts := Substring.Raw.toString t
      (ls.splitOn "--").length > 1 || (ts.splitOn "--").length > 1
    | _ => false
  match stx with
  | .atom info _      => inTrivia info
  | .ident info _ _ _ => inTrivia info
  | .node info _ args => inTrivia info || args.any has_line_comment
  | .missing          => false

/-- Check if a syntax should be emitted inline (simple expressions without control flow) -/
partial
def is_simple_expr (stx : Syntax) : Bool :=
  if has_line_comment stx then false else
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

partial
def emit_syntax (stx : Syntax) : emitter_m Unit := do
  match stx with
  | .missing => pure ()
  | .atom _info val => process_leading stx; emit val
  | .ident _info _rawVal name _ => process_leading stx; emit name.toString
  | .node _info kind args => emitNode stx kind args

where
  emitNode (stx : Syntax) (kind : SyntaxNodeKind) (args : Array Syntax) : emitter_m Unit := do
    -- Inline-prone term containers that carry a line comment must be reproduced
    -- verbatim: flattening them would let the comment swallow following tokens
    -- (list/ctor elements, applied args, match arms).
    let inlineProne :=
      kind == ``Lean.Parser.Term.app || kind == ``Lean.Parser.Term.anonymousCtor ||
      kind == ``Lean.Parser.Term.match || kind == ``Lean.Parser.Term.structInst ||
      kind.toString == "«term[_]»" || kind.toString == "«term{_}»"
    if inlineProne && has_line_comment stx then emit_verbatim stx
    -- Check for binary operators first
    else if is_bin_op kind && args.size == 3 then
      emitBinOp args
    -- Top-level
    else if kind == ``Lean.Parser.Module.module then emitModule args
    else if kind == ``Lean.Parser.Module.header then emitHeader args
    else if kind == ``Lean.Parser.Module.import then emitImport args
    else if kind == ``Lean.Parser.Command.open then emitOpen args
    else if kind == ``Lean.Parser.Command.namespace then emitNamespace args
    else if kind == ``Lean.Parser.Command.end then emitEnd args
    -- Declarations
    else if kind == ``Lean.Parser.Command.declaration then emitDeclaration args
    else if kind == ``Lean.Parser.Command.declModifiers then emitDeclModifiers args
    else if kind == ``Lean.Parser.Command.partial then emitModifierKeyword "partial" args
    else if kind == ``Lean.Parser.Command.noncomputable then emitModifierKeyword "noncomputable" args
    else if kind == ``Lean.Parser.Command.unsafe then emitModifierKeyword "unsafe" args
    else if kind == ``Lean.Parser.Command.private then emitModifierKeyword "private" args
    else if kind == ``Lean.Parser.Command.protected then emitModifierKeyword "protected" args
    else if kind == ``Lean.Parser.Command.opaque then emitKeywordDecl "opaque" args
    else if kind == ``Lean.Parser.Command.axiom then emitKeywordDecl "axiom" args
    else if kind == ``Lean.Parser.Command.definition then emitKeywordDecl "def" args
    else if kind == ``Lean.Parser.Command.theorem then emitKeywordDecl "theorem" args
    else if kind == ``Lean.Parser.Command.abbrev then emitKeywordDecl "abbrev" args
    -- Structure and Inductive
    else if kind == ``Lean.Parser.Command.structure then emitStructure args
    else if kind == ``Lean.Parser.Command.inductive then emitInductive args
    else if kind == ``Lean.Parser.Command.structureTk then emit_syntax args[0]!  -- just "structure"
    else if kind == ``Lean.Parser.Command.ctor then emitCtor args
    else if kind == ``Lean.Parser.Command.structFields then for arg in args do emit_syntax arg
    else if kind == ``Lean.Parser.Command.structSimpleBinder then emitStructField args
    else if kind == ``Lean.Parser.Command.optDeriving then emitDeriving args
    else if kind == ``Lean.Parser.Command.derivingClass then emitDerivingClass args
    -- Instance
    else if kind == ``Lean.Parser.Command.instance then emitInstance args
    else if kind == ``Lean.Parser.Command.whereStructInst then space; emit_verbatim stx
    else if kind == ``Lean.Parser.Term.structInstFields then for arg in args do emit_syntax arg
    else if kind == ``Lean.Parser.Term.structInstField then emitStructInstField args
    else if kind == ``Lean.Parser.Term.structInstLVal then emitStructInstLVal args
    else if kind == ``Lean.Parser.Term.structInstFieldDef then emitStructInstFieldDef args
    -- Value bindings
    else if kind == ``Lean.Parser.Command.declValSimple then emitDeclValSimple args
    else if kind == ``Lean.Parser.Command.declValEqns then emit_verbatim stx
    else if kind == ``Lean.Parser.Term.binderDefault then emitBinderDefault args
    -- Signature parts
    else if kind == ``Lean.Parser.Command.declSig then emitDeclSig args
    else if kind == ``Lean.Parser.Command.optDeclSig then emitDeclSig args
    else if kind == ``Lean.Parser.Command.declId then emitDeclId args
    else if kind == ``Lean.Parser.Command.docComment then emitDocComment args
    else if kind == ``Lean.Parser.Term.attributes then emitAttributes args
    else if kind == ``Lean.Parser.Term.typeSpec then emitTypeSpec args
    -- Binders
    else if kind == ``Lean.Parser.Term.explicitBinder then emitExplicitBinder args
    else if kind == ``Lean.Parser.Term.implicitBinder then emitImplicitBinder args
    -- instBinder [Foo x] handled via verbatim fallback (spacing is subtle)
    -- Terms
    else if kind == ``Lean.Parser.Term.app then emitApp stx args
    else if kind == ``Lean.Parser.Term.anonymousCtor then emitAnonCtor args
    else if kind == ``Lean.Parser.Term.forall then emitForall args
    else if kind == ``Lean.Parser.Term.arrow then emitArrow args
    -- Existential: «term∃_,_»
    else if kind.toString == "«term∃_,_»" then emitExists args
    -- Match
    else if kind == ``Lean.Parser.Term.match then emitMatch args
    else if kind == ``Lean.Parser.Term.doMatch then emitDoMatch args
    else if kind == ``Lean.Parser.Term.matchAlt then emitMatchAlt args
    else if kind == ``Lean.Parser.Term.matchAlts then emitMatchAlts args
    else if kind == ``Lean.Parser.Term.matchDiscr then emitMatchDiscr args
    -- Parens and structural
    else if kind == ``Lean.Parser.Term.paren then emitParen args
    else if kind == ``Lean.Parser.Term.dotIdent then emitDotIdent args
    else if kind == ``Lean.Parser.Term.pipeProj then emitPipeProj args
    else if kind == ``Lean.Parser.Term.structInst then emitStructInst args
    else if kind == ``Lean.Parser.Term.proj then emitProj args
    else if kind == ``Lean.Parser.Term.cdot then emit "·"
    else if kind == `hygieneInfo then pure ()  -- skip hygiene info nodes
    else if kind == ``Lean.Parser.Term.hygienicLParen then emit "("  -- just emit the paren
    -- Fun (lambda)
    else if kind == ``Lean.Parser.Term.fun then emitFun args
    else if kind == ``Lean.Parser.Term.basicFun then emitBasicFun args
    -- Do notation
    else if kind == ``Lean.Parser.Term.do then emitDo args
    else if kind == ``Lean.Parser.Term.doSeqBracketed then emitDoSeqBracketed args
    else if kind == ``Lean.Parser.Term.doSeqIndent then emitDoSeqIndent args
    else if kind == ``Lean.Parser.Term.doSeqItem then emitDoSeqItem args
    else if kind == ``Lean.Parser.Term.doLetArrow then emitDoLetArrow args
    else if kind == ``Lean.Parser.Term.doReturn then emitDoReturn args
    else if kind == ``Lean.Parser.Term.doFor then emitDoFor args
    else if kind == ``Lean.Parser.Term.doExpr then emitDoExpr args
    -- Let and If
    else if kind == ``Lean.Parser.Term.let then emitLet args
    else if kind == ``Lean.Parser.Term.doLet then emitDoLet args
    else if kind == ``Lean.Parser.Term.letDecl then emitLetDecl args
    else if kind == ``Lean.Parser.Term.letIdDecl then emitLetIdDecl args
    else if kind == ``Lean.Parser.Term.letId then emitLetId args
    else if kind == ``Lean.Parser.Term.letConfig then pure ()  -- skip config
    else if kind == ``Lean.Parser.Term.doIf then emitDoIf args
    else if kind == ``Lean.Parser.Term.doIfProp then emitDoIfProp args
    else if kind == ``Lean.Parser.Term.doIfLet then emitDoIfLet args
    else if kind == ``Lean.Parser.Term.doIfLetPure then emitDoIfLetPure args
    else if kind.toString == "termIfThenElse" then
      -- if a branch carries a line comment, inlining would let it swallow the
      -- `else`; reproduce verbatim to preserve the original line breaks
      if has_line_comment stx then emit_verbatim stx else emitTermIf args
    else if kind == `group then emitGroup args
    -- Strings and literals
    else if kind == `str then emitStr args
    else if kind.toString == "termS!_" then emitSInterp args
    else if kind == `interpolatedStrKind then emitInterpStr args
    else if kind == `interpolatedStrLitKind then for arg in args do emit_syntax arg
    -- List literal
    else if kind.toString == "«term[_]»" then emitListLit args
    -- Index notation
    else if kind.toString == "«term_[_]»" then emitIndexAccess args
    else if kind.toString == "«term_[_]!»" then emitIndexBang args
    else if kind.toString == "«term_[_]?»" then emitIndexQuestion args
    -- Anonymous struct {a, b, c}
    else if kind.toString == "«term{_}»" then emitAnonStruct args
    -- Hole
    else if kind == ``Lean.Parser.Term.hole then emit "_"
    -- Choice node (ambiguous parse) - emit first alternative only
    else if kind == `choice then
      if h : 0 < args.size then emit_syntax args[0]!
    -- Null and unknown
    else if kind == `null then for arg in args do emit_syntax arg
    -- Anything we don't actively restyle: reproduce verbatim from source so it
    -- is never mangled and always parses (tactics, where, calc, notations, …).
    else emit_verbatim stx

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Binary operators
  -- ─────────────────────────────────────────────────────────────────────────────

  emitBinOp (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = left, args[1] = operator atom, args[2] = right
    emit_syntax args[0]!
    space
    emit_syntax args[1]!
    space
    emit_syntax args[2]!

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Top-level
  -- ─────────────────────────────────────────────────────────────────────────────

  emitModule (args : Array Syntax) : emitter_m Unit := do
    if h : 0 < args.size then emit_syntax args[0]
    if h : 1 < args.size then for cmd in args[1].getArgs do emit_syntax cmd; newline

  emitHeader (args : Array Syntax) : emitter_m Unit := do
    for arg in args do emit_syntax arg

  emitImport (args : Array Syntax) : emitter_m Unit := do
    -- Module.import = [_, _, ATOM "import", _, IDENT path, _] (plus optional modifiers)
    let mut firstAtom := true
    for a in args do
      match a with
      | .atom _ v =>
        if firstAtom then process_leading a; emit v; firstAtom := false
        else space; emit v
      | .ident .. => space; emit_syntax a
      | _ => pure ()  -- skip empty null modifier slots
    newline

  emitOpen (args : Array Syntax) : emitter_m Unit := do
    -- Command.open = [ATOM "open", openSimple | openOnly | openHiding | ...]
    if h : 0 < args.size then process_leading args[0]!
    emit "open"
    for i in [1:args.size] do
      let a := args[i]!
      if a.getKind == ``Lean.Parser.Command.openSimple then
        -- null node of namespace idents; space-separate them
        for sub in a.getArgs do
          for id in sub.getArgs do space; emit_syntax id
      else if !a.isNone then
        space; emit_syntax a
    newline

  emitNamespace (args : Array Syntax) : emitter_m Unit := do
    process_leading args[0]!; emit "namespace"; space; emit_syntax args[1]!; newline; blank_line

  emitEnd (args : Array Syntax) : emitter_m Unit := do
    blank_line; process_leading args[0]!; emit "end"
    if args.size > 1 then let a := args[1]!; if !a.isNone then space; emit_syntax a
    newline

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Declarations
  -- ─────────────────────────────────────────────────────────────────────────────

  emitDeclaration (args : Array Syntax) : emitter_m Unit := do
    if h : 0 < args.size then emit_syntax args[0]
    if h : 1 < args.size then emit_syntax args[1]

  emitDeclModifiers (args : Array Syntax) : emitter_m Unit := do
    for arg in args do if !arg.isNone then emit_syntax arg

  emitModifierKeyword (kw : String) (_args : Array Syntax) : emitter_m Unit := do
    emit kw
    space

  emitKeywordDecl (kw : String) (args : Array Syntax) : emitter_m Unit := do
    process_leading args[0]!; emit kw; space
    for i in [1:args.size] do emit_syntax args[i]!

  emitDocComment (args : Array Syntax) : emitter_m Unit := do
    process_leading args[0]!; emit "/--"
    if h : 1 < args.size then
      match args[1]! with
      | .atom _ val =>
        if val.length > 0 then
          let first := val.toList.head!
          if first != ' ' && first != '\n' then emit " "
        emit val
      | other => emit_syntax other
    newline

  emitAttributes (args : Array Syntax) : emitter_m Unit := do
    process_leading args[0]!; emit "@["
    if h : 1 < args.size then
      let attrs := args[1]!.getArgs
      for i in [:attrs.size] do
        if i > 0 then emit ", "
        emitAttrInstance attrs[i]!
    emit "]"; newline

  emitAttrInstance (stx : Syntax) : emitter_m Unit := do
    let args := stx.getArgs
    if h : 1 < args.size then emitAttr args[1]!

  emitAttr (stx : Syntax) : emitter_m Unit := do
    match stx with
    | .node _ kind args =>
      if kind == ``Lean.Parser.Attr.extern then
        emit "extern"
        if h : 1 < args.size then for entry in args[1]!.getArgs do emitExternEntry entry
      else for arg in args do emit_syntax arg
    | other => emit_syntax other

  emitExternEntry (stx : Syntax) : emitter_m Unit := do
    let args := stx.getArgs
    if h : 2 < args.size then space; emit_syntax args[2]!

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Signatures
  -- ─────────────────────────────────────────────────────────────────────────────

  emitDeclId (args : Array Syntax) : emitter_m Unit := do
    if h : 0 < args.size then emit_syntax args[0]
    if h : 1 < args.size then let a := args[1]!; if !a.isNone then emit_syntax a

  emitDeclSig (args : Array Syntax) : emitter_m Unit := do
    if h : 0 < args.size then for binder in args[0]!.getArgs do space; emit_syntax binder
    if h : 1 < args.size then space; emit_syntax args[1]

  emitTypeSpec (args : Array Syntax) : emitter_m Unit := do
    emit ":"; space
    if h : 1 < args.size then emit_syntax args[1]

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Binders
  -- ─────────────────────────────────────────────────────────────────────────────

  emitExplicitBinder (args : Array Syntax) : emitter_m Unit := do
    -- args[0]="(", args[1]=names, args[2]=type?, args[3]=default?, args[4]=")"
    emit "("
    if h : 1 < args.size then
      let names := args[1]!.getArgs
      for i in [:names.size] do
        if i > 0 then space
        emit_syntax names[i]!
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

  emitImplicitBinder (args : Array Syntax) : emitter_m Unit := do
    emit "{"
    if h : 1 < args.size then
      let names := args[1]!.getArgs
      for i in [:names.size] do
        if i > 0 then space
        emit_syntax names[i]!
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

  emitApp (stx : Syntax) (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = fn, args[1] = null of argument terms
    let fn := if h : 0 < args.size then args[0]! else Syntax.missing
    let argList := if h : 1 < args.size then args[1]!.getArgs else #[]
    -- If every part is simple, flatten to a single line (suppressing any stray
    -- source newlines). Otherwise reproduce verbatim so a complex argument's
    -- own layout (do/match/tactic) is preserved and never mangled.
    if is_simple_expr fn && argList.all is_simple_expr then
      with_inline do
        emit_syntax fn
        for arg in argList do space; emit_syntax arg
    else
      emit_verbatim stx

  emitAnonCtor (args : Array Syntax) : emitter_m Unit := do
    emit "⟨"
    if h : 1 < args.size then
      let vals := args[1]!.getArgs
      let mut first := true
      for v in vals do
        if v.isAtom then continue  -- skip existing comma separators
        if !first then emit ", "
        first := false
        emit_syntax v
    emit "⟩"

  emitForall (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "∀", args[1] = binders (null), args[2] = type? (null), args[3] = ",", args[4] = body
    emit "∀"
    space
    -- Emit binders (space-separated)
    if h : 1 < args.size then
      let binders := args[1]!.getArgs
      for i in [:binders.size] do
        if i > 0 then space
        emit_syntax binders[i]!
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

  emitArrow (args : Array Syntax) : emitter_m Unit := do
    -- A → B: args[0] = A, args[1] = "→", args[2] = B
    if h : 0 < args.size then emit_syntax args[0]
    space
    emit "→"
    space
    if h : 2 < args.size then emit_syntax args[2]!

  emitExists (args : Array Syntax) : emitter_m Unit := do
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

  emitStructure (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = structureTk, args[1] = declId, args[2] = optDeclSig,
    -- args[3] = extends?, args[4] = whereBody?, args[5] = optDeriving
    process_leading args[0]!
    -- emit the actual keyword (`structure` OR `class` — never hardcode)
    let kw := (args[0]!.getArgs.findSome? fun c =>
      match c with | .atom _ v => some v | _ => none).getD "structure"
    emit kw
    space
    if h : 1 < args.size then emit_syntax args[1]!  -- name
    if h : 2 < args.size then emit_syntax args[2]!  -- optDeclSig
    -- args[3] is extends (often empty)
    if h : 3 < args.size then let a := args[3]!; if !a.isNone then emit_syntax a
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

  emitInductive (args : Array Syntax) : emitter_m Unit := do
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
      for i in [5:args.size] do emit_syntax args[i]!
    blank_line

  emitCtor (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = docComment?, args[1] = "|", args[2] = modifiers, args[3] = name, args[4] = sig
    -- Don't process leading - we control inductive ctor layout
    emit "  | "
    -- Emit name without triggering processLeading
    if h : 3 < args.size then
      let nameNode := args[3]!
      if let .ident _ _ name _ := nameNode then
        emit name.toString
    if h : 4 < args.size then emit_syntax args[4]!  -- sig

  emitStructField (args : Array Syntax) : emitter_m Unit := do
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
            | .atom _ val =>
              if val.length > 0 then
                let first := val.toList.head!
                if first != ' ' && first != '\n' then emit " "
              emit val
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

  emitDeriving (args : Array Syntax) : emitter_m Unit := do
    -- args[0] is null containing [deriving, classes]
    if args.size > 0 then
      let inner := args[0]!.getArgs
      if inner.size >= 2 then
        -- Don't use processLeading - we control the formatting
        emit "deriving"
        space
        -- inner[1] has the classes
        let classes := inner[1]!.getArgs
        for i in [:classes.size] do
          let cls := classes[i]!
          if cls.isAtom then emit ", "  -- comma separator
          else emit_syntax cls
        newline

  emitDerivingClass (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = optional stuff, args[1] = class name
    if h : 1 < args.size then emit_syntax args[1]!

  emitInstance (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = attrKind, args[1] = "instance", args[2] = priority?, args[3] = name?,
    -- args[4] = sig, args[5] = whereStructInst
    if args.size > 1 then process_leading args[1]!
    emit "instance"
    -- Emit sig (typeSpec)
    if h : 4 < args.size then emit_syntax args[4]!
    -- Emit where body
    if h : 5 < args.size then emit_syntax args[5]!
    blank_line

  emitStructInstField (args : Array Syntax) : emitter_m Unit := do
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
          for b in binders.getArgs do
            space
            if let .ident _ _ name _ := b then emit name.toString
            else emit_syntax b
      if rest.size > 2 then
        emit_syntax rest[2]!  -- fieldDef
    newline

  emitStructInstLVal (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = ident, args[1] = suffix?
    if h : 0 < args.size then emit_syntax args[0]!

  emitStructInstFieldDef (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = ":=", args[1] = optional, args[2] = value
    space
    emit ":="
    space
    if h : 2 < args.size then emit_syntax args[2]!

  emitDeclValSimple (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = ":=", args[1] = body, args[2] = termination?, args[3] = where?
    space
    emit ":="
    space
    if h : 1 < args.size then emit_syntax args[1]!
    -- termination_by / decreasing_by suffix (verbatim, indentation-sensitive)
    if h : 2 < args.size then
      let t := args[2]!
      if !t.isNone && !(t.reprint.getD "").trimAscii.toString.isEmpty then space; emit_verbatim t
    -- where clause (verbatim, indentation-sensitive)
    if h : 3 < args.size then
      let w := args[3]!
      if !w.isNone && !(w.reprint.getD "").trimAscii.toString.isEmpty then space; emit_verbatim w

  emitDeclValEqns (args : Array Syntax) : emitter_m Unit := do
    -- equation-style body: `| pat => e | pat => e`
    -- args[0] = matchAltsWhereDecls ([matchAlts, termination, where?])
    newline
    indent
    for arg in args do emit_syntax arg
    dedent

  emitBinderDefault (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = ":=", args[1] = value
    space
    emit ":="
    space
    if h : 1 < args.size then emit_syntax args[1]!

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Match
  -- ─────────────────────────────────────────────────────────────────────────────

  emitMatch (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "match", args[1..] = opt stuff, scrutinees, "with", alts
    process_leading args[0]!
    emit "match"
    space
    -- Emit scrutinees and alts
    let st ← get_state
    for i in [1:args.size] do
      let arg := args[i]!
      if arg.isAtom then
        if let .atom _ val := arg then
          if val == "with" then
            space
            emit "with"
            if st.inlineMode then space else newline
      else if !arg.isNone then emit_syntax arg

  emitDoMatch (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "match", args[1..] = opt stuff, scrutinees, "with", alts
    emit "match"
    space
    let st ← get_state
    -- Skip the opt null nodes, find the discriminant and alts
    for i in [1:args.size] do
      let arg := args[i]!
      if arg.isAtom then
        if let .atom _ val := arg then
          if val == "with" then
            space
            emit "with"
            if st.inlineMode then space else newline
      else if !arg.isNone then emit_syntax arg

  emitMatchDiscr (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = opt h:, args[1] = expr
    if h : 1 < args.size then emit_syntax args[1]!

  emitMatchAlts (args : Array Syntax) : emitter_m Unit := do
    -- args is typically a single null node containing the alts
    let st ← get_state
    for arg in args do
      match arg with
      | .node _ _ alts =>
        let mut first := true
        for alt in alts do
          if !first && st.inlineMode then space
          first := false
          emit_syntax alt
      | _ => emit_syntax arg

  emitMatchAlt (args : Array Syntax) : emitter_m Unit := do
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

  emitParen (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "(", args[1] = content, args[2] = ")"
    emit "("
    if h : 1 < args.size then emit_syntax args[1]!
    emit ")"

  emitDotIdent (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = ".", args[1] = ident
    emit "."
    if h : 1 < args.size then emit_syntax args[1]!

  emitPipeProj (args : Array Syntax) : emitter_m Unit := do
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

  emitStructInst (args : Array Syntax) : emitter_m Unit := do
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
        for f in fieldArr do
          -- Skip null separator nodes
          match f with
          | .node _ kind _ =>
            if kind == ``Lean.Parser.Term.structInstField then
              if !first then emit ", "
              first := false
              emitStructInstFieldInline f
          | _ => pure ()
    emit " }"

  emitStructInstFieldInline (stx : Syntax) : emitter_m Unit := do
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

  emitProj (args : Array Syntax) : emitter_m Unit := do
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

  emitFun (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "fun", args[1] = funBody
    process_leading args[0]!
    emit "fun"
    space
    if h : 1 < args.size then emit_syntax args[1]!

  emitBasicFun (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = binders (null), args[1] = type? (null), args[2] = "=>", args[3] = body
    -- Emit binders (idents, holes `_`, typed `(x : T)`, etc.) via emitSyntax
    if h : 0 < args.size then
      let binders := args[0]!.getArgs
      for i in [:binders.size] do
        if i > 0 then space
        emit_syntax binders[i]!
    -- optional return-type ascription
    if h : 1 < args.size then
      let t := args[1]!
      if !t.isNone then space; emit_syntax t
    space
    emit "=>"
    space
    if h : 3 < args.size then emit_syntax args[3]!

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Do notation
  -- ─────────────────────────────────────────────────────────────────────────────

  emitDo (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "do", args[1] = doSeq
    process_leading args[0]!
    emit "do"
    newline
    indent
    if h : 1 < args.size then emit_syntax args[1]!
    dedent

  emitDoSeqBracketed (args : Array Syntax) : emitter_m Unit := do
    for arg in args do emit_syntax arg

  emitDoSeqIndent (args : Array Syntax) : emitter_m Unit := do
    for arg in args do emit_syntax arg

  emitDoSeqItem (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = content, args[1] = optional semicolon
    -- Indentation is handled by the emit function based on indentLevel
    if h : 0 < args.size then emit_syntax args[0]!
    newline

  emitDoLetArrow (args : Array Syntax) : emitter_m Unit := do
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

  emitDoReturn (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "return", args[1] = value (null containing expr)
    emit "return"
    space
    if h : 1 < args.size then
      for v in args[1]!.getArgs do emit_syntax v

  emitDoFor (args : Array Syntax) : emitter_m Unit := do
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

  emitDoForDecl (stx : Syntax) : emitter_m Unit := do
    -- doForDecl: args[0] = opt h:, args[1] = pattern, args[2] = "in", args[3] = expr
    let args := stx.getArgs
    if h : 1 < args.size then emit_syntax args[1]!  -- pattern
    space
    emit "in"
    space
    if h : 3 < args.size then emit_syntax args[3]!  -- collection

  emitDoExpr (args : Array Syntax) : emitter_m Unit := do
    -- doExpr wraps an expression
    for arg in args do emit_syntax arg

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Let and If
  -- ─────────────────────────────────────────────────────────────────────────────

  emitLet (args : Array Syntax) : emitter_m Unit := do
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

  emitDoLet (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "let", args[1] = opt "mut", args[2] = config, args[3] = letDecl
    emit "let"
    space
    -- optional `mut` modifier — must not be dropped (mutation depends on it)
    if h : 1 < args.size then
      let opt := args[1]!
      if !opt.isNone then emit_syntax opt; space
    if h : 3 < args.size then emit_syntax args[3]!

  emitLetDecl (args : Array Syntax) : emitter_m Unit := do
    for arg in args do emit_syntax arg

  emitLetIdDecl (args : Array Syntax) : emitter_m Unit := do
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

  emitLetId (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = ident
    if h : 0 < args.size then
      let nameNode := args[0]!
      if let .ident _ _ name _ := nameNode then
        emit name.toString

  emitDoIf (args : Array Syntax) : emitter_m Unit := do
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

  emitDoIfProp (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = opt h:, args[1] = condition expr
    if h : 1 < args.size then emit_syntax args[1]!

  emitDoIfLet (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "let", args[1] = pattern, args[2] = ":="/"<-" and value
    emit "let"
    space
    if h : 1 < args.size then emit_syntax args[1]!
    if h : 2 < args.size then emit_syntax args[2]!

  emitDoIfLetPure (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = ":=", args[1] = value
    space
    emit ":="
    space
    if h : 1 < args.size then emit_syntax args[1]!

  emitTermIf (args : Array Syntax) : emitter_m Unit := do
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

  emitGroup (args : Array Syntax) : emitter_m Unit := do
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
    for i in [1:args.size] do
      let arg := args[i]!
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
        if i == args.size - 1 then dedent

  -- ─────────────────────────────────────────────────────────────────────────────
  -- Strings and literals
  -- ─────────────────────────────────────────────────────────────────────────────

  emitStr (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = the string literal atom
    if h : 0 < args.size then emit_syntax args[0]!

  emitSInterp (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = "s!", args[1] = interpolatedStrKind
    emit "s!"
    if h : 1 < args.size then emit_syntax args[1]!

  emitInterpStr (args : Array Syntax) : emitter_m Unit := do
    -- Children are alternating string literals and expressions
    for arg in args do emit_syntax arg

  emitListLit (args : Array Syntax) : emitter_m Unit := do
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

  emitIndexAccess (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = array, args[1] = "[", args[2] = index, args[3] = "]"
    if h : 0 < args.size then emit_syntax args[0]!
    emit "["
    if h : 2 < args.size then emit_syntax args[2]!
    emit "]"

  emitIndexBang (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = array, args[1] = "[", args[2] = index, args[3] = "]!"
    if h : 0 < args.size then emit_syntax args[0]!
    emit "["
    if h : 2 < args.size then emit_syntax args[2]!
    emit "]!"

  emitIndexQuestion (args : Array Syntax) : emitter_m Unit := do
    -- args[0] = array, args[1] = "[", args[2] = index, args[3] = "]?"
    if h : 0 < args.size then emit_syntax args[0]!
    emit "["
    if h : 2 < args.size then emit_syntax args[2]!
    emit "]?"

  emitAnonStruct (args : Array Syntax) : emitter_m Unit := do
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

end Emitter

def format (stx : Syntax) (config : style_config := {}) : String × Array Diagnostic :=
  let ((), st) := emitter_m.run Unit config (Emitter.emit_syntax stx)
  let output :=
    if config.trailingNewline && !st.output.endsWith "\n" then st.output ++ "\n" else st.output
  (output, st.lints)

end Lean4Fmt
