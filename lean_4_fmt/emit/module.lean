/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // EMIT // MODULE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Header + per-command dispatch. THIS is the passthrough seam: each top-level
    command is independently routed through `walk` — a handled kind (e.g. a
    declaration) is actively formatted, everything else is reproduced verbatim,
    with byte-exact tiling of leading trivia. Per-top-level-form granularity.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.emit.monad

namespace Lean4Fmt.Emit.Module

open Lean Lean4Fmt.Doc

private
structure trivia_state where
  idx    : Nat := 0
  doc    : Doc := .nil
  blanks : Nat := 0
  sawAny : Bool := false
  depth  : Nat := 0
  chunk  : Array String := #[]

private
structure module_state where
  output       : Doc := .nil
  previous     : Option (Lean.Syntax × Doc) := none
  pendingTrail : Doc := .nil

private
def import_lines_doc? (imports : Array Lean.Syntax) : Option Doc :=
  Id.run do
    let mut document : Doc := .nil
    for idx in [0:imports.size] do
      let importSyntax := imports[idx]!
      let text := (Lean4Fmt.Emit.bare_src importSyntax).trimAscii.toString
      if text.isEmpty || text.any (· == '\n') then
        return none
      let last := idx + 1 == imports.size
      let trailing := ((Lean4Fmt.Syntax.trailing? importSyntax).getD "").trimAscii.toString
      if !last && trailing.any (· == '\n') then
        return none
      let trailingDoc : Doc := if !last && !trailing.isEmpty then .text (" " ++ trailing) else .nil
      let separator? :=
        if idx == 0 then
          some (.nil : Doc)
        else
          Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? importSyntax).getD "")
      match separator? with
      | some separator => document := document ++ separator ++ .text text ++ trailingDoc
      | none => return none
    return some document

/-- Active layout for the module header: one `import X` line per import, the
    line reproduced token-for-token (trimmed, single-spaced — `public`/`meta`
    markers ride inside the import node's span), inter-import comment/blank
    lines placed structurally, same-line trailing comments re-appended. The
    FIRST import's leading is the header's outer leading (the file banner —
    `unit` places it byte-exact); the LAST import's trailing is the header's
    trailing, likewise. `none` (verbatim) on a `module`/`prelude` marker, a
    multi-line import span, or a seamless comment. -/
private
def header_doc? (headerSyntax : Lean.Syntax) : Option Doc :=
  Id.run do
    if headerSyntax.getKind != ``Lean.Parser.Module.header then
      return none
    let args := headerSyntax.getArgs
    if args.size != 3 then
      return none
    if !((args[0]?.map Lean4Fmt.Emit.bare_src).getD "").trimAscii.toString.isEmpty then
      return none
    if !((args[1]?.map Lean4Fmt.Emit.bare_src).getD "").trimAscii.toString.isEmpty then
      return none
    let imps := (args[2]?.map (·.getArgs)).getD #[]
    if imps.isEmpty then
      return none
    import_lines_doc? imps

/-- Structural placement of MODULE-LEVEL trivia with block-comment awareness:
    comment chunks (line comments; balanced `/- … -/` blocks INCLUDING their
    interior blank lines — comment text is content) ride byte-exact; the
    whitespace runs between chunks become structural separators (blank runs
    clamp to policy). `none` when the trivia has a shape no seam owns
    (a same-line head segment with content). -/
private
def flush_trivia_chunk
    (atFileStart : Bool)
    (document : Doc)
    (blanks : Nat)
    (sawAny : Bool)
    (chunk : Array String)
    : Doc :=
  if chunk.isEmpty then
    document
  else
    let separator : Doc :=
      if atFileStart && !sawAny then .nil else if blanks > 0 then .blank blanks else .hardline
    document ++ separator
        ++ .textRaw (String.intercalate "\n" (chunk.toList.map (·.trimAsciiEnd.toString)))

private
def trivia_depth_delta (text : String) : Nat :=
  (text.splitOn "/-").length - 1 - ((text.splitOn "-/").length - 1)

private
def append_open_comment_line
    (state : trivia_state)
    (line text : String)
    : trivia_state := { state with
  chunk := state.chunk.push line
  depth := state.depth + trivia_depth_delta text
}

private
def append_blank_trivia_line (atFileStart last : Bool) (state : trivia_state) : trivia_state :=
  if last then
    state
  else if !state.chunk.isEmpty then
    { state with
      doc := flush_trivia_chunk atFileStart state.doc state.blanks state.sawAny state.chunk
      sawAny := true
      chunk := #[]
      blanks := 1
    }
  else
    { state with blanks := state.blanks + 1 }

private
def append_comment_start_line
    (atFileStart : Bool)
    (state : trivia_state)
    (line text : String)
    : trivia_state :=
  let state :=
    if !state.chunk.isEmpty && text.startsWith "/-" then
      { state with
        doc := flush_trivia_chunk atFileStart state.doc state.blanks state.sawAny state.chunk
        sawAny := true
        chunk := #[]
        blanks := 0
      }
    else
      state
  let state := { state with chunk := state.chunk.push (line.trimAsciiEnd.toString) }
  if text.startsWith "/-" then
    { state with depth := state.depth + trivia_depth_delta text }
  else
    state

private
def advance_trivia_line?
    (atFileStart : Bool)
    (lines : List String)
    (state : trivia_state)
    : Option trivia_state :=
  let line := lines[state.idx]!
  let last := state.idx + 1 == lines.length
  let text := line.trimAscii.toString
  let next? :=
    if state.depth > 0 then
      some (append_open_comment_line state line text)
    else if text.isEmpty then
      some (append_blank_trivia_line atFileStart last state)
    else if text.startsWith "--" || text.startsWith "/-" then
      some (append_comment_start_line atFileStart state line text)
    else
      none
  next?.map fun next => { next with idx := next.idx + 1 }

/-- Structural placement of MODULE-LEVEL trivia with block-comment awareness:
    comment chunks (line comments; balanced `/- … -/` blocks INCLUDING their
    interior blank lines — comment text is content) ride byte-exact; the
    whitespace runs between chunks become structural separators (blank runs
    clamp to policy). `none` when the trivia has a shape no seam owns
    (a same-line head segment with content). -/
private
def module_trivia? (lead : String) (atFileStart : Bool) : Option Doc :=
  Id.run
    do
      let lines := lead.splitOn "\n"
      if lines.isEmpty then
        return some .nil
      -- head segment: remainder of the previous line (must be ws) — except at
      -- file start, where the first segment IS the first line of the file
      let mut state : trivia_state := {}
      if !atFileStart then
        if !(lines[0]!.toList.all (·.isWhitespace)) then
          return none
        state := { state with idx := 1 }
      let lineCount := lines.length
      while state.idx < lineCount do
        match advance_trivia_line? atFileStart lines state with
        | some next => state := next
        | none => return none
      if state.depth != 0 then
        return none
      if !state.chunk.isEmpty then
        state := { state with
          doc := flush_trivia_chunk atFileStart state.doc state.blanks state.sawAny state.chunk
          sawAny := true
          blanks := 0
        }
      -- final separator before the form
      let finalSep : Doc :=
        if atFileStart && !state.sawAny then
          .nil
        else if state.blanks > 0 then .blank state.blanks else .hardline
      return some (state.doc ++ finalSep)

/-- Drop the leftmost separator of a seam doc (the file head has no previous
    line — a leading hardline/blank would open the file with a stray newline). -/
private partial
def drop_leading_sep : Doc → Doc
  | .cat leftValue rightValue => .cat (drop_leading_sep leftValue) rightValue
  | .hardline => .nil
  | .blank _ => .nil
  | document => document

private
def module_doc_is_multiline (style : Lean4Fmt.Style.Style) (body : Doc) : Bool :=
  match Lean4Fmt.Doc.flat_width body with
  | some width => width > style.layout.lineWidth
  | none       => true

private
def module_gap_is_normalizable
    (style : Lean4Fmt.Style.Style)
    (previous current : Lean.Syntax)
    (previousBody currentBody : Doc)
    : Bool :=
  if style.blankLines.policy != Lean4Fmt.Style.blank_policy.normalize then
    false
  else
    let gap :=
      ((Lean4Fmt.Syntax.trailing? previous).getD "") ++ ((Lean4Fmt.Syntax.leading? current).getD "")
    let newlines := (gap.toList.filter (· == '\n')).length
    gap.toList.all (·.isWhitespace) && newlines ≥ 1
        && (
          module_doc_is_multiline style previousBody || module_doc_is_multiline style currentBody
              || newlines ≥ 2
        )

private
def module_file_head (style : Lean4Fmt.Style.Style) (leading : String) : Doc :=
  if style.blankLines.policy == Lean4Fmt.Style.blank_policy.normalize then
    match module_trivia? leading (atFileStart := true) with
    | some document => document
    | none          => .textRaw leading
  else
    .textRaw leading

private
def normalized_comment_gap?
    (style : Lean4Fmt.Style.Style)
    (trailing leading : String)
    : Option Doc := do
  if style.blankLines.policy != Lean4Fmt.Style.blank_policy.normalize then none
  if trailing.any (· == '\n') then none
  let trailingText := trailing.trimAscii.toString
  if trailingText.startsWith "/-" && !trailingText.startsWith "/--" then none
  let separator ← module_trivia? leading (atFileStart := false)
  let trailingDoc : Doc := if trailingText.isEmpty then .nil else .text (" " ++ trailingText)
  return trailingDoc ++ separator

private
def append_comment_or_raw_gap
    (style : Lean4Fmt.Style.Style)
    (state : module_state)
    (current : Lean.Syntax)
    (body : Doc)
    (trailing leading : String)
    : module_state :=
  match normalized_comment_gap? style trailing leading with
  | some gap => { state with output := state.output ++ gap ++ body }
  | none =>
    { state with
      output := state.output ++ state.pendingTrail ++ Lean4Fmt.Emit.leading_raw current ++ body }

private
def append_after_previous
    (style : Lean4Fmt.Style.Style)
    (state : module_state)
    (current : Lean.Syntax)
    (body : Doc)
    (previous : Lean.Syntax)
    (previousBody : Doc)
    : module_state :=
  if (Lean4Fmt.Emit.bare_src previous).isEmpty
      && ((Lean4Fmt.Syntax.trailing? previous).getD "").isEmpty then
    { state with
      output := state.output ++ module_file_head style ((Lean4Fmt.Syntax.leading? current).getD "")
          ++ body }
  else if module_gap_is_normalizable style previous current previousBody body then
    { state with output := state.output ++ .blank style.blankLines.betweenTopLevelDecls ++ body }
  else
    let trailing := (Lean4Fmt.Syntax.trailing? previous).getD ""
    let leading := (Lean4Fmt.Syntax.leading? current).getD ""
    let gap := trailing ++ leading
    let normalize := style.blankLines.policy == Lean4Fmt.Style.blank_policy.normalize
    if normalize && gap.toList.all (·.isWhitespace) && (gap.toList.filter (· == '\n')).length == 1 then
      { state with output := state.output ++ .hardline ++ body }
    else
      append_comment_or_raw_gap style state current body trailing leading

private
def append_module_body
    (style : Lean4Fmt.Style.Style)
    (state : module_state)
    (current : Lean.Syntax)
    (body : Doc)
    : module_state :=
  let state :=
    match state.previous with
    | some (previous, previousBody) =>
      append_after_previous style state current body previous previousBody
    | none =>
      { state with
        output := state.output
            ++ module_file_head style ((Lean4Fmt.Syntax.leading? current).getD "")
            ++ body }
  { state with
    previous := some (current, body)
    pendingTrail := Lean4Fmt.Emit.trailing_raw current
  }

private
def append_eoi (state : module_state) (command : Lean.Syntax) : module_state :=
  let leading := (Lean4Fmt.Syntax.leading? command).getD ""
  if leading.toList.all (·.isWhitespace) then
    state
  else
    { state with
      output := state.output ++ state.pendingTrail ++ Lean4Fmt.Emit.leading_raw command
      pendingTrail := .nil
      previous := none
    }

private
def append_module_command
    (walk : Lean4Fmt.Emit.Walk)
    (style : Lean4Fmt.Style.Style)
    (state : module_state)
    (command : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m module_state := do
  if command.getKind == ``Lean.Parser.Command.eoi then
    return append_eoi state command
  let body ← walk command
  return append_module_body style state command body

private
def initial_header_state
    (walk : Lean4Fmt.Emit.Walk)
    (style : Lean4Fmt.Style.Style)
    (header : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m module_state := do
  let body ← match header_doc? header with
  | some document => pure document
  | none => walk header
  return {
    output := module_file_head style ((Lean4Fmt.Syntax.leading? header).getD "") ++ body
    previous := some (header, body)
    pendingTrail := Lean4Fmt.Emit.trailing_raw header
  }

private
def initial_module_state
    (walk : Lean4Fmt.Emit.Walk)
    (style : Lean4Fmt.Style.Style)
    (header? : Option Lean.Syntax)
    : Lean4Fmt.Emit.emit_m module_state :=
  match header? with
  | some header => initial_header_state walk style header
  | none        => pure {}

private
def finish_module (style : Lean4Fmt.Style.Style) (state : module_state) : Doc :=
  let finalWhitespace :=
    match state.previous with
    | some (previous, _) =>
      ((Lean4Fmt.Syntax.trailing? previous).getD "").toList.all (·.isWhitespace)
    | none => false
  if style.blankLines.policy == Lean4Fmt.Style.blank_policy.normalize && finalWhitespace then
    state.output
  else
    state.output ++ state.pendingTrail

/-- Emit a whole module: each form (header + commands) as
    `leading ++ walk(bare) ++ trailing`. Since leading[next] and trailing[prev]
    partition the inter-form gap exactly, forms tile byte-exactly — handled kinds
    are actively formatted, the rest reproduced verbatim. Per-form granularity.

    Blank-line policy (`blankLines.policy = .normalize`): a PURE-WHITESPACE
    inter-form gap containing a newline, where either neighbor is a multi-line
    form, is replaced by exactly `blankLines.betweenTopLevelDecls` blank lines —
    the top-level rhythm is imposed, not preserved. Everything else stays
    byte-exact: gaps carrying comments (banners, section markers), same-line
    gaps, and gaps between single-line forms (runs of one-line defs keep their
    hand grouping). `.preserve` keeps every gap byte-exact. -/
def emit (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let style ← read
  let args := stx.getArgs
  let mut state ← initial_module_state walk style args[0]?
  let cmds := (args[1]?.map (·.getArgs)).getD #[]
  for command in cmds do
    state ← append_module_command walk style state command
  return finish_module style state

end Lean4Fmt.Emit.Module
