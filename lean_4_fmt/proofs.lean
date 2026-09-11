/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                            // LEAN4FMT // PROOFS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The laws of the extended Wadler/Leijen core (doc/design.md §5), stated about
    the SHIPPED render functions. Two-tier verification: everything below the
    parser boundary is proved here; everything whose statement needs the parser
    (idempotence, whole-pipeline token preservation) is the runtime gate's job
    by design.

    T1  render_content — rendering only moves whitespace (content
        preservation), UNCONDITIONALLY: verbatim/textRaw payloads are covered
        (the wrBlock dedent is provably spaces-only), and alignOr coherence is
        enforced by the renderer itself (the grid is taken only when its
        content equals the fallback's).
    T2  go_flat_exact  — flat rendering is exact: `flatWidth d = some n` means
        flat mode appends ONE newline-free string of length exactly n and
        advances the column by exactly n. This is what makes `group`'s fit
        decision (and goFill's packing) an oracle rather than a heuristic.
    T3  leadingSep?_content — the seam kit is content-exact: when a vertical
        loop owns a form's leading trivia, the separator doc it emits carries
        EXACTLY the trivia's non-whitespace characters (every comment, in
        order); when a partial line carries content no seam owns, the answer
        is `none` (verbatim), never a drop.
    T4  wr_out         — the writer's extension is exactly the written content
        (never an indent with nothing after it).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.doc.core
import lean_4_fmt.doc.content
import lean_4_fmt.doc.render
import lean_4_fmt.doc.seam

namespace Lean4Fmt.Doc.Proofs

open Lean4Fmt.Doc

set_option maxHeartbeats 1000000

-- ── char/string plumbing ──────────────────────────────────────────────────────

@[simp]
theorem non_ws_l_nil : non_ws_l [] = [] := rfl

@[simp]
theorem non_ws_l_append
        (proofLeft proofRight : List Char)
        : non_ws_l (proofLeft ++ proofRight) = non_ws_l proofLeft ++ non_ws_l proofRight := by
  simp [non_ws_l, List.filter_append]

@[simp]
theorem non_ws_append
        (proofLeft proofRight : String)
        : non_ws (proofLeft ++ proofRight) = non_ws proofLeft ++ non_ws proofRight := by
  simp [non_ws, String.toList_append]

@[simp]
theorem non_ws_of_list
        (proofList : List Char)
        : non_ws (String.ofList proofList) = non_ws_l proofList := by
  simp [non_ws, String.toList_ofList]

@[simp]
theorem of_list_length
        (proofList : List Char)
        : (String.ofList proofList).length = proofList.length := by
  have listLengthEquality := congrArg List.length (String.toList_ofList (l := proofList))
  simpa [String.length_toList] using listLengthEquality

@[simp]
theorem space_length : (" " : String).length = 1 := rfl

@[simp]
theorem non_ws_spaces (proofCount : Nat) : non_ws (spaces proofCount) = [] := by
  simp only [spaces, non_ws_of_list, non_ws_l]
  induction proofCount with
  | zero => rfl
  | succ predecessor inductionHypothesis => simpa [List.replicate_succ] using inductionHypothesis

@[simp]
theorem non_ws_newlines (proofCount : Nat) : non_ws (newlines proofCount) = [] := by
  simp only [newlines, non_ws_of_list, non_ws_l]
  induction proofCount with
  | zero => rfl
  | succ predecessor inductionHypothesis => simpa [List.replicate_succ] using inductionHypothesis

@[simp]
theorem non_ws_empty : non_ws "" = [] := rfl

@[simp]
theorem non_ws_space : non_ws " " = [] := by decide

@[simp]
theorem non_ws_newline : non_ws "\n" = [] := by decide

theorem non_ws_l_nil_of_spaces
        (proofChars : List Char)
        (allSpaces : proofChars.all (· == ' '))
        : non_ws_l proofChars = [] := by
  simp only [non_ws_l, List.filter_eq_nil_iff]
  intro char charMem
  have : char = ' ' := by simpa using List.all_eq_true.mp allSpaces char charMem
  subst this
  decide

theorem non_ws_l_drop_while_space
        (proofChars : List Char)
        : non_ws_l (proofChars.dropWhile (· == ' ')) = non_ws_l proofChars := by
  induction proofChars with
  | nil => rfl
  | cons head tail inductionHypothesis =>
    by_cases char_is_space : head = ' '
    · subst char_is_space
      have : (!(' ' : Char).isWhitespace) = false := by decide
      simpa [List.dropWhile_cons, non_ws_l, List.filter_cons, this] using inductionHypothesis
    · simp [List.dropWhile_cons, char_is_space]

theorem non_ws_l_drop_while_ws
        (proofChars : List Char)
        : non_ws_l (proofChars.dropWhile Char.isWhitespace) = non_ws_l proofChars := by
  induction proofChars with
  | nil => rfl
  | cons head tail inductionHypothesis =>
    by_cases char_is_whitespace : head.isWhitespace
    · simpa [List.dropWhile_cons, non_ws_l, List.filter_cons, char_is_whitespace] using inductionHypothesis
    · simp [List.dropWhile_cons, char_is_whitespace]

theorem non_ws_l_reverse
        (proofChars : List Char)
        : non_ws_l proofChars.reverse = (non_ws_l proofChars).reverse := by
  simp [non_ws_l, List.filter_reverse]

theorem non_ws_l_trim_end_ws
        (proofChars : List Char)
        : non_ws_l (trim_end_ws proofChars) = non_ws_l proofChars := by
  unfold trim_end_ws
  rw [non_ws_l_reverse, non_ws_l_drop_while_ws, non_ws_l_reverse, List.reverse_reverse]

-- ── splitLines / wrBlock plumbing ─────────────────────────────────────────────

theorem split_lines_ne_nil (proofChars : List Char) : split_lines proofChars ≠ [] := by
  cases proofChars with
  | nil => simp [split_lines]
  | cons head tail =>
    simp only [split_lines]
    repeat' split
    all_goals simp

/-- Line-splitting loses only the '\n' separators — whitespace. -/
theorem split_lines_non_ws
        (proofChars : List Char)
        : ((split_lines proofChars).map non_ws_l).flatten = non_ws_l proofChars := by
  induction proofChars with
  | nil => simp [split_lines]
  | cons head tail inductionHypothesis =>
    simp only [split_lines]
    cases splitLinesEquation : split_lines tail with
    | nil => exact absurd splitLinesEquation (split_lines_ne_nil tail)
    | cons line lines =>
      rw [splitLinesEquation] at inductionHypothesis
      simp only [List.map_cons, List.flatten_cons] at inductionHypothesis
      by_cases char_is_newline : head = '\n'
      · subst char_is_newline
        simp only [reduceIte, List.map_cons, List.flatten_cons, non_ws_l_nil, List.nil_append]
        rw [inductionHypothesis]
        show non_ws_l tail = non_ws_l ('\n' :: tail)
        have : (!('\n' : Char).isWhitespace) = false := by decide
        simp [non_ws_l, List.filter_cons, this]
      · simp only [if_neg char_is_newline, List.map_cons, List.flatten_cons]
        show non_ws_l (head :: line) ++ (lines.map non_ws_l).flatten = non_ws_l (head :: tail)
        cases whitespaceEquation : (!head.isWhitespace) with
        | false =>
          simp only [non_ws_l, List.filter_cons, whitespaceEquation, Bool.false_eq_true, if_false]
          exact inductionHypothesis
        | true =>
          simp only [non_ws_l, List.filter_cons, whitespaceEquation, if_true, List.cons_append]
          exact congrArg (head :: ·) inductionHypothesis

theorem flatten_map_drop_blank
        (proofLines : List (List Char))
        : (((proofLines.dropWhile is_blank_line).map non_ws_l)).flatten
            = (proofLines.map non_ws_l).flatten := by
  induction proofLines with
  | nil => rfl
  | cons line lines inductionHypothesis =>
    by_cases line_is_blank : is_blank_line line = true
    · rw [List.dropWhile_cons_of_pos line_is_blank]
      simp [inductionHypothesis, non_ws_l_nil_of_spaces line line_is_blank]
    · rw [List.dropWhile_cons_of_neg (by simp [line_is_blank])]

/-- T4 (writer hygiene / content): `writeResult`'s extension over the old output is
    exactly `nonWs s` — the pending newlines and indent it flushes contribute
    nothing. In particular `writeResult` never writes the indent except immediately
    followed by its content. -/
@[simp]
theorem wr_out
        (proofState : rst)
        (indent : Nat)
        (proofText : String)
        : non_ws (writeResult proofState indent proofText).out
            = non_ws proofState.out ++ non_ws proofText := by
  unfold writeResult
  by_cases has_pending_lines : proofState.pend > 0 <;> simp [has_pending_lines]

/-- Dedenting drops only spaces — the content of a continuation line survives
    its re-anchoring intact (the wrBlock content-eater made impossible). -/
theorem non_ws_l_dedent
        (base : Nat)
        (proofList : List Char)
        : non_ws_l (dedent base proofList) = non_ws_l proofList := by
  unfold dedent
  split
  · next dedentCondition =>
      simp only [Bool.and_eq_true] at dedentCondition
      have takeDropContent : non_ws_l proofList = non_ws_l (proofList.take base) ++ non_ws_l (proofList.drop base) := by
        rw [← non_ws_l_append, List.take_append_drop]
      rw [takeDropContent, non_ws_l_nil_of_spaces _ dedentCondition.2, List.nil_append]
  · exact non_ws_l_drop_while_space proofList

theorem wr_line_out
        (proofState : rst)
        (indent base : Nat)
        (proofList : List Char)
        : non_ws (wr_line proofState indent base proofList).out
            = non_ws proofState.out ++ non_ws_l proofList := by
  unfold wr_line
  split
  · next dedentIsEmpty =>
      have dedentEmpty : dedent base proofList = [] := by
        simpa [List.isEmpty_iff] using dedentIsEmpty
      have lineContentEmpty : non_ws_l proofList = [] := by
        rw [← non_ws_l_dedent base proofList, dedentEmpty]; rfl
      simp [lineContentEmpty]
  · simp [wr_out, non_ws_l_dedent]

theorem wr_lines_out
        (indent base : Nat)
        (proofLines : List (List Char))
        (proofState : rst)
        : non_ws (wr_lines indent base proofLines proofState).out
            = non_ws proofState.out ++ (proofLines.map non_ws_l).flatten := by
  induction proofLines generalizing proofState with
  | nil => simp [wr_lines]
  | cons line lines inductionHypothesis =>
    simp [wr_lines, inductionHypothesis, wr_line_out, List.append_assoc]

/-- The string-aware block writer preserves the content of every continuation
    line; its mask changes indentation only. -/
theorem wr_lines_m_out
        (indent base : Nat)
        (proofLines : List (List Char))
        (mask : List Bool)
        (proofState : rst)
        : non_ws (wr_lines_m indent base proofLines mask proofState).out
            = non_ws proofState.out ++ (proofLines.map non_ws_l).flatten := by
  induction proofLines generalizing mask proofState with
  | nil => simp [wr_lines_m]
  | cons line lines inductionHypothesis =>
    simp only [wr_lines_m, List.map_cons, List.flatten_cons]
    split
    · rw [inductionHypothesis, wr_out]
      simp [non_ws_of_list, List.append_assoc]
    · rw [inductionHypothesis, wr_line_out, List.append_assoc]

/-- Dropping the length of the accepted prefix is `dropWhile`. -/
theorem drop_take_while_length
        (predicate : List Char → Bool)
        (proofLines : List (List Char))
        : proofLines.drop (proofLines.takeWhile predicate).length = proofLines.dropWhile predicate := by
  induction proofLines with
  | nil => rfl
  | cons line lines inductionHypothesis =>
    by_cases accepted : predicate line
    · simp [List.takeWhile, List.dropWhile, accepted, inductionHypothesis]
    · simp [List.takeWhile, List.dropWhile, accepted]

/-- The block writer preserves content exactly: trimming, blank-line dropping,
    and dedenting all touch only whitespace (the spaces-only dedent guard is
    what makes this true — it was a latent content-eater before this law). -/
theorem wr_block_out
        (proofState : rst)
        (indent base : Nat)
        (raw : String)
        : non_ws (wr_block proofState indent base raw).out = non_ws proofState.out ++ non_ws raw := by
  have contentChain :
      (((split_lines (trim_end_ws raw.toList)).dropWhile is_blank_line).map non_ws_l).flatten
          = non_ws_l raw.toList := by
    rw [flatten_map_drop_blank, split_lines_non_ws, non_ws_l_trim_end_ws]
  unfold wr_block
  simp only [drop_take_while_length]
  cases linesEquation : (split_lines (trim_end_ws raw.toList)).dropWhile is_blank_line with
  | nil =>
    rw [linesEquation] at contentChain
    simp only [List.map_nil, List.flatten_nil] at contentChain
    show non_ws proofState.out = non_ws proofState.out ++ non_ws raw
    rw [show non_ws raw = non_ws_l raw.toList from rfl, ← contentChain, List.append_nil]
  | cons line rest =>
    rw [linesEquation] at contentChain
    simp only [List.map_cons, List.flatten_cons] at contentChain
    rw [wr_lines_m_out, wr_out, non_ws_of_list, List.append_assoc, contentChain]
    rfl

-- ── T1: content preservation ──────────────────────────────────────────────────

/-- The table-emission fold appends exactly the padded rows' content. -/
theorem emit_table_content
        (maxPend indent : Nat)
        (sep : String)
        (widths : List Nat)
        (strRows : List (List String))
        (proofState : rst)
        : non_ws (emit_table maxPend indent sep widths strRows proofState).out
            = non_ws proofState.out
                ++ ((strRows.map fun row => non_ws (render_row_str sep widths row)).flatten) := by
  suffices table_content : ∀ (first : Bool) (proofState : rst),
      non_ws ((strRows.foldl (fun (progress : rst × Bool) row =>
        let state :=
          if progress.2 then
            progress.1
          else
            { progress.1 with pend := Nat.min (progress.1.pend + 1) maxPend }
        (writeResult state indent (render_row_str sep widths row), false)) (proofState, first)).1).out
      = non_ws proofState.out
          ++ ((strRows.map fun row => non_ws (render_row_str sep widths row)).flatten) by
    exact table_content true proofState
  induction strRows with
  | nil => intro first state; simp
  | cons row rows inductionHypothesis =>
    intro first state
    simp only [List.foldl_cons, List.map_cons, List.flatten_cons]
    rw [inductionHypothesis]
    by_cases is_first_row : first <;> simp [is_first_row, wr_out, List.append_assoc]

mutual

/-- **T1 — content preservation, UNCONDITIONAL.** Rendering appends exactly
    the doc's content: the renderer can move, insert, and collapse whitespace,
    and can do NOTHING else — for every doc, opaque payloads included. -/
theorem go_content (width maxPend : Nat) (proofDocument : Doc) (indent : Nat) (flat : Bool)
    (proofState : rst) :
    non_ws (renderLoop width maxPend proofDocument indent flat proofState).out = non_ws proofState.out ++ content proofDocument := by
  match proofDocument with
  | .nil => simp [renderLoop, go_basic?, content]
  | .text textValue => simp [renderLoop, go_basic?, content, wr_out]
  | .textRaw textValue =>
    simp only [renderLoop, go_basic?, content]
    by_cases hasPending : proofState.pend > 0 <;>
      by_cases hasNewline : textValue.toList.any (· == '\n') <;>
      simp [hasPending, hasNewline, non_ws_append]
  | .verbatim textValue base =>
    simp only [renderLoop, go_basic?, content]
    exact wr_block_out proofState indent base textValue
  | .cat leftValue rightValue =>
    simp only [renderLoop, content]
    rw [go_content width maxPend rightValue indent flat _,
        go_content width maxPend leftValue indent flat proofState, List.append_assoc]
  | .line =>
    simp only [renderLoop, go_basic?, content]
    by_cases isFlatMode : flat <;> simp [isFlatMode, wr_out]
  | .softline =>
    simp only [renderLoop, go_basic?, content]
    by_cases isFlatMode : flat <;> simp [isFlatMode]
  | .hardline => simp [renderLoop, go_basic?, content]
  | .blank _ => simp [renderLoop, go_basic?, content]
  | .pad _ => simp [renderLoop, go_basic?, content]
  | .group document =>
    simp only [renderLoop, content]
    exact go_content width maxPend document indent _ proofState
  | .flatten document =>
    simp only [renderLoop, content]
    exact go_content width maxPend document indent true proofState
  | .nest amount document =>
    simp only [renderLoop, content]
    exact go_content width maxPend document _ flat proofState
  | .align document =>
    simp only [renderLoop, content]
    exact go_content width maxPend document
      (if proofState.pend > 0 then indent else proofState.col) flat proofState
  | .fillSep items =>
    simp only [renderLoop, content]
    exact goFill_content width maxPend items indent flat true proofState
  | .alignTable spec rows =>
    simp only [renderLoop, go_align_table, content]
    rw [emit_table_content]
    congr 1
    exact goCellsRows_content width maxPend rows indent spec.sep _
  | .align_or spec rows flatBody =>
    simp only [renderLoop, go_align_or, content]
    repeat' split
    all_goals first
      | exact go_content width maxPend flatBody indent true proofState
      | exact go_content width maxPend flatBody indent flat proofState
      | (rename_i gridCoherent
         rw [emit_table_content]
         congr 1
         simp only [Bool.and_eq_true, decide_eq_true_eq] at gridCoherent
         exact gridCoherent.2)

/-- Fill packing appends exactly the items' content. -/
theorem goFill_content (width maxPend : Nat) (items : List Doc) (indent : Nat)
    (flat first : Bool) (proofState : rst) :
    non_ws (goFill width maxPend items indent flat first proofState).out
    = non_ws proofState.out ++ contentList items := by
  match items with
  | [] => simp [goFill, contentList]
  | item :: items =>
    have hcell : non_ws (renderLoop width maxPend item indent true {}).out = content item := by
      have := go_content width maxPend item indent true {}
      simpa [non_ws] using this
    simp only [goFill, contentList]
    rw [goFill_content width maxPend items indent flat false _]
    by_cases is_first_item : first
    · simp [is_first_item, wr_out, hcell, List.append_assoc]
    · simp only [is_first_item]
      repeat' split
      all_goals simp_all [wr_out, hcell, List.append_assoc]

/-- One rendered, padded row carries exactly the row's content (cells joined
    by the separator's content), for ANY column widths. -/
theorem goCells_content (width maxPend : Nat) (proofChars : List Doc) (indent : Nat)
    (sep : String) (widths : List Nat) :
    non_ws (render_row_str sep widths (goCells width maxPend proofChars indent))
    = contentRow (non_ws sep) proofChars := by
  match proofChars with
  | [] => simp [goCells, render_row_str, contentRow]
  | [headChar] =>
    simp only [goCells, render_row_str, contentRow]
    have := go_content width maxPend headChar indent true {}
    simpa [non_ws] using this
  | headCharBinding :: headChar :: tailChars =>
    have hcell : non_ws (renderLoop width maxPend headCharBinding indent true {}).out = content headCharBinding := by
      have := go_content width maxPend headCharBinding indent true {}
      simpa [non_ws] using this
    have hrec := goCells_content width maxPend (headChar :: tailChars) indent sep (widths.drop 1)
    simp only [goCells] at hrec ⊢
    simp only [render_row_str]
    simp only [non_ws_append, non_ws_spaces, List.append_nil]
    rw [hrec]
    simp [hcell, List.append_assoc, contentRow]

theorem goCellsRows_content (width maxPend : Nat) (rows : List (List Doc)) (indent : Nat)
    (sep : String) (widths : List Nat) :
    ((goCellsRows width maxPend rows indent).map
      fun row => non_ws (render_row_str sep widths row)).flatten
    = contentRows (non_ws sep) rows := by
  match rows with
  | [] => simp [goCellsRows, contentRows]
  | row :: rows =>
    simp only [goCellsRows, List.map_cons, List.flatten_cons, contentRows]
    rw [goCellsRows_content width maxPend rows indent sep widths,
        goCells_content width maxPend row indent sep widths]

end

@[simp]
theorem non_ws_strip_trailing_ws
        (source : String)
        : non_ws (strip_trailing_ws source) = non_ws source := by
  simpa [non_ws, non_ws_l, whitespace_erased] using
    whitespace_erased_strip_trailing_ws source

/-- T1 at the public entry point, UNCONDITIONAL: for every doc, `render`'s
    output carries exactly the doc's content. -/
theorem render_content
        (style : Lean4Fmt.Style.Style)
        (proofDocument : Doc)
        : non_ws (render style proofDocument) = content proofDocument := by
  unfold render
  let proofState :=
    renderLoop style.layout.lineWidth (style.blankLines.maxConsecutive + 1) proofDocument 0 false {}
  have loopContent :=
    go_content style.layout.lineWidth (style.blankLines.maxConsecutive + 1) proofDocument 0 false {}
  change
    non_ws
        (if (strip_trailing_ws proofState.out).endsWith "\n"
          then strip_trailing_ws proofState.out
          else strip_trailing_ws proofState.out ++ "\n")
      = content proofDocument
  split
  · rw [non_ws_strip_trailing_ws]
    simpa [proofState] using loopContent
  · rw [non_ws_append, non_ws_strip_trailing_ws, non_ws_newline, List.append_nil]
    simpa [proofState] using loopContent

-- ── T2: flat exactness ────────────────────────────────────────────────────────

mutual

  /-- The one-line string flat rendering denotes (meaningful when `flatWidth`
    is `some`). -/
  def flatRender : Doc → String
    | .nil | .softline | .hardline | .blank _ | .pad _ => ""
    | .alignTable _ _ => ""
    | .text textValue => textValue
    | .textRaw textValue => textValue
    | .verbatim textValue _ => String.ofList (trim_end_ws textValue.toList)
    | .cat leftValue rightValue => flatRender leftValue ++ flatRender rightValue
    | .line => " "
    | .group document | .nest _ document | .align document | .flatten document =>
      flatRender document
    | .align_or _ _ flatBody => flatRender flatBody
    | .fillSep [] => ""
    | .fillSep (item :: items) => flatRender item ++ flatRenderSep items

  def flatRenderSep : List Doc → String
    | []            => ""
    | item :: items => " " ++ flatRender item ++ flatRenderSep items

end

mutual

  /-- `flatWidth` measures `flatRender` exactly. -/
  theorem flatRender_length
          (proofDocument : Doc)
          (proofCount : Nat)
          (hardWidth : flat_width proofDocument = some proofCount)
          : (flatRender proofDocument).length = proofCount := by
    match proofDocument with
    | .nil => simp_all [flat_width, flatRender]
    | .pad _ => simp_all [flat_width, flatRender]
    | .text textValue => simp_all [flat_width, flatRender]
    | .textRaw textValue =>
      simp only [flat_width] at hardWidth
      split at hardWidth
      · exact absurd hardWidth (by simp)
      · simp_all [flatRender]
    | .verbatim textValue _ =>
      simp only [flat_width] at hardWidth
      split at hardWidth
      · exact absurd hardWidth (by simp)
      · simp only [Option.some.injEq] at hardWidth
        simp [flatRender, ← hardWidth]
    | .cat leftValue rightValue =>
      simp only [flat_width] at hardWidth
      split at hardWidth
      · next leftWidth rightWidth leftWidthEq rightWidthEq =>
          simp only [Option.some.injEq] at hardWidth
          simp [flatRender, String.length_append, flatRender_length leftValue leftWidth leftWidthEq,
            flatRender_length rightValue rightWidth rightWidthEq, hardWidth]
      · exact absurd hardWidth (by simp)
    | .line =>
      simp only [flat_width, Option.some.injEq] at hardWidth
      rw [← hardWidth]; rfl
    | .softline => simp_all [flat_width, flatRender]
    | .hardline => simp_all [flat_width]
    | .blank _ => simp_all [flat_width]
    | .alignTable _ _ => simp_all [flat_width]
    | .group document =>
      simp only [flat_width] at hardWidth; simpa [flatRender] using flatRender_length document proofCount hardWidth
    | .nest _ document =>
      simp only [flat_width] at hardWidth; simpa [flatRender] using flatRender_length document proofCount hardWidth
    | .align document =>
      simp only [flat_width] at hardWidth; simpa [flatRender] using flatRender_length document proofCount hardWidth
    | .flatten document =>
      simp only [flat_width] at hardWidth; simpa [flatRender] using flatRender_length document proofCount hardWidth
    | .align_or _ _ flatBody =>
      simp only [flat_width] at hardWidth; simpa [flatRender] using flatRender_length flatBody proofCount hardWidth
    | .fillSep [] => simp_all [flat_width, flatRender]
    | .fillSep (item :: items) =>
      simp only [flat_width] at hardWidth
      split at hardWidth
      · next itemWidth restWidth itemWidthEq restWidthEq =>
          simp only [Option.some.injEq] at hardWidth
          simp [flatRender, String.length_append, flatRender_length item itemWidth itemWidthEq,
            flatRenderSep_length items restWidth restWidthEq, hardWidth]
      · exact absurd hardWidth (by simp)

  theorem flatRenderSep_length
          (proofIndents : List Doc)
          (proofCount : Nat)
          (hardWidth : flatWidthSep proofIndents = some proofCount)
          : (flatRenderSep proofIndents).length = proofCount := by
    match proofIndents with
    | [] => simp_all [flatWidthSep, flatRenderSep]
    | item :: items =>
      simp only [flatWidthSep] at hardWidth
      split at hardWidth
      · next itemWidth restWidth itemWidthEq restWidthEq =>
          simp only [Option.some.injEq] at hardWidth
          subst hardWidth
          simp [flatRenderSep, String.length_append, flatRender_length item itemWidth itemWidthEq,
            flatRenderSep_length items restWidth restWidthEq]
      · exact absurd hardWidth (by simp)

end

-- splitLines / trimEndWs facts for the verbatim case of T2

theorem split_lines_no_nl
        (proofChars : List Char)
        (noNewline : '\n' ∉ proofChars)
        : split_lines proofChars = [proofChars] := by
  induction proofChars with
  | nil => rfl
  | cons head tail inductionHypothesis =>
    have head_not_newline : head ≠ '\n' :=
      fun head_is_newline => noNewline (head_is_newline ▸ List.mem_cons_self ..)
    have tail_has_no_newline : '\n' ∉ tail :=
      fun newline_mem => noNewline (List.mem_cons_of_mem _ newline_mem)
    simp only [split_lines, inductionHypothesis tail_has_no_newline]
    simp [head_not_newline]

theorem mem_trim_end_ws
        {proofCharacter : Char}
        {proofChars : List Char}
        (trimmedMembership : proofCharacter ∈ trim_end_ws proofChars)
        : proofCharacter ∈ proofChars := by
  unfold trim_end_ws at trimmedMembership
  rw [List.mem_reverse] at trimmedMembership
  have :=
    (List.dropWhile_sublist (l := proofChars.reverse) (p := Char.isWhitespace)).subset
      trimmedMembership
  simpa [List.mem_reverse] using this

theorem drop_while_head_not
        {proofPredicate : Char → Bool}
        {proofList : List Char}
        {proofHead : Char}
        {proofTail : List Char}
        (dropEquation : proofList.dropWhile proofPredicate = proofHead :: proofTail)
        : proofPredicate proofHead = false := by
  induction proofList with
  | nil => simp [List.dropWhile] at dropEquation
  | cons head tail inductionHypothesis =>
    rw [List.dropWhile_cons] at dropEquation
    split at dropEquation
    · exact inductionHypothesis dropEquation
    · next hpa =>
        injection dropEquation with headEquation _
        subst headEquation
        simpa using hpa

/-- A nonempty trailing-trimmed line is not blank (its last char is non-ws). -/
theorem trim_end_ws_not_blank
        (proofChars : List Char)
        (hne : trim_end_ws proofChars ≠ [])
        : is_blank_line (trim_end_ws proofChars) = false := by
  unfold trim_end_ws at hne ⊢
  cases reversedTailEquation : proofChars.reverse.dropWhile Char.isWhitespace with
  | nil => simp [reversedTailEquation] at hne
  | cons head tail =>
    have head_not_whitespace : Char.isWhitespace head = false :=
      drop_while_head_not reversedTailEquation
    have head_not_space : head ≠ ' ' := fun head_is_space => by
      subst head_is_space
      simp at head_not_whitespace
    simp only [reversedTailEquation, is_blank_line]
    rw [Bool.eq_false_iff]
    intro hall
    have := (List.all_eq_true.mp hall) head (by simp)
    exact head_not_space (by simpa using this)

/-- The verbatim branch of flat rendering is exact once its width is known. -/
theorem flat_verbatim
        (width maxPend : Nat)
        (raw : String)
        (base indent proofCount : Nat)
        (proofState : rst)
        (hardWidth : flat_width (.verbatim raw base) = some proofCount)
        (positiveProof : proofState.pend = 0)
        : renderLoop width maxPend (.verbatim raw base) indent true proofState
            = ⟨proofState.out ++ flatRender (.verbatim raw base), proofState.col + proofCount, 0⟩ := by
  simp only [flat_width] at hardWidth
  split at hardWidth
  · exact absurd hardWidth (by simp)
  · next noNewline =>
      simp only [Option.some.injEq] at hardWidth
      have noNewlineMem : '\n' ∉ trim_end_ws raw.toList :=
        fun newlineMem =>
          noNewline (List.any_eq_true.mpr ⟨'\n', mem_trim_end_ws newlineMem, by simp⟩)
      have splitEquation : split_lines (trim_end_ws raw.toList) = [trim_end_ws raw.toList] :=
        split_lines_no_nl _ noNewlineMem
      cases trimmed : trim_end_ws raw.toList with
      | nil =>
        obtain ⟨output, column, pending⟩ := proofState
        simp only [rst.pend] at positiveProof
        subst pending
        have countZero : proofCount = 0 := by simpa [trimmed] using hardWidth.symm
        subst proofCount
        rw [trimmed] at splitEquation
        simp [renderLoop, go_basic?, wr_block, trimmed, splitEquation, is_blank_line, flatRender]
      | cons head tail =>
        have notBlank : is_blank_line (head :: tail) = false := by
          have := trim_end_ws_not_blank (proofChars := raw.toList) (by simp [trimmed])
          rwa [trimmed] at this
        obtain ⟨output, column, pending⟩ := proofState
        simp only [rst.pend] at positiveProof
        subst pending
        have widthEquality : (head :: tail).length = proofCount := by
          simpa [trimmed] using hardWidth
        rw [trimmed] at splitEquation
        simp [renderLoop, go_basic?, wr_block, trimmed, splitEquation, notBlank, wr_lines_m,
          writeResult, flatRender]
        simpa [Nat.add_comm] using widthEquality

/-- A pad node contributes width but emits no bytes in flat mode. -/
theorem go_flat_pad
        {width maxPend indent proofCount padCount : Nat}
        (proofState : rst)
        (hardWidth : flat_width (.pad padCount) = some proofCount)
        (positiveProof : proofState.pend = 0)
        : renderLoop width maxPend (.pad padCount) indent true proofState
            = ⟨proofState.out ++ flatRender (.pad padCount), proofState.col + proofCount, 0⟩ := by
  simp only [flat_width, Option.some.injEq] at hardWidth
  obtain ⟨output, column, pending⟩ := proofState
  subst positiveProof
  simp [renderLoop, flatRender, ← hardWidth]

/-- A newline-free raw text node appends its payload exactly in flat mode. -/
theorem flat_text_raw
        (width maxPend indent proofCount : Nat)
        (textValue : String)
        (proofState : rst)
        (hardWidth : flat_width (.textRaw textValue) = some proofCount)
        (positiveProof : proofState.pend = 0)
        : renderLoop width maxPend (.textRaw textValue) indent true proofState
            = ⟨proofState.out ++ flatRender (.textRaw textValue), proofState.col + proofCount, 0⟩ := by
  simp only [flat_width] at hardWidth
  split at hardWidth
  · exact absurd hardWidth (by simp)
  · next noNewline =>
      simp only [Option.some.injEq] at hardWidth
      obtain ⟨output, column, pending⟩ := proofState
      subst positiveProof
      simp [renderLoop, noNewline, flatRender, ← hardWidth]

/-- The empty document is the identity flat rendering step. -/
theorem flat_nil
        (width maxPend indent proofCount : Nat)
        (proofState : rst)
        (hardWidth : flat_width .nil = some proofCount)
        (positiveProof : proofState.pend = 0)
        : renderLoop width maxPend .nil indent true proofState
            = ⟨proofState.out ++ flatRender .nil, proofState.col + proofCount, 0⟩ := by
  simp only [flat_width, Option.some.injEq] at hardWidth
  obtain ⟨output, column, pending⟩ := proofState
  subst positiveProof
  simp [renderLoop, flatRender, ← hardWidth]

/-- A text node appends its newline-free payload exactly in flat mode. -/
theorem flat_text
        (width maxPend indent proofCount : Nat)
        (textValue : String)
        (proofState : rst)
        (hardWidth : flat_width (.text textValue) = some proofCount)
        (positiveProof : proofState.pend = 0)
        : renderLoop width maxPend (.text textValue) indent true proofState
            = ⟨proofState.out ++ flatRender (.text textValue), proofState.col + proofCount, 0⟩ := by
  simp only [flat_width, Option.some.injEq] at hardWidth
  obtain ⟨output, column, pending⟩ := proofState
  subst positiveProof
  simp [renderLoop, writeResult, flatRender, ← hardWidth]

mutual

  /-- **T2 — flat exactness (state form).** With no pending newlines, flat
      rendering appends `flatRender d` and advances by its exact width. -/
  theorem go_flat
          (width maxPend indent proofCount : Nat)
          (proofDocument : Doc)
          (proofState : rst)
          (hardWidth : flat_width proofDocument = some proofCount)
          (positiveProof : proofState.pend = 0)
          : renderLoop width maxPend proofDocument indent true proofState
              = ⟨proofState.out ++ flatRender proofDocument, proofState.col + proofCount, 0⟩ := by
    match proofDocument with
    | .nil => exact flat_nil width maxPend indent proofCount proofState hardWidth positiveProof
    | .text textValue =>
      exact flat_text width maxPend indent proofCount textValue proofState hardWidth positiveProof
    | .textRaw textValue =>
      exact
        flat_text_raw width maxPend indent proofCount textValue proofState hardWidth positiveProof
    | .verbatim raw base =>
      exact
        flat_verbatim width maxPend raw base indent proofCount proofState hardWidth positiveProof
    | .cat leftValue rightValue =>
      simp only [flat_width] at hardWidth; split at hardWidth
      · next leftWidth rightWidth leftWidthEq rightWidthEq =>
          simp only [Option.some.injEq] at hardWidth; simp only [renderLoop]
          rw [go_flat width maxPend indent leftWidth leftValue proofState leftWidthEq positiveProof,
            go_flat width maxPend indent rightWidth rightValue _ rightWidthEq rfl]
          simp [flatRender, String.append_assoc, ← hardWidth, Nat.add_assoc]
      · exact absurd hardWidth (by simp)
    | .line =>
      simp only [flat_width, Option.some.injEq] at hardWidth; obtain ⟨output, column, pending⟩ := proofState; subst positiveProof; simp [renderLoop, writeResult, flatRender, ← hardWidth]
    | .softline =>
      simp only [flat_width, Option.some.injEq] at hardWidth; obtain ⟨output, column, pending⟩ := proofState; subst positiveProof; simp [renderLoop, flatRender, ← hardWidth]
    | .hardline => simp [flat_width] at hardWidth
    | .blank _ => simp [flat_width] at hardWidth
    | .pad _ => exact go_flat_pad proofState hardWidth positiveProof
    | .alignTable _ _ => simp [flat_width] at hardWidth
    | .group document =>
      simp only [flat_width] at hardWidth; simp only [renderLoop, Bool.true_or]; simpa [flatRender] using go_flat width maxPend indent proofCount document proofState hardWidth positiveProof
    | .nest candidate document =>
      simp only [flat_width] at hardWidth; simp only [renderLoop]; simpa [flatRender] using go_flat width maxPend _ proofCount document proofState hardWidth positiveProof
    | .align document =>
      simp only [flat_width] at hardWidth; simp only [renderLoop, positiveProof, gt_iff_lt, Nat.lt_irrefl, if_false]; simpa [flatRender] using go_flat width maxPend proofState.col proofCount document proofState hardWidth positiveProof
    | .flatten document =>
      simp only [flat_width] at hardWidth; simp only [renderLoop]; simpa [flatRender] using go_flat width maxPend indent proofCount document proofState hardWidth positiveProof
    | .align_or _ _ flatBody =>
      simp only [flat_width] at hardWidth; simp only [renderLoop, if_true]; simpa [flatRender] using go_flat width maxPend indent proofCount flatBody proofState hardWidth positiveProof
    | .fillSep [] =>
      simp only [flat_width, Option.some.injEq] at hardWidth; obtain ⟨output, column, pending⟩ := proofState; subst positiveProof; simp [renderLoop, goFill, flatRender, ← hardWidth]
    | .fillSep (item :: items) =>
      simp only [flat_width] at hardWidth; split at hardWidth
      · next itemWidth restWidth itemWidthEq restWidthEq =>
          simp only [Option.some.injEq] at hardWidth; subst hardWidth
          obtain ⟨output, column, pending⟩ := proofState; subst positiveProof
          simp only [renderLoop, goFill]
          rw [go_flat width maxPend indent itemWidth item {} itemWidthEq rfl]
          have renderedLength : (flatRender item).length = itemWidth :=
            flatRender_length item itemWidth itemWidthEq
          simp only [writeResult, gt_iff_lt, Nat.lt_irrefl, if_false, reduceIte, if_true]
          rw [goFill_flat width maxPend items indent restWidth _ restWidthEq rfl]
          simp [flatRender, String.append_assoc, renderedLength, rst.mk.injEq]
          omega
      · exact absurd hardWidth (by simp)

  /-- Fill continuation in flat mode: each further item is ` item`, exactly. -/
  theorem goFill_flat
          (width maxPend : Nat)
          (proofIndents : List Doc)
          (indent : Nat)
          (proofCount : Nat)
          (proofState : rst)
          (hardWidth : flatWidthSep proofIndents = some proofCount)
          (positiveProof : proofState.pend = 0)
          : goFill width maxPend proofIndents indent true false proofState
              = ⟨proofState.out ++ flatRenderSep proofIndents, proofState.col + proofCount, 0⟩ := by
    match proofIndents with
    | [] =>
      simp only [flatWidthSep, Option.some.injEq] at hardWidth
      obtain ⟨output, column, pending⟩ := proofState
      subst positiveProof
      simp [goFill, flatRenderSep, ← hardWidth]
    | item :: items =>
      simp only [flatWidthSep] at hardWidth
      split at hardWidth
      · next itemWidth restWidth itemWidthEq restWidthEq =>
          simp only [Option.some.injEq] at hardWidth
          subst hardWidth
          obtain ⟨output, column, pending⟩ := proofState
          subst positiveProof
          simp only [goFill, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false, reduceIte]
          rw [go_flat width maxPend indent itemWidth item {} itemWidthEq rfl]
          have hlen : (flatRender item).length = itemWidth :=
            flatRender_length item itemWidth itemWidthEq
          simp only [writeResult, gt_iff_lt, Nat.lt_irrefl, if_false, reduceIte]
          rw [goFill_flat width maxPend items indent restWidth _ restWidthEq rfl]
          simp [flatRenderSep, String.append_assoc, String.length_append, hlen, rst.mk.injEq]
          omega
      · exact absurd hardWidth (by simp)

end

-- ── T2, one-line corollary ────────────────────────────────────────────────────

mutual
  /-- Well-formed docs: `.text` payloads are newline-free (the Doc contract —
    multi-line content must ride `textRaw`/`verbatim`). -/
  def WF : Doc → Prop
    | .text textValue => '\n' ∉ textValue.toList
    | .cat leftValue rightValue => WF leftValue ∧ WF rightValue
    | .group document | .nest _ document | .align document | .flatten document => WF document
    | .alignTable _ rows => WFRows rows
    | .align_or _ rows flatBody => WFRows rows ∧ WF flatBody
    | .fillSep items => WFList items
    | _ => True

  def WFList : List Doc → Prop
    | [] => True
    | document :: documents => WF document ∧ WFList documents

  def WFRows : List (List Doc) → Prop
    | []          => True
    | row :: rows => WFList row ∧ WFRows rows
end

mutual

  /-- A flattenable well-formed doc's flat rendering is a SINGLE line. -/
  theorem flatRender_noNl
          (proofDocument : Doc)
          (proofCount : Nat)
          (wellFormed : WF proofDocument)
          (hardWidth : flat_width proofDocument = some proofCount)
          : '\n' ∉ (flatRender proofDocument).toList := by
    match proofDocument with
    | .nil | .softline | .pad _ => simp [flatRender]
    | .hardline | .blank _ | .alignTable _ _ => simp [flat_width] at hardWidth
    | .text textValue => exact wellFormed
    | .textRaw textValue =>
      simp only [flat_width] at hardWidth
      split at hardWidth
      · exact absurd hardWidth (by simp)
      · next hnl =>
          simp only [flatRender]
          intro newlineMem
          exact hnl (List.any_eq_true.mpr ⟨'\n', newlineMem, by simp⟩)
    | .verbatim textValue _ =>
      simp only [flat_width] at hardWidth
      split at hardWidth
      · exact absurd hardWidth (by simp)
      · next hnl =>
          simp only [flatRender, String.toList_ofList]
          intro newlineMem
          exact hnl (List.any_eq_true.mpr ⟨'\n', mem_trim_end_ws newlineMem, by simp⟩)
    | .cat leftValue rightValue =>
      simp only [flat_width] at hardWidth
      split at hardWidth
      · next leftWidth rightWidth leftWidthEq rightWidthEq =>
          have ⟨leftWellFormed, rightWellFormed⟩ : WF leftValue ∧ WF rightValue := wellFormed
          simp only [flatRender, String.toList_append, List.mem_append]
          rintro (left_newline_mem | right_newline_mem)
          · exact flatRender_noNl leftValue leftWidth leftWellFormed leftWidthEq left_newline_mem
          · exact
              flatRender_noNl rightValue rightWidth rightWellFormed rightWidthEq right_newline_mem
      · exact absurd hardWidth (by simp)
    | .line => simp only [flatRender]; decide
    | .group document =>
      exact flatRender_noNl document proofCount wellFormed (by simpa [flat_width] using hardWidth)
    | .nest _ document =>
      exact flatRender_noNl document proofCount wellFormed (by simpa [flat_width] using hardWidth)
    | .align document =>
      exact flatRender_noNl document proofCount wellFormed (by simpa [flat_width] using hardWidth)
    | .flatten document =>
      exact flatRender_noNl document proofCount wellFormed (by simpa [flat_width] using hardWidth)
    | .align_or _ _ flatBody =>
      exact flatRender_noNl flatBody proofCount wellFormed.2 (by simpa [flat_width] using hardWidth)
    | .fillSep [] => simp [flatRender]
    | .fillSep (item :: items) =>
      simp only [flat_width] at hardWidth
      split at hardWidth
      · next itemWidth restWidth itemWidthEq restWidthEq =>
          have ⟨itemWellFormed, wis⟩ : WF item ∧ WFList items := wellFormed
          simp only [flatRender, String.toList_append, List.mem_append]
          rintro (item_newline_mem | rest_newline_mem)
          · exact flatRender_noNl item itemWidth itemWellFormed itemWidthEq item_newline_mem
          · exact flatRenderSep_noNl items restWidth wis restWidthEq rest_newline_mem
      · exact absurd hardWidth (by simp)

  theorem flatRenderSep_noNl
          (proofIndents : List Doc)
          (proofCount : Nat)
          (wellFormed : WFList proofIndents)
          (hardWidth : flatWidthSep proofIndents = some proofCount)
          : '\n' ∉ (flatRenderSep proofIndents).toList := by
    match proofIndents with
    | [] => simp [flatRenderSep]
    | item :: items =>
      simp only [flatWidthSep] at hardWidth
      split at hardWidth
      · next itemWidth restWidth itemWidthEq restWidthEq =>
          have ⟨itemWellFormed, wis⟩ : WF item ∧ WFList items := wellFormed
          simp only [flatRenderSep, String.toList_append, List.mem_append]
          rintro ((separator_newline_mem | item_newline_mem) | rest_newline_mem)
          · revert separator_newline_mem; decide
          · exact flatRender_noNl item itemWidth itemWellFormed itemWidthEq item_newline_mem
          · exact flatRenderSep_noNl items restWidth wis restWidthEq rest_newline_mem
      · exact absurd hardWidth (by simp)

end

/-- **T2 — flat exactness.** If `flatWidth d = some n`, flat rendering (from a
    clean line state) appends ONE newline-free string of length exactly `n`,
    advancing the column by exactly `n`. -/
theorem go_flat_exact
        (width maxPend : Nat)
        (proofDocument : Doc)
        (indent : Nat)
        (proofCount : Nat)
        (proofState : rst)
        (hardWidth : flat_width proofDocument = some proofCount)
        (positiveProof : proofState.pend = 0)
        (wellFormed : WF proofDocument)
        : ∃ proofText : String,
            renderLoop width maxPend proofDocument indent true proofState
                = ⟨proofState.out ++ proofText, proofState.col + proofCount, 0⟩
                ∧ proofText.length = proofCount
                ∧ '\n' ∉ proofText.toList :=
  ⟨
    flatRender proofDocument,
    go_flat width maxPend indent proofCount proofDocument proofState hardWidth positiveProof,
    flatRender_length proofDocument proofCount hardWidth,
    flatRender_noNl proofDocument proofCount wellFormed hardWidth
  ⟩

-- ── T3: seam content preservation ─────────────────────────────────────────────

@[simp]
theorem content_append
        (proofLeft proofRight : Doc)
        : content (proofLeft ++ proofRight) = content proofLeft ++ content proofRight :=
  rfl

theorem non_ws_l_nil_of_ws_line
        (proofList : List Char)
        (whitespaceLine : ws_line proofList)
        : non_ws_l proofList = [] := by
  simp only [non_ws_l, List.filter_eq_nil_iff]
  intro char charMem
  have := List.all_eq_true.mp whitespaceLine char charMem
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with rfl | rfl <;> decide

@[simp]
theorem content_seam_sep (proofRight : Nat) : content (seam_sep proofRight) = [] := by
  unfold seam_sep; split <;> simp [content]

/-- The seam's interior emission carries exactly the lines' content: blank
    lines denote nothing; each comment line's dedent (spaces only) and
    trailing trim (whitespace only) are content-invariant. -/
theorem seam_lines_content
        (base : Nat)
        (blanks : Nat)
        (proofLines : List (List Char))
        : content (seam_lines base blanks proofLines) = (proofLines.map non_ws_l).flatten := by
  induction proofLines generalizing blanks with
  | nil => simp [seam_lines]
  | cons line lines inductionHypothesis =>
    simp only [seam_lines, List.map_cons, List.flatten_cons]
    split
    · next line_is_whitespace =>
        rw [inductionHypothesis, non_ws_l_nil_of_ws_line line line_is_whitespace, List.nil_append]
    · simp only [content_append, content_seam_sep, List.nil_append, content]
      rw [inductionHypothesis, non_ws_of_list, non_ws_l_trim_end_ws, non_ws_l_dedent]

theorem flatten_map_drop_last
        (proofTransform : List Char → List Char)
        (proofTail : List (List Char))
        (rightProof : proofTail ≠ [])
        : (proofTail.map proofTransform).flatten
            = (proofTail.dropLast.map proofTransform).flatten
                ++ proofTransform (proofTail.getLast rightProof) := by
  calc (proofTail.map proofTransform).flatten
      = (((proofTail.dropLast ++ [proofTail.getLast rightProof]).map proofTransform)).flatten := by
        rw [List.dropLast_concat_getLast rightProof]
    _
        = (proofTail.dropLast.map proofTransform).flatten
            ++ proofTransform (proofTail.getLast rightProof) := by
          simp [List.map_append, List.flatten_append]

/-- **T3 — seam content preservation.** When the seam kit owns a leading
    trivia, the emitted separator doc carries EXACTLY the trivia's
    non-whitespace characters: every comment survives, in order, nothing is
    invented. (With `render_content`, the rendered seam bytes carry exactly
    the trivia's comment content.) -/
theorem leading_sep?_content
        (lead : String)
        (proofDocument : Doc)
        (separatorEquation : leading_sep? lead = some proofDocument)
        : content proofDocument = non_ws lead := by
  unfold leading_sep? at separatorEquation
  split at separatorEquation
  · exact absurd separatorEquation (by simp)
  split at separatorEquation
  · exact absurd separatorEquation (by simp)
  next firstSplitCondition secondSplitCondition =>
    simp only [Option.some.injEq] at separatorEquation
    subst separatorEquation
    rw [seam_lines_content]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false] at firstSplitCondition
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false] at secondSplitCondition
    have hchain := split_lines_non_ws lead.toList
    cases splitLinesEquation : split_lines lead.toList with
    | nil => exact absurd splitLinesEquation (split_lines_ne_nil lead.toList)
    | cons firstLine rest =>
      rw [splitLinesEquation] at hchain firstSplitCondition secondSplitCondition
      simp only [List.drop_succ_cons, List.drop_zero]
      simp only [List.headD_cons] at firstSplitCondition
      simp only [List.map_cons, List.flatten_cons,
        non_ws_l_nil_of_ws_line firstLine firstSplitCondition, List.nil_append] at hchain
      cases rest with
      | nil => simpa [non_ws] using hchain
      | cons secondLine remainingLines =>
        have hne : (secondLine :: remainingLines) ≠ [] := by simp
        have hlast :
            (firstLine :: secondLine :: remainingLines).getLastD []
                = (secondLine :: remainingLines).getLast hne := by
          simp [List.getLastD_eq_getLast?, List.getLast?_eq_getLast]
        rw [hlast] at secondSplitCondition
        rw [flatten_map_drop_last non_ws_l (secondLine :: remainingLines) hne,
          non_ws_l_nil_of_ws_line _ secondSplitCondition, List.append_nil] at hchain
        simpa [non_ws] using hchain

end Lean4Fmt.Doc.Proofs
