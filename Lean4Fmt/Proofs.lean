/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                            // LEAN4FMT // PROOFS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The laws of the extended Wadler/Leijen core (DESIGN_V2 §10), stated about
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

import Lean4Fmt.Doc.Core
import Lean4Fmt.Doc.Content
import Lean4Fmt.Doc.Render
import Lean4Fmt.Doc.Seam

namespace Lean4Fmt.Doc.Proofs

open Lean4Fmt.Doc

-- ── char/string plumbing ──────────────────────────────────────────────────────

@[simp]
theorem non_ws_l_nil : non_ws_l [] = [] := rfl

@[simp]
theorem non_ws_l_append (a b : List Char) : non_ws_l (a ++ b) = non_ws_l a ++ non_ws_l b := by
  simp [non_ws_l, List.filter_append]

@[simp]
theorem non_ws_append (a b : String) : non_ws (a ++ b) = non_ws a ++ non_ws b := by
  simp [non_ws, String.toList_append]

@[simp]
theorem non_ws_of_list (l : List Char) : non_ws (String.ofList l) = non_ws_l l := by
  simp [non_ws, String.toList_ofList]

@[simp]
theorem of_list_length (l : List Char) : (String.ofList l).length = l.length := by
  have h := congrArg List.length (String.toList_ofList (l := l))
  simpa [String.length_toList] using h

@[simp]
theorem space_length : (" " : String).length = 1 := rfl

@[simp]
theorem non_ws_spaces (n : Nat) : non_ws (spaces n) = [] := by
  simp only [spaces, non_ws_of_list, non_ws_l]
  induction n with
  | zero => rfl
  | succ predecessor inductionHypothesis => simpa [List.replicate_succ] using inductionHypothesis

@[simp]
theorem non_ws_newlines (n : Nat) : non_ws (newlines n) = [] := by
  simp only [newlines, non_ws_of_list, non_ws_l]
  induction n with
  | zero => rfl
  | succ predecessor inductionHypothesis => simpa [List.replicate_succ] using inductionHypothesis

@[simp]
theorem non_ws_empty : non_ws "" = [] := rfl

@[simp]
theorem non_ws_space : non_ws " " = [] := by decide

@[simp]
theorem non_ws_newline : non_ws "\n" = [] := by decide

theorem non_ws_l_nil_of_spaces (cs : List Char) (h : cs.all (· == ' ')) : non_ws_l cs = [] := by
  simp only [non_ws_l, List.filter_eq_nil_iff]
  intro char charMem
  have : char = ' ' := by simpa using List.all_eq_true.mp h char charMem
  subst this
  decide

theorem non_ws_l_drop_while_space
        (cs : List Char)
        : non_ws_l (cs.dropWhile (· == ' ')) = non_ws_l cs := by
  induction cs with
  | nil => rfl
  | cons head tail inductionHypothesis =>
    by_cases char_is_space : head = ' '
    · subst char_is_space
      have : (!(' ' : Char).isWhitespace) = false := by decide
      simpa [List.dropWhile_cons, non_ws_l, List.filter_cons, this] using inductionHypothesis
    · simp [List.dropWhile_cons, char_is_space]

theorem non_ws_l_drop_while_ws
        (cs : List Char)
        : non_ws_l (cs.dropWhile Char.isWhitespace) = non_ws_l cs := by
  induction cs with
  | nil => rfl
  | cons head tail inductionHypothesis =>
    by_cases char_is_whitespace : head.isWhitespace
    · simpa [List.dropWhile_cons, non_ws_l, List.filter_cons, char_is_whitespace] using inductionHypothesis
    · simp [List.dropWhile_cons, char_is_whitespace]

theorem non_ws_l_reverse (cs : List Char) : non_ws_l cs.reverse = (non_ws_l cs).reverse := by
  simp [non_ws_l, List.filter_reverse]

theorem non_ws_l_trim_end_ws (cs : List Char) : non_ws_l (trim_end_ws cs) = non_ws_l cs := by
  unfold trim_end_ws
  rw [non_ws_l_reverse, non_ws_l_drop_while_ws, non_ws_l_reverse, List.reverse_reverse]

-- ── splitLines / wrBlock plumbing ─────────────────────────────────────────────

theorem split_lines_ne_nil (cs : List Char) : split_lines cs ≠ [] := by
  cases cs with
  | nil => simp [split_lines]
  | cons head tail =>
    simp only [split_lines]
    repeat' split
    all_goals simp

/-- Line-splitting loses only the '\n' separators — whitespace. -/
theorem split_lines_non_ws
        (cs : List Char)
        : ((split_lines cs).map non_ws_l).flatten = non_ws_l cs := by
  induction cs with
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
        (ls : List (List Char))
        : (((ls.dropWhile is_blank_line).map non_ws_l)).flatten = (ls.map non_ws_l).flatten := by
  induction ls with
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
        (st : rst)
        (indent : Nat)
        (s : String)
        : non_ws (writeResult st indent s).out = non_ws st.out ++ non_ws s := by
  unfold writeResult
  by_cases has_pending_lines : st.pend > 0 <;> simp [has_pending_lines]

/-- Dedenting drops only spaces — the content of a continuation line survives
    its re-anchoring intact (the wrBlock content-eater made impossible). -/
theorem non_ws_l_dedent (base : Nat) (l : List Char) : non_ws_l (dedent base l) = non_ws_l l := by
  unfold dedent
  split
  · next dedentCondition =>
      simp only [Bool.and_eq_true] at dedentCondition
      have h2 : non_ws_l l = non_ws_l (l.take base) ++ non_ws_l (l.drop base) := by
        rw [← non_ws_l_append, List.take_append_drop]
      rw [h2, non_ws_l_nil_of_spaces _ dedentCondition.2, List.nil_append]
  · exact non_ws_l_drop_while_space l

theorem wr_line_out
        (st : rst)
        (indent base : Nat)
        (l : List Char)
        : non_ws (wr_line st indent base l).out = non_ws st.out ++ non_ws_l l := by
  unfold wr_line
  split
  · next dedentIsEmpty =>
      have h0 : dedent base l = [] := by simpa [List.isEmpty_iff] using dedentIsEmpty
      have hl : non_ws_l l = [] := by rw [← non_ws_l_dedent base l, h0]; rfl
      simp [hl]
  · simp [wr_out, non_ws_l_dedent]

theorem wr_lines_out
        (indent base : Nat)
        (ls : List (List Char))
        (st : rst)
        : non_ws (wr_lines indent base ls st).out = non_ws st.out ++ (ls.map non_ws_l).flatten := by
  induction ls generalizing st with
  | nil => simp [wr_lines]
  | cons line lines inductionHypothesis =>
    simp [wr_lines, inductionHypothesis, wr_line_out, List.append_assoc]

/-- The block writer preserves content exactly: trimming, blank-line dropping,
    and dedenting all touch only whitespace (the spaces-only dedent guard is
    what makes this true — it was a latent content-eater before this law). -/
theorem wr_block_out
        (st : rst)
        (indent base : Nat)
        (raw : String)
        : non_ws (wr_block st indent base raw).out = non_ws st.out ++ non_ws raw := by
  have hchain :
      (((split_lines (trim_end_ws raw.toList)).dropWhile is_blank_line).map non_ws_l).flatten
          = non_ws_l raw.toList := by
    rw [flatten_map_drop_blank, split_lines_non_ws, non_ws_l_trim_end_ws]
  unfold wr_block
  cases linesEquation : (split_lines (trim_end_ws raw.toList)).dropWhile is_blank_line with
  | nil =>
    rw [linesEquation] at hchain
    simp only [List.map_nil, List.flatten_nil] at hchain
    show non_ws st.out = non_ws st.out ++ non_ws raw
    rw [show non_ws raw = non_ws_l raw.toList from rfl, ← hchain, List.append_nil]
  | cons line rest =>
    rw [linesEquation] at hchain
    simp only [List.map_cons, List.flatten_cons] at hchain
    rw [wr_lines_out, wr_out, non_ws_of_list, List.append_assoc, hchain]
    rfl

-- ── T1: content preservation ──────────────────────────────────────────────────

/-- The table-emission fold appends exactly the padded rows' content. -/
theorem emit_table_content
        (maxPend indent : Nat)
        (sep : String)
        (widths : List Nat)
        (strRows : List (List String))
        (st : rst)
        : non_ws (emit_table maxPend indent sep widths strRows st).out
            = non_ws st.out
                ++ ((strRows.map fun row => non_ws (render_row_str sep widths row)).flatten) := by
  suffices table_content : ∀ (first : Bool) (st : rst),
      non_ws ((strRows.foldl (fun (progress : rst × Bool) row =>
        let state :=
          if progress.2 then
            progress.1
          else
            { progress.1 with pend := Nat.min (progress.1.pend + 1) maxPend }
        (writeResult state indent (render_row_str sep widths row), false)) (st, first)).1).out
      = non_ws st.out
          ++ ((strRows.map fun row => non_ws (render_row_str sep widths row)).flatten) by
    exact table_content true st
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
theorem go_content (width maxPend : Nat) (d : Doc) (indent : Nat) (flat : Bool)
    (st : rst) :
    non_ws (renderLoop width maxPend d indent flat st).out = non_ws st.out ++ content d := by
  match d with
  | .nil => simp [renderLoop, content]
  | .text textValue => simp [renderLoop, content, wr_out]
  | .textRaw textValue =>
    simp only [renderLoop, content]
    repeat' split
    all_goals simp
  | .verbatim textValue rightValue =>
    simp only [renderLoop, content]
    exact wr_block_out st indent rightValue textValue
  | .cat leftValue rightValue =>
    simp only [renderLoop, content]
    rw [go_content width maxPend rightValue indent flat _,
        go_content width maxPend leftValue indent flat st, List.append_assoc]
  | .line =>
    simp only [renderLoop, content]
    by_cases is_flat_mode : flat <;> simp [is_flat_mode, wr_out]
  | .softline =>
    simp only [renderLoop, content]
    by_cases is_flat_mode : flat <;> simp [is_flat_mode]
  | .hardline => simp [renderLoop, content]
  | .blank _ => simp [renderLoop, content]
  | .group document =>
    simp only [renderLoop, content]
    exact go_content width maxPend document indent _ st
  | .flatten document =>
    simp only [renderLoop, content]
    exact go_content width maxPend document indent true st
  | .nest count document =>
    simp only [renderLoop, content]
    exact go_content width maxPend document _ flat st
  | .align document =>
    simp only [renderLoop, content]
    exact go_content width maxPend document st.col flat st
  | .fillSep items =>
    simp only [renderLoop, content]
    exact goFill_content width maxPend items indent flat true st
  | .alignTable spec rows =>
    simp only [renderLoop, content]
    rw [emit_table_content]
    congr 1
    exact goCellsRows_content width maxPend rows indent spec.sep _
  | .align_or spec rows flatBody =>
    simp only [renderLoop, content]
    repeat' split
    all_goals first
      | exact go_content width maxPend flatBody indent true st
      | exact go_content width maxPend flatBody indent flat st
      | (rename_i hgrid
         rw [emit_table_content]
         congr 1
         simp only [Bool.and_eq_true, decide_eq_true_eq] at hgrid
         exact hgrid.2)

/-- Fill packing appends exactly the items' content. -/
theorem goFill_content (width maxPend : Nat) (items : List Doc) (indent : Nat)
    (flat first : Bool) (st : rst) :
    non_ws (goFill width maxPend items indent flat first st).out
    = non_ws st.out ++ contentList items := by
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
theorem goCells_content (width maxPend : Nat) (cs : List Doc) (indent : Nat)
    (sep : String) (widths : List Nat) :
    non_ws (render_row_str sep widths (goCells width maxPend cs indent))
    = contentRow (non_ws sep) cs := by
  match cs with
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

/-- T1 at the public entry point, UNCONDITIONAL: for every doc, `render`'s
    output carries exactly the doc's content. -/
theorem render_content
        (style : Lean4Fmt.Style.Style)
        (d : Doc)
        : non_ws (render style d) = content d := by
  have h := go_content style.layout.lineWidth (style.blankLines.maxConsecutive + 1) d 0 false {}
  simp only [render]
  by_cases output_ends_with_newline : (renderLoop style.layout.lineWidth (style.blankLines.maxConsecutive + 1)
      d 0 false {}).out.endsWith "\n"
  · simp only [output_ends_with_newline, if_true]
    simpa [non_ws] using h
  · simp only [output_ends_with_newline, if_false, Bool.false_eq_true]
    rw [non_ws_append]
    have hnl : non_ws "\n" = [] := by decide
    rw [hnl, List.append_nil]
    simpa [non_ws] using h

-- ── T2: flat exactness ────────────────────────────────────────────────────────

mutual

  /-- The one-line string flat rendering denotes (meaningful when `flatWidth`
    is `some`). -/
  def flatRender : Doc → String
    | .nil | .softline | .hardline | .blank _ => ""
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
          (d : Doc)
          (n : Nat)
          (hw : flat_width d = some n)
          : (flatRender d).length = n := by
    match d with
    | .nil => simp_all [flat_width, flatRender]
    | .text textValue => simp_all [flat_width, flatRender]
    | .textRaw textValue =>
      simp only [flat_width] at hw
      split at hw
      · exact absurd hw (by simp)
      · simp_all [flatRender]
    | .verbatim textValue _ =>
      simp only [flat_width] at hw
      split at hw
      · exact absurd hw (by simp)
      · simp only [Option.some.injEq] at hw
        simp [flatRender, ← hw]
    | .cat leftValue rightValue =>
      simp only [flat_width] at hw
      split at hw
      · next leftWidth rightWidth leftWidthEq rightWidthEq =>
          simp only [Option.some.injEq] at hw
          simp [flatRender, String.length_append, flatRender_length leftValue leftWidth leftWidthEq,
            flatRender_length rightValue rightWidth rightWidthEq, hw]
      · exact absurd hw (by simp)
    | .line =>
      simp only [flat_width, Option.some.injEq] at hw
      rw [← hw]; rfl
    | .softline => simp_all [flat_width, flatRender]
    | .hardline => simp_all [flat_width]
    | .blank _ => simp_all [flat_width]
    | .alignTable _ _ => simp_all [flat_width]
    | .group document =>
      simp only [flat_width] at hw; simpa [flatRender] using flatRender_length document n hw
    | .nest _ document =>
      simp only [flat_width] at hw; simpa [flatRender] using flatRender_length document n hw
    | .align document =>
      simp only [flat_width] at hw; simpa [flatRender] using flatRender_length document n hw
    | .flatten document =>
      simp only [flat_width] at hw; simpa [flatRender] using flatRender_length document n hw
    | .align_or _ _ flatBody =>
      simp only [flat_width] at hw; simpa [flatRender] using flatRender_length flatBody n hw
    | .fillSep [] => simp_all [flat_width, flatRender]
    | .fillSep (item :: items) =>
      simp only [flat_width] at hw
      split at hw
      · next itemWidth restWidth itemWidthEq restWidthEq =>
          simp only [Option.some.injEq] at hw
          simp [flatRender, String.length_append, flatRender_length item itemWidth itemWidthEq,
            flatRenderSep_length items restWidth restWidthEq, hw]
      · exact absurd hw (by simp)

  theorem flatRenderSep_length
          (is : List Doc)
          (n : Nat)
          (hw : flatWidthSep is = some n)
          : (flatRenderSep is).length = n := by
    match is with
    | [] => simp_all [flatWidthSep, flatRenderSep]
    | item :: items =>
      simp only [flatWidthSep] at hw
      split at hw
      · next itemWidth restWidth itemWidthEq restWidthEq =>
          simp only [Option.some.injEq] at hw
          subst hw
          simp [flatRenderSep, String.length_append, flatRender_length item itemWidth itemWidthEq,
            flatRenderSep_length items restWidth restWidthEq]
      · exact absurd hw (by simp)

end

-- splitLines / trimEndWs facts for the verbatim case of T2

theorem split_lines_no_nl (cs : List Char) (h : '\n' ∉ cs) : split_lines cs = [cs] := by
  induction cs with
  | nil => rfl
  | cons head tail inductionHypothesis =>
    have head_not_newline : head ≠ '\n' :=
      fun head_is_newline => h (head_is_newline ▸ List.mem_cons_self ..)
    have tail_has_no_newline : '\n' ∉ tail :=
      fun newline_mem => h (List.mem_cons_of_mem _ newline_mem)
    simp only [split_lines, inductionHypothesis tail_has_no_newline]
    simp [head_not_newline]

theorem mem_trim_end_ws {c : Char} {cs : List Char} (h : c ∈ trim_end_ws cs) : c ∈ cs := by
  unfold trim_end_ws at h
  rw [List.mem_reverse] at h
  have := (List.dropWhile_sublist (l := cs.reverse) (p := Char.isWhitespace)).subset h
  simpa [List.mem_reverse] using this

theorem drop_while_head_not
        {p : Char → Bool}
        {l : List Char}
        {y : Char}
        {ys : List Char}
        (h : l.dropWhile p = y :: ys)
        : p y = false := by
  induction l with
  | nil => simp [List.dropWhile] at h
  | cons head tail inductionHypothesis =>
    rw [List.dropWhile_cons] at h
    split at h
    · exact inductionHypothesis h
    · next hpa =>
        injection h with headEquation _
        subst headEquation
        simpa using hpa

/-- A nonempty trailing-trimmed line is not blank (its last char is non-ws). -/
theorem trim_end_ws_not_blank
        (cs : List Char)
        (hne : trim_end_ws cs ≠ [])
        : is_blank_line (trim_end_ws cs) = false := by
  unfold trim_end_ws at hne ⊢
  cases reversedTailEquation : cs.reverse.dropWhile Char.isWhitespace with
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
theorem go_flat_verbatim
        (width maxPend : Nat)
        (raw : String)
        (base indent n : Nat)
        (st : rst)
        (hw : flat_width (.verbatim raw base) = some n)
        (hp : st.pend = 0)
        : renderLoop width maxPend (.verbatim raw base) indent true st
            = { out := st.out ++ flatRender (.verbatim raw base), col := st.col + n, pend := 0 } := by
  simp only [flat_width] at hw
  split at hw
  · exact absurd hw (by simp)
  · next no_newline =>
      simp only [Option.some.injEq] at hw
      have no_newline_mem : '\n' ∉ trim_end_ws raw.toList :=
        fun newline_mem =>
          no_newline (List.any_eq_true.mpr ⟨'\n', mem_trim_end_ws newline_mem, by simp⟩)
      simp only [renderLoop, wr_block, split_lines_no_nl _ no_newline_mem]
      cases trimmed : trim_end_ws raw.toList with
      | nil =>
        rw [trimmed] at hw
        obtain ⟨out, column, pending⟩ := st; subst hp
        simp_all [is_blank_line, flatRender, trimmed]
      | cons head tail =>
        have not_blank : is_blank_line (head :: tail) = false := by
          have := trim_end_ws_not_blank (cs := raw.toList) (by simp [trimmed])
          rwa [trimmed] at this
        rw [trimmed] at hw
        obtain ⟨out, column, pending⟩ := st; subst hp
        simp_all [List.dropWhile_cons, wr_lines, writeResult, flatRender, trimmed]
        omega

mutual

  /-- **T2 — flat exactness (state form).** In flat mode with no pending
    newlines, rendering a doc of known flat width appends EXACTLY
    `flatRender d` and advances the column by exactly `n`. This is the law
    that makes `group`'s fit check (`effCol + flatWidth ≤ width`) an oracle:
    what it measures is precisely what gets emitted. -/
  theorem go_flat
          (width maxPend indent n : Nat)
          (d : Doc)
          (st : rst)
          (hw : flat_width d = some n)
          (hp : st.pend = 0)
          : renderLoop width maxPend d indent true st
              = { out := st.out ++ flatRender d, col := st.col + n, pend := 0 } := by
    match d with
    | .nil =>
      simp only [flat_width, Option.some.injEq] at hw; obtain ⟨output, column, pending⟩ := st; subst hp; simp [renderLoop, flatRender, ← hw]
    | .text textValue =>
      simp only [flat_width, Option.some.injEq] at hw; obtain ⟨output, column, pending⟩ := st; subst hp; simp [renderLoop, writeResult, flatRender, ← hw]
    | .textRaw textValue =>
      simp only [flat_width] at hw; split at hw
      · exact absurd hw (by simp)
      · next hnl =>
          simp only [Option.some.injEq] at hw; obtain ⟨output, column, pending⟩ := st; subst hp; simp [renderLoop, hnl, flatRender, ← hw]
    | .verbatim raw base => exact go_flat_verbatim width maxPend raw base indent n st hw hp
    | .cat leftValue rightValue =>
      simp only [flat_width] at hw; split at hw
      · next leftWidth rightWidth leftWidthEq rightWidthEq =>
          simp only [Option.some.injEq] at hw; simp only [renderLoop]
          rw [go_flat width maxPend leftValue indent leftWidth st leftWidthEq hp,
            go_flat width maxPend rightValue indent rightWidth _ rightWidthEq rfl]
          simp [flatRender, String.append_assoc, ← hw, Nat.add_assoc]
      · exact absurd hw (by simp)
    | .line =>
      simp only [flat_width, Option.some.injEq] at hw; obtain ⟨output, column, pending⟩ := st; subst hp; simp [renderLoop, writeResult, flatRender, ← hw]
    | .softline =>
      simp only [flat_width, Option.some.injEq] at hw; obtain ⟨output, column, pending⟩ := st; subst hp; simp [renderLoop, flatRender, ← hw]
    | .hardline => simp [flat_width] at hw
    | .blank _ => simp [flat_width] at hw
    | .alignTable _ _ => simp [flat_width] at hw
    | .group document =>
      simp only [flat_width] at hw; simp only [renderLoop, Bool.true_or]; simpa [flatRender] using go_flat width maxPend document indent n st hw hp
    | .nest candidate document =>
      simp only [flat_width] at hw; simp only [renderLoop]; simpa [flatRender] using go_flat width maxPend document _ n st hw hp
    | .align document =>
      simp only [flat_width] at hw; simp only [renderLoop]; simpa [flatRender] using go_flat width maxPend document st.col n st hw hp
    | .flatten document =>
      simp only [flat_width] at hw; simp only [renderLoop]; simpa [flatRender] using go_flat width maxPend document indent n st hw hp
    | .align_or _ _ flatBody =>
      simp only [flat_width] at hw; simp only [renderLoop, if_true]; simpa [flatRender] using go_flat width maxPend flatBody indent n st hw hp
    | .fillSep [] =>
      simp only [flat_width, Option.some.injEq] at hw; obtain ⟨output, column, pending⟩ := st; subst hp; simp [renderLoop, goFill, flatRender, ← hw]
    | .fillSep (item :: items) =>
      simp only [flat_width] at hw; split at hw
      · next itemWidth restWidth itemWidthEq restWidthEq =>
          simp only [Option.some.injEq] at hw; subst hw
          obtain ⟨output, column, pending⟩ := st; subst hp
          simp only [renderLoop, goFill]
          rw [go_flat width maxPend item indent itemWidth {} itemWidthEq rfl]
          have renderedLength : (flatRender item).length = itemWidth :=
            flatRender_length item itemWidth itemWidthEq
          simp only [writeResult, gt_iff_lt, Nat.lt_irrefl, if_false, reduceIte, if_true]
          rw [goFill_flat width maxPend items indent restWidth _ restWidthEq rfl]
          simp [flatRender, String.append_assoc, renderedLength, rst.mk.injEq]
          omega
      · exact absurd hw (by simp)

  /-- Fill continuation in flat mode: each further item is ` item`, exactly. -/
  theorem goFill_flat
          (width maxPend : Nat)
          (is : List Doc)
          (indent : Nat)
          (n : Nat)
          (st : rst)
          (hw : flatWidthSep is = some n)
          (hp : st.pend = 0)
          : goFill width maxPend is indent true false st
              = { out := st.out ++ flatRenderSep is, col := st.col + n, pend := 0 } := by
    match is with
    | [] =>
      simp only [flatWidthSep, Option.some.injEq] at hw
      obtain ⟨output, column, pending⟩ := st
      subst hp
      simp [goFill, flatRenderSep, ← hw]
    | item :: items =>
      simp only [flatWidthSep] at hw
      split at hw
      · next itemWidth restWidth itemWidthEq restWidthEq =>
          simp only [Option.some.injEq] at hw
          subst hw
          obtain ⟨output, column, pending⟩ := st
          subst hp
          simp only [goFill, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false, reduceIte]
          rw [go_flat width maxPend item indent itemWidth {} itemWidthEq rfl]
          have hlen : (flatRender item).length = itemWidth :=
            flatRender_length item itemWidth itemWidthEq
          simp only [writeResult, gt_iff_lt, Nat.lt_irrefl, if_false, reduceIte]
          rw [goFill_flat width maxPend items indent restWidth _ restWidthEq rfl]
          simp [flatRenderSep, String.append_assoc, String.length_append, hlen, rst.mk.injEq]
          omega
      · exact absurd hw (by simp)

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
          (d : Doc)
          (n : Nat)
          (wf : WF d)
          (hw : flat_width d = some n)
          : '\n' ∉ (flatRender d).toList := by
    match d with
    | .nil | .softline => simp [flatRender]
    | .hardline | .blank _ | .alignTable _ _ => simp [flat_width] at hw
    | .text textValue => exact wf
    | .textRaw textValue =>
      simp only [flat_width] at hw
      split at hw
      · exact absurd hw (by simp)
      · next hnl =>
          simp only [flatRender]
          intro newlineMem
          exact hnl (List.any_eq_true.mpr ⟨'\n', newlineMem, by simp⟩)
    | .verbatim textValue _ =>
      simp only [flat_width] at hw
      split at hw
      · exact absurd hw (by simp)
      · next hnl =>
          simp only [flatRender, String.toList_ofList]
          intro newlineMem
          exact hnl (List.any_eq_true.mpr ⟨'\n', mem_trim_end_ws newlineMem, by simp⟩)
    | .cat leftValue rightValue =>
      simp only [flat_width] at hw
      split at hw
      · next leftWidth rightWidth leftWidthEq rightWidthEq =>
          have ⟨wa, wb⟩ : WF leftValue ∧ WF rightValue := wf
          simp only [flatRender, String.toList_append, List.mem_append]
          rintro (left_newline_mem | right_newline_mem)
          · exact flatRender_noNl leftValue leftWidth wa leftWidthEq left_newline_mem
          · exact flatRender_noNl rightValue rightWidth wb rightWidthEq right_newline_mem
      · exact absurd hw (by simp)
    | .line => simp only [flatRender]; decide
    | .group document => exact flatRender_noNl document n wf (by simpa [flat_width] using hw)
    | .nest _ document => exact flatRender_noNl document n wf (by simpa [flat_width] using hw)
    | .align document => exact flatRender_noNl document n wf (by simpa [flat_width] using hw)
    | .flatten document => exact flatRender_noNl document n wf (by simpa [flat_width] using hw)
    | .align_or _ _ flatBody =>
      exact flatRender_noNl flatBody n wf.2 (by simpa [flat_width] using hw)
    | .fillSep [] => simp [flatRender]
    | .fillSep (item :: items) =>
      simp only [flat_width] at hw
      split at hw
      · next itemWidth restWidth itemWidthEq restWidthEq =>
          have ⟨wi, wis⟩ : WF item ∧ WFList items := wf
          simp only [flatRender, String.toList_append, List.mem_append]
          rintro (item_newline_mem | rest_newline_mem)
          · exact flatRender_noNl item itemWidth wi itemWidthEq item_newline_mem
          · exact flatRenderSep_noNl items restWidth wis restWidthEq rest_newline_mem
      · exact absurd hw (by simp)

  theorem flatRenderSep_noNl
          (is : List Doc)
          (n : Nat)
          (wf : WFList is)
          (hw : flatWidthSep is = some n)
          : '\n' ∉ (flatRenderSep is).toList := by
    match is with
    | [] => simp [flatRenderSep]
    | item :: items =>
      simp only [flatWidthSep] at hw
      split at hw
      · next itemWidth restWidth itemWidthEq restWidthEq =>
          have ⟨wi, wis⟩ : WF item ∧ WFList items := wf
          simp only [flatRenderSep, String.toList_append, List.mem_append]
          rintro ((separator_newline_mem | item_newline_mem) | rest_newline_mem)
          · revert separator_newline_mem; decide
          · exact flatRender_noNl item itemWidth wi itemWidthEq item_newline_mem
          · exact flatRenderSep_noNl items restWidth wis restWidthEq rest_newline_mem
      · exact absurd hw (by simp)

end

/-- **T2 — flat exactness.** If `flatWidth d = some n`, flat rendering (from a
    clean line state) appends ONE newline-free string of length exactly `n`,
    advancing the column by exactly `n`. -/
theorem go_flat_exact
        (width maxPend : Nat)
        (d : Doc)
        (indent : Nat)
        (n : Nat)
        (st : rst)
        (hw : flat_width d = some n)
        (hp : st.pend = 0)
        (wf : WF d)
        : ∃ s : String,
            renderLoop width maxPend d indent true st
                = { out := st.out ++ s, col := st.col + n, pend := 0 }
                ∧ s.length = n
                ∧ '\n' ∉ s.toList :=
  ⟨
    flatRender d,
    go_flat width maxPend d indent n st hw hp,
    flatRender_length d n hw,
    flatRender_noNl d n wf hw
  ⟩

-- ── T3: seam content preservation ─────────────────────────────────────────────

@[simp]
theorem content_append (a b : Doc) : content (a ++ b) = content a ++ content b := rfl

theorem non_ws_l_nil_of_ws_line (l : List Char) (h : ws_line l) : non_ws_l l = [] := by
  simp only [non_ws_l, List.filter_eq_nil_iff]
  intro char charMem
  have := List.all_eq_true.mp h char charMem
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with rfl | rfl <;> decide

@[simp]
theorem content_seam_sep (b : Nat) : content (seam_sep b) = [] := by
  unfold seam_sep; split <;> simp [content]

/-- The seam's interior emission carries exactly the lines' content: blank
    lines denote nothing; each comment line's dedent (spaces only) and
    trailing trim (whitespace only) are content-invariant. -/
theorem seam_lines_content
        (base : Nat)
        (blanks : Nat)
        (ls : List (List Char))
        : content (seam_lines base blanks ls) = (ls.map non_ws_l).flatten := by
  induction ls generalizing blanks with
  | nil => simp [seam_lines]
  | cons line lines inductionHypothesis =>
    simp only [seam_lines, List.map_cons, List.flatten_cons]
    split
    · next line_is_whitespace =>
        rw [inductionHypothesis, non_ws_l_nil_of_ws_line line line_is_whitespace, List.nil_append]
    · simp only [content_append, content_seam_sep, List.nil_append, content]
      rw [inductionHypothesis, non_ws_of_list, non_ws_l_trim_end_ws, non_ws_l_dedent]

theorem flatten_map_drop_last
        (f : List Char → List Char)
        (ys : List (List Char))
        (hy : ys ≠ [])
        : (ys.map f).flatten = (ys.dropLast.map f).flatten ++ f (ys.getLast hy) := by
  calc (ys.map f).flatten = (((ys.dropLast ++ [ys.getLast hy]).map f)).flatten := by
        rw [List.dropLast_concat_getLast hy]
    _ = (ys.dropLast.map f).flatten ++ f (ys.getLast hy) := by
          simp [List.map_append, List.flatten_append]

/-- **T3 — seam content preservation.** When the seam kit owns a leading
    trivia, the emitted separator doc carries EXACTLY the trivia's
    non-whitespace characters: every comment survives, in order, nothing is
    invented. (With `render_content`, the rendered seam bytes carry exactly
    the trivia's comment content.) -/
theorem leading_sep?_content
        (lead : String)
        (d : Doc)
        (h : leading_sep? lead = some d)
        : content d = non_ws lead := by
  unfold leading_sep? at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  next firstSplitCondition secondSplitCondition =>
    simp only [Option.some.injEq] at h
    subst h
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
