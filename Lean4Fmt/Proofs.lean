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

-- ── char/string plumbing ────────────────────────────────────────────────────

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
  | succ k ih => simpa [List.replicate_succ] using ih

@[simp]
theorem non_ws_newlines (n : Nat) : non_ws (newlines n) = [] := by
  simp only [newlines, non_ws_of_list, non_ws_l]
  induction n with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ] using ih

@[simp]
theorem non_ws_empty : non_ws "" = [] := rfl

@[simp]
theorem non_ws_space : non_ws " " = [] := by decide

@[simp]
theorem non_ws_newline : non_ws "\n" = [] := by decide

theorem non_ws_l_nil_of_spaces (cs : List Char) (h : cs.all (· == ' ')) : non_ws_l cs = [] := by
  simp only [non_ws_l, List.filter_eq_nil_iff]
  intro a ha
  have : a = ' ' := by simpa using List.all_eq_true.mp h a ha
  subst this
  decide

theorem non_ws_l_drop_while_space
        (cs : List Char)
        : non_ws_l (cs.dropWhile (· == ' ')) = non_ws_l cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c = ' '
    · subst hc
      have : (!(' ' : Char).isWhitespace) = false := by decide
      simpa [List.dropWhile_cons, non_ws_l, List.filter_cons, this] using ih
    · simp [List.dropWhile_cons, hc]

theorem non_ws_l_drop_while_ws
        (cs : List Char)
        : non_ws_l (cs.dropWhile Char.isWhitespace) = non_ws_l cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c.isWhitespace
    · simpa [List.dropWhile_cons, non_ws_l, List.filter_cons, hc] using ih
    · simp [List.dropWhile_cons, hc]

theorem non_ws_l_reverse (cs : List Char) : non_ws_l cs.reverse = (non_ws_l cs).reverse := by
  simp [non_ws_l, List.filter_reverse]

theorem non_ws_l_trim_end_ws (cs : List Char) : non_ws_l (trim_end_ws cs) = non_ws_l cs := by
  unfold trim_end_ws
  rw [non_ws_l_reverse, non_ws_l_drop_while_ws, non_ws_l_reverse, List.reverse_reverse]

-- ── splitLines / wrBlock plumbing ───────────────────────────────────────────

theorem split_lines_ne_nil (cs : List Char) : split_lines cs ≠ [] := by
  cases cs with
  | nil => simp [split_lines]
  | cons c cs =>
    simp only [split_lines]
    repeat' split
    all_goals simp

/-- Line-splitting loses only the '\n' separators — whitespace. -/
theorem split_lines_non_ws
        (cs : List Char)
        : ((split_lines cs).map non_ws_l).flatten = non_ws_l cs := by
  induction cs with
  | nil => simp [split_lines]
  | cons c cs ih =>
    simp only [split_lines]
    cases h : split_lines cs with
    | nil => exact absurd h (split_lines_ne_nil cs)
    | cons l ls =>
      rw [h] at ih
      simp only [List.map_cons, List.flatten_cons] at ih
      by_cases hc : c = '\n'
      · subst hc
        simp only [reduceIte, List.map_cons, List.flatten_cons, non_ws_l_nil, List.nil_append]
        rw [ih]
        show non_ws_l cs = non_ws_l ('\n' :: cs)
        have : (!('\n' : Char).isWhitespace) = false := by decide
        simp [non_ws_l, List.filter_cons, this]
      · simp only [if_neg hc, List.map_cons, List.flatten_cons]
        show non_ws_l (c :: l) ++ (ls.map non_ws_l).flatten = non_ws_l (c :: cs)
        cases hw : (!c.isWhitespace) with
        | false =>
          simp only [non_ws_l, List.filter_cons, hw, Bool.false_eq_true, if_false]
          exact ih
        | true =>
          simp only [non_ws_l, List.filter_cons, hw, if_true, List.cons_append]
          exact congrArg (c :: ·) ih

theorem flatten_map_drop_blank
        (ls : List (List Char))
        : (((ls.dropWhile is_blank_line).map non_ws_l)).flatten = (ls.map non_ws_l).flatten := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    by_cases hb : is_blank_line l = true
    · rw [List.dropWhile_cons_of_pos hb]
      simp [ih, non_ws_l_nil_of_spaces l hb]
    · rw [List.dropWhile_cons_of_neg (by simp [hb])]

/-- T4 (writer hygiene / content): `wr`'s extension over the old output is
    exactly `nonWs s` — the pending newlines and indent it flushes contribute
    nothing. In particular `wr` never writes the indent except immediately
    followed by its content. -/
@[simp]
theorem wr_out
        (st : rst)
        (indent : Nat)
        (s : String)
        : non_ws (wr st indent s).out = non_ws st.out ++ non_ws s := by
  unfold wr
  by_cases h : st.pend > 0 <;> simp [h]

/-- Dedenting drops only spaces — the content of a continuation line survives
    its re-anchoring intact (the wrBlock content-eater made impossible). -/
theorem non_ws_l_dedent (base : Nat) (l : List Char) : non_ws_l (dedent base l) = non_ws_l l := by
  unfold dedent
  split
  · next h =>
      simp only [Bool.and_eq_true] at h
      have h2 : non_ws_l l = non_ws_l (l.take base) ++ non_ws_l (l.drop base) := by
        rw [← non_ws_l_append, List.take_append_drop]
      rw [h2, non_ws_l_nil_of_spaces _ h.2, List.nil_append]
  · exact non_ws_l_drop_while_space l

theorem wr_line_out
        (st : rst)
        (indent base : Nat)
        (l : List Char)
        : non_ws (wr_line st indent base l).out = non_ws st.out ++ non_ws_l l := by
  unfold wr_line
  split
  · next he =>
      have h0 : dedent base l = [] := by simpa [List.isEmpty_iff] using he
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
  | cons l ls ih => simp [wr_lines, ih, wr_line_out, List.append_assoc]

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
  cases h : (split_lines (trim_end_ws raw.toList)).dropWhile is_blank_line with
  | nil =>
    rw [h] at hchain
    simp only [List.map_nil, List.flatten_nil] at hchain
    show non_ws st.out = non_ws st.out ++ non_ws raw
    rw [show non_ws raw = non_ws_l raw.toList from rfl, ← hchain, List.append_nil]
  | cons l rest =>
    rw [h] at hchain
    simp only [List.map_cons, List.flatten_cons] at hchain
    rw [wr_lines_out, wr_out, non_ws_of_list, List.append_assoc, hchain]
    rfl

-- ── T1: content preservation ────────────────────────────────────────────────

/-- The table-emission fold appends exactly the padded rows' content. -/
theorem emit_table_content
        (maxPend indent : Nat)
        (sep : String)
        (widths : List Nat)
        (strRows : List (List String))
        (st : rst)
        : non_ws (emit_table maxPend indent sep widths strRows st).out
            = non_ws st.out ++ ((strRows.map fun r => non_ws (render_row_str sep widths r)).flatten) := by
  suffices h : ∀ (first : Bool) (st : rst),
      non_ws ((strRows.foldl (fun (p : rst × Bool) r =>
        let st := if p.2 then p.1 else { p.1 with pend := Nat.min (p.1.pend + 1) maxPend }
        (wr st indent (render_row_str sep widths r), false)) (st, first)).1).out
      = non_ws st.out ++ ((strRows.map fun r => non_ws (render_row_str sep widths r)).flatten) by
    exact h true st
  induction strRows with
  | nil => intro first st; simp
  | cons r rs ih =>
    intro first st
    simp only [List.foldl_cons, List.map_cons, List.flatten_cons]
    rw [ih]
    by_cases h : first <;> simp [h, wr_out, List.append_assoc]

mutual

/-- **T1 — content preservation, UNCONDITIONAL.** Rendering appends exactly
    the doc's content: the renderer can move, insert, and collapse whitespace,
    and can do NOTHING else — for every doc, opaque payloads included. -/
theorem go_content (width maxPend : Nat) (d : Doc) (indent : Nat) (flat : Bool)
    (st : rst) :
    non_ws (go width maxPend d indent flat st).out = non_ws st.out ++ content d := by
  match d with
  | .nil => simp [go, content]
  | .text s => simp [go, content, wr_out]
  | .textRaw s =>
    simp only [go, content]
    repeat' split
    all_goals simp
  | .verbatim s b =>
    simp only [go, content]
    exact wr_block_out st indent b s
  | .cat a b =>
    simp only [go, content]
    rw [go_content width maxPend b indent flat _,
        go_content width maxPend a indent flat st, List.append_assoc]
  | .line =>
    simp only [go, content]
    by_cases h : flat <;> simp [h, wr_out]
  | .softline =>
    simp only [go, content]
    by_cases h : flat <;> simp [h]
  | .hardline => simp [go, content]
  | .blank _ => simp [go, content]
  | .group d' =>
    simp only [go, content]
    exact go_content width maxPend d' indent _ st
  | .flatten d' =>
    simp only [go, content]
    exact go_content width maxPend d' indent true st
  | .nest n d' =>
    simp only [go, content]
    exact go_content width maxPend d' _ flat st
  | .align d' =>
    simp only [go, content]
    exact go_content width maxPend d' st.col flat st
  | .fillSep items =>
    simp only [go, content]
    exact goFill_content width maxPend items indent flat true st
  | .alignTable spec rows =>
    simp only [go, content]
    rw [emit_table_content]
    congr 1
    exact goCellsRows_content width maxPend rows indent spec.sep _
  | .align_or spec rows fb =>
    simp only [go, content]
    repeat' split
    all_goals first
      | exact go_content width maxPend fb indent true st
      | exact go_content width maxPend fb indent flat st
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
  | i :: is =>
    have hcell : non_ws (go width maxPend i indent true {}).out = content i := by
      have := go_content width maxPend i indent true {}
      simpa [non_ws] using this
    simp only [goFill, contentList]
    rw [goFill_content width maxPend is indent flat false _]
    by_cases hf : first
    · simp [hf, wr_out, hcell, List.append_assoc]
    · simp only [hf]
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
  | [c] =>
    simp only [goCells, render_row_str, contentRow]
    have := go_content width maxPend c indent true {}
    simpa [non_ws] using this
  | c :: c' :: cs' =>
    have hcell : non_ws (go width maxPend c indent true {}).out = content c := by
      have := go_content width maxPend c indent true {}
      simpa [non_ws] using this
    have hrec := goCells_content width maxPend (c' :: cs') indent sep (widths.drop 1)
    simp only [goCells] at hrec ⊢
    simp only [render_row_str]
    simp only [non_ws_append, non_ws_spaces, List.append_nil]
    rw [hrec]
    simp [hcell, List.append_assoc, contentRow]

theorem goCellsRows_content (width maxPend : Nat) (rows : List (List Doc)) (indent : Nat)
    (sep : String) (widths : List Nat) :
    ((goCellsRows width maxPend rows indent).map fun r => non_ws (render_row_str sep widths r)).flatten
    = contentRows (non_ws sep) rows := by
  match rows with
  | [] => simp [goCellsRows, contentRows]
  | r :: rs =>
    simp only [goCellsRows, List.map_cons, List.flatten_cons, contentRows]
    rw [goCellsRows_content width maxPend rs indent sep widths,
        goCells_content width maxPend r indent sep widths]

end

/-- T1 at the public entry point, UNCONDITIONAL: for every doc, `render`'s
    output carries exactly the doc's content. -/
theorem render_content
        (style : Lean4Fmt.Style.Style)
        (d : Doc)
        : non_ws (render style d) = content d := by
  have h := go_content style.layout.lineWidth (style.blankLines.maxConsecutive + 1) d 0 false {}
  simp only [render]
  by_cases he : (go style.layout.lineWidth (style.blankLines.maxConsecutive + 1)
      d 0 false {}).out.endsWith "\n"
  · simp only [he, if_true]
    simpa [non_ws] using h
  · simp only [he, if_false, Bool.false_eq_true]
    rw [non_ws_append]
    have hnl : non_ws "\n" = [] := by decide
    rw [hnl, List.append_nil]
    simpa [non_ws] using h

-- ── T2: flat exactness ──────────────────────────────────────────────────────

mutual

  /-- The one-line string flat rendering denotes (meaningful when `flatWidth`
    is `some`). -/
  def flatRender : Doc → String
    | .nil | .softline | .hardline | .blank _ => ""
    | .alignTable _ _ => ""
    | .text s => s
    | .textRaw s => s
    | .verbatim s _ => String.ofList (trim_end_ws s.toList)
    | .cat a b => flatRender a ++ flatRender b
    | .line => " "
    | .group d | .nest _ d | .align d | .flatten d => flatRender d
    | .align_or _ _ fb => flatRender fb
    | .fillSep [] => ""
    | .fillSep (i :: is) => flatRender i ++ flatRenderSep is

  def flatRenderSep : List Doc → String
    | []      => ""
    | i :: is => " " ++ flatRender i ++ flatRenderSep is

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
    | .text s => simp_all [flat_width, flatRender]
    | .textRaw s =>
      simp only [flat_width] at hw
      split at hw
      · exact absurd hw (by simp)
      · simp_all [flatRender]
    | .verbatim s _ =>
      simp only [flat_width] at hw
      split at hw
      · exact absurd hw (by simp)
      · simp only [Option.some.injEq] at hw
        simp [flatRender, ← hw]
    | .cat a b =>
      simp only [flat_width] at hw
      split at hw
      · next x y hx hy =>
          simp only [Option.some.injEq] at hw
          simp [flatRender, String.length_append, flatRender_length a x hx,
            flatRender_length b y hy, hw]
      · exact absurd hw (by simp)
    | .line =>
      simp only [flat_width, Option.some.injEq] at hw
      rw [← hw]; rfl
    | .softline => simp_all [flat_width, flatRender]
    | .hardline => simp_all [flat_width]
    | .blank _ => simp_all [flat_width]
    | .alignTable _ _ => simp_all [flat_width]
    | .group d' => simp only [flat_width] at hw; simpa [flatRender] using flatRender_length d' n hw
    | .nest _ d' => simp only [flat_width] at hw; simpa [flatRender] using flatRender_length d' n hw
    | .align d' => simp only [flat_width] at hw; simpa [flatRender] using flatRender_length d' n hw
    | .flatten d' =>
      simp only [flat_width] at hw; simpa [flatRender] using flatRender_length d' n hw
    | .align_or _ _ fb =>
      simp only [flat_width] at hw; simpa [flatRender] using flatRender_length fb n hw
    | .fillSep [] => simp_all [flat_width, flatRender]
    | .fillSep (i :: is) =>
      simp only [flat_width] at hw
      split at hw
      · next w ws hi his =>
          simp only [Option.some.injEq] at hw
          simp [flatRender, String.length_append, flatRender_length i w hi,
            flatRenderSep_length is ws his, hw]
      · exact absurd hw (by simp)

  theorem flatRenderSep_length
          (is : List Doc)
          (n : Nat)
          (hw : flatWidthSep is = some n)
          : (flatRenderSep is).length = n := by
    match is with
    | [] => simp_all [flatWidthSep, flatRenderSep]
    | i :: is' =>
      simp only [flatWidthSep] at hw
      split at hw
      · next w ws hi his =>
          simp only [Option.some.injEq] at hw
          subst hw
          simp [flatRenderSep, String.length_append, flatRender_length i w hi,
            flatRenderSep_length is' ws his]
      · exact absurd hw (by simp)

end

-- splitLines / trimEndWs facts for the verbatim case of T2

theorem split_lines_no_nl (cs : List Char) (h : '\n' ∉ cs) : split_lines cs = [cs] := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '\n' := fun hc => h (hc ▸ List.mem_cons_self ..)
    have hcs : '\n' ∉ cs := fun hm => h (List.mem_cons_of_mem _ hm)
    simp only [split_lines, ih hcs]
    simp [hc]

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
  | cons a l ih =>
    rw [List.dropWhile_cons] at h
    split at h
    · exact ih h
    · next hpa =>
        injection h with h1 _
        subst h1
        simpa using hpa

/-- A nonempty trailing-trimmed line is not blank (its last char is non-ws). -/
theorem trim_end_ws_not_blank
        (cs : List Char)
        (hne : trim_end_ws cs ≠ [])
        : is_blank_line (trim_end_ws cs) = false := by
  unfold trim_end_ws at hne ⊢
  cases h : cs.reverse.dropWhile Char.isWhitespace with
  | nil => simp [h] at hne
  | cons y ys =>
    have hy : Char.isWhitespace y = false := drop_while_head_not h
    have hy' : y ≠ ' ' := fun he => by subst he; simp at hy
    simp only [h, is_blank_line]
    rw [Bool.eq_false_iff]
    intro hall
    have := (List.all_eq_true.mp hall) y (by simp)
    exact hy' (by simpa using this)

mutual

  /-- **T2 — flat exactness (state form).** In flat mode with no pending
    newlines, rendering a doc of known flat width appends EXACTLY
    `flatRender d` and advances the column by exactly `n`. This is the law
    that makes `group`'s fit check (`effCol + flatWidth ≤ width`) an oracle:
    what it measures is precisely what gets emitted. -/
  theorem go_flat
          (width maxPend : Nat)
          (d : Doc)
          (indent : Nat)
          (n : Nat)
          (st : rst)
          (hw : flat_width d = some n)
          (hp : st.pend = 0)
          : go width maxPend d indent true st
              = { out := st.out ++ flatRender d, col := st.col + n, pend := 0 } := by
    match d with
    | .nil =>
      simp only [flat_width, Option.some.injEq] at hw
      obtain ⟨o, c, p⟩ := st
      subst hp
      simp [go, flatRender, ← hw]
    | .text s =>
      simp only [flat_width, Option.some.injEq] at hw
      obtain ⟨o, c, p⟩ := st
      subst hp
      simp [go, wr, flatRender, ← hw]
    | .textRaw s =>
      simp only [flat_width] at hw
      split at hw
      · exact absurd hw (by simp)
      · next hnl =>
          simp only [Option.some.injEq] at hw
          obtain ⟨o, c, p⟩ := st
          subst hp
          simp [go, hnl, flatRender, ← hw]
    | .verbatim s b =>
      simp only [flat_width] at hw
      split at hw
      · exact absurd hw (by simp)
      · next hnl =>
          simp only [Option.some.injEq] at hw
          have hnomem : '\n' ∉ trim_end_ws s.toList :=
            fun hm => hnl (List.any_eq_true.mpr ⟨'\n', mem_trim_end_ws hm, by simp⟩)
          simp only [go, wr_block, split_lines_no_nl _ hnomem]
          cases htr : trim_end_ws s.toList with
          | nil =>
            rw [htr] at hw
            obtain ⟨o, c, p⟩ := st
            subst hp
            simp_all [is_blank_line, flatRender, htr]
          | cons x xs =>
            have hnb : is_blank_line (x :: xs) = false := by
              have := trim_end_ws_not_blank (cs := s.toList) (by simp [htr])
              rwa [htr] at this
            rw [htr] at hw
            obtain ⟨o, c, p⟩ := st
            subst hp
            simp_all [List.dropWhile_cons, wr_lines, wr, flatRender, htr]
            omega
    | .cat a b =>
      simp only [flat_width] at hw
      split at hw
      · next x y hx hy =>
          simp only [Option.some.injEq] at hw
          simp only [go]
          rw [go_flat width maxPend a indent x st hx hp, go_flat width maxPend b indent y _ hy rfl]
          simp [flatRender, String.append_assoc, ← hw, Nat.add_assoc]
      · exact absurd hw (by simp)
    | .line =>
      simp only [flat_width, Option.some.injEq] at hw
      obtain ⟨o, c, p⟩ := st
      subst hp
      simp [go, wr, flatRender, ← hw]
    | .softline =>
      simp only [flat_width, Option.some.injEq] at hw
      obtain ⟨o, c, p⟩ := st
      subst hp
      simp [go, flatRender, ← hw]
    | .hardline => simp [flat_width] at hw
    | .blank _ => simp [flat_width] at hw
    | .alignTable _ _ => simp [flat_width] at hw
    | .group d' =>
      simp only [flat_width] at hw
      simp only [go, Bool.true_or]
      simpa [flatRender] using go_flat width maxPend d' indent n st hw hp
    | .nest m d' =>
      simp only [flat_width] at hw
      simp only [go]
      simpa [flatRender] using go_flat width maxPend d' _ n st hw hp
    | .align d' =>
      simp only [flat_width] at hw
      simp only [go]
      simpa [flatRender] using go_flat width maxPend d' st.col n st hw hp
    | .flatten d' =>
      simp only [flat_width] at hw
      simp only [go]
      simpa [flatRender] using go_flat width maxPend d' indent n st hw hp
    | .align_or _ _ fb =>
      simp only [flat_width] at hw
      simp only [go, if_true]
      simpa [flatRender] using go_flat width maxPend fb indent n st hw hp
    | .fillSep [] =>
      simp only [flat_width, Option.some.injEq] at hw
      obtain ⟨o, c, p⟩ := st
      subst hp
      simp [go, goFill, flatRender, ← hw]
    | .fillSep (i :: is) =>
      simp only [flat_width] at hw
      split at hw
      · next w ws hi his =>
          simp only [Option.some.injEq] at hw
          subst hw
          obtain ⟨o, c, p⟩ := st
          subst hp
          simp only [go, goFill]
          rw [go_flat width maxPend i indent w {} hi rfl]
          have hlen : (flatRender i).length = w := flatRender_length i w hi
          simp only [wr, gt_iff_lt, Nat.lt_irrefl, if_false, reduceIte, if_true]
          rw [goFill_flat width maxPend is indent ws _ his rfl]
          simp [flatRender, String.append_assoc, hlen, rst.mk.injEq]
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
      obtain ⟨o, c, p⟩ := st
      subst hp
      simp [goFill, flatRenderSep, ← hw]
    | i :: is' =>
      simp only [flatWidthSep] at hw
      split at hw
      · next w ws hi his =>
          simp only [Option.some.injEq] at hw
          subst hw
          obtain ⟨o, c, p⟩ := st
          subst hp
          simp only [goFill, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false, reduceIte]
          rw [go_flat width maxPend i indent w {} hi rfl]
          have hlen : (flatRender i).length = w := flatRender_length i w hi
          simp only [wr, gt_iff_lt, Nat.lt_irrefl, if_false, reduceIte]
          rw [goFill_flat width maxPend is' indent ws _ his rfl]
          simp [flatRenderSep, String.append_assoc, String.length_append, hlen, rst.mk.injEq]
          omega
      · exact absurd hw (by simp)

end

-- ── T2, one-line corollary ──────────────────────────────────────────────────

mutual
  /-- Well-formed docs: `.text` payloads are newline-free (the Doc contract —
    multi-line content must ride `textRaw`/`verbatim`). -/
  def WF : Doc → Prop
    | .text s => '\n' ∉ s.toList
    | .cat a b => WF a ∧ WF b
    | .group d | .nest _ d | .align d | .flatten d => WF d
    | .alignTable _ rows => WFRows rows
    | .align_or _ rows fb => WFRows rows ∧ WF fb
    | .fillSep items => WFList items
    | _ => True

  def WFList : List Doc → Prop
    | []      => True
    | d :: ds => WF d ∧ WFList ds

  def WFRows : List (List Doc) → Prop
    | []      => True
    | r :: rs => WFList r ∧ WFRows rs
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
    | .text s => exact wf
    | .textRaw s =>
      simp only [flat_width] at hw
      split at hw
      · exact absurd hw (by simp)
      · next hnl =>
          simp only [flatRender]
          intro hm
          exact hnl (List.any_eq_true.mpr ⟨'\n', hm, by simp⟩)
    | .verbatim s _ =>
      simp only [flat_width] at hw
      split at hw
      · exact absurd hw (by simp)
      · next hnl =>
          simp only [flatRender, String.toList_ofList]
          intro hm
          exact hnl (List.any_eq_true.mpr ⟨'\n', mem_trim_end_ws hm, by simp⟩)
    | .cat a b =>
      simp only [flat_width] at hw
      split at hw
      · next x y hx hy =>
          have ⟨wa, wb⟩ : WF a ∧ WF b := wf
          simp only [flatRender, String.toList_append, List.mem_append]
          rintro (h | h)
          · exact flatRender_noNl a x wa hx h
          · exact flatRender_noNl b y wb hy h
      · exact absurd hw (by simp)
    | .line => simp only [flatRender]; decide
    | .group d' => exact flatRender_noNl d' n wf (by simpa [flat_width] using hw)
    | .nest _ d' => exact flatRender_noNl d' n wf (by simpa [flat_width] using hw)
    | .align d' => exact flatRender_noNl d' n wf (by simpa [flat_width] using hw)
    | .flatten d' => exact flatRender_noNl d' n wf (by simpa [flat_width] using hw)
    | .align_or _ _ fb => exact flatRender_noNl fb n wf.2 (by simpa [flat_width] using hw)
    | .fillSep [] => simp [flatRender]
    | .fillSep (i :: is) =>
      simp only [flat_width] at hw
      split at hw
      · next w ws hi his =>
          have ⟨wi, wis⟩ : WF i ∧ WFList is := wf
          simp only [flatRender, String.toList_append, List.mem_append]
          rintro (h | h)
          · exact flatRender_noNl i w wi hi h
          · exact flatRenderSep_noNl is ws wis his h
      · exact absurd hw (by simp)

  theorem flatRenderSep_noNl
          (is : List Doc)
          (n : Nat)
          (wf : WFList is)
          (hw : flatWidthSep is = some n)
          : '\n' ∉ (flatRenderSep is).toList := by
    match is with
    | [] => simp [flatRenderSep]
    | i :: is' =>
      simp only [flatWidthSep] at hw
      split at hw
      · next w ws hi his =>
          have ⟨wi, wis⟩ : WF i ∧ WFList is' := wf
          simp only [flatRenderSep, String.toList_append, List.mem_append]
          rintro ((h | h) | h)
          · revert h; decide
          · exact flatRender_noNl i w wi hi h
          · exact flatRenderSep_noNl is' ws wis his h
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
            go width maxPend d indent true st = { out := st.out ++ s, col := st.col + n, pend := 0 }
                ∧ s.length = n
                ∧ '\n' ∉ s.toList :=
  ⟨
    flatRender d,
    go_flat width maxPend d indent n st hw hp,
    flatRender_length d n hw,
    flatRender_noNl d n wf hw
  ⟩

-- ── T3: seam content preservation ───────────────────────────────────────────

@[simp]
theorem content_append (a b : Doc) : content (a ++ b) = content a ++ content b := rfl

theorem non_ws_l_nil_of_ws_line (l : List Char) (h : ws_line l) : non_ws_l l = [] := by
  simp only [non_ws_l, List.filter_eq_nil_iff]
  intro a ha
  have := List.all_eq_true.mp h a ha
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
  | cons l ls ih =>
    simp only [seam_lines, List.map_cons, List.flatten_cons]
    split
    · next h => rw [ih, non_ws_l_nil_of_ws_line l h, List.nil_append]
    · simp only [content_append, content_seam_sep, List.nil_append, content]
      rw [ih, non_ws_of_list, non_ws_l_trim_end_ws, non_ws_l_dedent]

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
  next hh hl =>
    simp only [Option.some.injEq] at h
    subst h
    rw [seam_lines_content]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false] at hh hl
    have hchain := split_lines_non_ws lead.toList
    cases hls : split_lines lead.toList with
    | nil => exact absurd hls (split_lines_ne_nil lead.toList)
    | cons l0 rest =>
      rw [hls] at hchain hh hl
      simp only [List.drop_succ_cons, List.drop_zero]
      simp only [List.headD_cons] at hh
      simp only [List.map_cons, List.flatten_cons, non_ws_l_nil_of_ws_line l0 hh, List.nil_append] at hchain
      cases rest with
      | nil => simpa [non_ws] using hchain
      | cons r1 rs =>
        have hne : (r1 :: rs) ≠ [] := by simp
        have hlast : (l0 :: r1 :: rs).getLastD [] = (r1 :: rs).getLast hne := by
          simp [List.getLastD_eq_getLast?, List.getLast?_eq_getLast]
        rw [hlast] at hl
        rw [flatten_map_drop_last non_ws_l (r1 :: rs) hne, non_ws_l_nil_of_ws_line _ hl,
          List.append_nil] at hchain
        simpa [non_ws] using hchain

end Lean4Fmt.Doc.Proofs
