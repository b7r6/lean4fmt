/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                            // LEAN4FMT // PROOFS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The laws of the extended Wadler/Leijen core (DESIGN_V2 §10), stated about
    the SHIPPED render functions. Two-tier verification: everything below the
    parser boundary is proved here; everything whose statement needs the parser
    (idempotence, whole-pipeline token preservation) is the runtime gate's job
    by design.

    T1  go_content   — rendering only moves whitespace (content preservation)
    T4  wr_out       — the writer's extension is exactly the written content

    Scope: `Tame` docs (no opaque verbatim/textRaw payloads) that are
    `Coherent` (an alignOr's grid rows carry the same content as its fallback —
    true by construction in every emitter; stating it makes it a LAW).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Doc.Core
import Lean4Fmt.Doc.Render

namespace Lean4Fmt.Doc.Proofs

open Lean4Fmt.Doc

/-- Non-whitespace character content of a string, in order. -/
def nonWs (s : String) : List Char :=
  s.toList.filter (fun c => !c.isWhitespace)

mutual
/-- Docs with no opaque payloads (`verbatim`/`textRaw`) and whitespace-only
    table separators. -/
def Tame : Doc → Prop
  | .textRaw _ => False
  | .verbatim _ _ => False
  | .cat a b => Tame a ∧ Tame b
  | .group d | .nest _ d | .align d | .flatten d => Tame d
  | .alignTable spec rows => nonWs spec.sep = [] ∧ TameRows rows
  | .alignOr spec rows fb => nonWs spec.sep = [] ∧ TameRows rows ∧ Tame fb
  | .fillSep items => TameList items
  | _ => True

def TameList : List Doc → Prop
  | [] => True
  | d :: ds => Tame d ∧ TameList ds

def TameRows : List (List Doc) → Prop
  | [] => True
  | r :: rs => TameList r ∧ TameRows rs
end

mutual
/-- The content a doc denotes: `.text` payloads in order, whitespace-filtered
    (`alignOr` projected through its fallback). -/
def content : Doc → List Char
  | .text s => nonWs s
  | .cat a b => content a ++ content b
  | .group d | .nest _ d | .align d | .flatten d => content d
  | .alignTable _ rows => contentRows rows
  | .alignOr _ _ fb => content fb
  | .fillSep items => contentList items
  | _ => []

def contentList : List Doc → List Char
  | [] => []
  | d :: ds => content d ++ contentList ds

def contentRows : List (List Doc) → List Char
  | [] => []
  | r :: rs => contentList r ++ contentRows rs
end

mutual
/-- Coherence: every `alignOr`'s rows carry exactly its fallback's content. -/
def Coherent : Doc → Prop
  | .cat a b => Coherent a ∧ Coherent b
  | .group d | .nest _ d | .align d | .flatten d => Coherent d
  | .alignTable _ rows => CoherentRows rows
  | .alignOr _ rows fb => contentRows rows = content fb ∧ CoherentRows rows ∧ Coherent fb
  | .fillSep items => CoherentList items
  | _ => True

def CoherentList : List Doc → Prop
  | [] => True
  | d :: ds => Coherent d ∧ CoherentList ds

def CoherentRows : List (List Doc) → Prop
  | [] => True
  | r :: rs => CoherentList r ∧ CoherentRows rs
end

-- ── string plumbing ─────────────────────────────────────────────────────────

@[simp] theorem nonWs_append (a b : String) : nonWs (a ++ b) = nonWs a ++ nonWs b := by
  simp [nonWs, String.toList_append, List.filter_append]

@[simp] theorem nonWs_spaces (n : Nat) : nonWs (spaces n) = [] := by
  simp only [nonWs, spaces, String.toList_ofList]
  induction n with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ] using ih

@[simp] theorem nonWs_newlines (n : Nat) : nonWs (newlines n) = [] := by
  simp only [nonWs, newlines, String.toList_ofList]
  induction n with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ] using ih

@[simp] theorem nonWs_empty : nonWs "" = [] := rfl

@[simp] theorem nonWs_space : nonWs " " = [] := by decide

@[simp] theorem nonWs_newline : nonWs "\n" = [] := by decide

/-- T4 (writer hygiene / content): `wr`'s extension over the old output is
    exactly `nonWs s` — the pending newlines and indent it flushes contribute
    nothing. In particular `wr` never writes the indent except immediately
    followed by its content. -/
@[simp] theorem wr_out (st : RSt) (indent : Nat) (s : String) :
    nonWs (wr st indent s).out = nonWs st.out ++ nonWs s := by
  unfold wr
  by_cases h : st.pend > 0 <;> simp [h]

/-- A padded row's content is its cells' content in order (separators and pads
    are whitespace). -/
theorem renderRowStr_content (sep : String) (hsep : nonWs sep = [])
    (widths : List Nat) (r : List String) :
    nonWs (renderRowStr sep widths r) = (r.map nonWs).flatten := by
  induction r generalizing widths with
  | nil => simp [renderRowStr]
  | cons c cs ih =>
    cases cs with
    | nil => simp [renderRowStr]
    | cons c' cs' =>
      simp only [renderRowStr, List.map_cons, List.flatten_cons]
      rw [nonWs_append, nonWs_append, nonWs_append]
      simp [hsep, ih]

-- ── T1: content preservation ────────────────────────────────────────────────

/-- The table-emission fold appends exactly the rows' content. -/
theorem emitTable_content (maxPend indent : Nat) (sep : String) (hsep : nonWs sep = [])
    (widths : List Nat) (strRows : List (List String)) (st : RSt) :
    nonWs (emitTable maxPend indent sep widths strRows st).out
    = nonWs st.out ++ ((strRows.map (fun r => (r.map nonWs).flatten)).flatten) := by
  suffices h : ∀ (first : Bool) (st : RSt),
      nonWs ((strRows.foldl (fun (p : RSt × Bool) r =>
        let st := if p.2 then p.1 else { p.1 with pend := Nat.min (p.1.pend + 1) maxPend }
        (wr st indent (renderRowStr sep widths r), false)) (st, first)).1).out
      = nonWs st.out ++ ((strRows.map (fun r => (r.map nonWs).flatten)).flatten) by
    exact h true st
  induction strRows with
  | nil => intro first st; simp
  | cons r rs ih =>
    intro first st
    simp only [List.foldl_cons, List.map_cons, List.flatten_cons]
    rw [ih]
    by_cases h : first <;>
      simp [h, wr_out, renderRowStr_content sep hsep, List.append_assoc]

mutual

/-- **T1 — content preservation.** Rendering a Tame, Coherent doc appends
    exactly its content: the renderer can move, insert, and collapse
    whitespace, and can do NOTHING else. -/
theorem go_content (width maxPend : Nat) (d : Doc) (indent : Nat) (flat : Bool)
    (st : RSt) (tame : Tame d) (coh : Coherent d) :
    nonWs (go width maxPend d indent flat st).out = nonWs st.out ++ content d := by
  match d with
  | .nil => simp [go, content]
  | .text s => simp [go, content, wr_out]
  | .textRaw _ => exact absurd tame (by simp [Tame])
  | .verbatim _ _ => exact absurd tame (by simp [Tame])
  | .cat a b =>
    have ⟨ta, tb⟩ : Tame a ∧ Tame b := tame
    have ⟨ca, cb⟩ : Coherent a ∧ Coherent b := coh
    simp only [go, content]
    rw [go_content width maxPend b indent flat _ tb cb,
        go_content width maxPend a indent flat st ta ca, List.append_assoc]
  | .line =>
    simp only [go, content]
    by_cases h : flat <;> simp [h, wr_out]
  | .softline =>
    simp only [go, content]
    by_cases h : flat <;> simp [h]
  | .hardline => simp [go, content]
  | .blank _ => simp [go, content]
  | .group d' =>
    have t : Tame d' := tame
    have c : Coherent d' := coh
    simp only [go, content]
    exact go_content width maxPend d' indent _ st t c
  | .flatten d' =>
    have t : Tame d' := tame
    have c : Coherent d' := coh
    simp only [go, content]
    exact go_content width maxPend d' indent true st t c
  | .nest n d' =>
    have t : Tame d' := tame
    have c : Coherent d' := coh
    simp only [go, content]
    exact go_content width maxPend d' _ flat st t c
  | .align d' =>
    have t : Tame d' := tame
    have c : Coherent d' := coh
    simp only [go, content]
    exact go_content width maxPend d' st.col flat st t c
  | .fillSep items =>
    have t : TameList items := tame
    have c : CoherentList items := coh
    simp only [go, content]
    exact goFill_content width maxPend items indent flat true st t c
  | .alignTable spec rows =>
    have ⟨hsep, tr⟩ : nonWs spec.sep = [] ∧ TameRows rows := tame
    have cr : CoherentRows rows := coh
    simp only [go, content]
    rw [emitTable_content maxPend indent spec.sep hsep]
    congr 1
    exact goCellsRows_content width maxPend rows indent tr cr
  | .alignOr spec rows fb =>
    have ⟨hsep, tr, tf⟩ : nonWs spec.sep = [] ∧ TameRows rows ∧ Tame fb := tame
    have ⟨heq, cr, cf⟩ : contentRows rows = content fb ∧ CoherentRows rows ∧ Coherent fb := coh
    simp only [go, content]
    repeat' split
    all_goals first
      | exact go_content width maxPend fb indent true st tf cf
      | exact go_content width maxPend fb indent flat st tf cf
      | (rw [emitTable_content maxPend indent spec.sep hsep,
             goCellsRows_content width maxPend rows indent tr cr, heq])

/-- Fill packing appends exactly the items' content. -/
theorem goFill_content (width maxPend : Nat) (items : List Doc) (indent : Nat)
    (flat first : Bool) (st : RSt) (tame : TameList items) (coh : CoherentList items) :
    nonWs (goFill width maxPend items indent flat first st).out
    = nonWs st.out ++ contentList items := by
  match items with
  | [] => simp [goFill, contentList]
  | i :: is =>
    have ⟨ti, tis⟩ : Tame i ∧ TameList is := tame
    have ⟨ci, cis⟩ : Coherent i ∧ CoherentList is := coh
    have hcell : nonWs (go width maxPend i indent true {}).out = content i := by
      have := go_content width maxPend i indent true {} ti ci
      simpa [nonWs] using this
    simp only [goFill, contentList]
    rw [goFill_content width maxPend is indent flat false _ tis cis]
    by_cases hf : first
    · simp [hf, wr_out, hcell, List.append_assoc]
    · simp only [hf]
      repeat' split
      all_goals simp_all [wr_out, hcell, List.append_assoc]

/-- Cell rendering: the rendered strings carry the cells' content. -/
theorem goCells_content (width maxPend : Nat) (cs : List Doc) (indent : Nat)
    (tame : TameList cs) (coh : CoherentList cs) :
    ((goCells width maxPend cs indent).map nonWs).flatten = contentList cs := by
  match cs with
  | [] => simp [goCells, contentList]
  | c :: cs' =>
    have ⟨tc, tcs⟩ : Tame c ∧ TameList cs' := tame
    have ⟨cc, ccs⟩ : Coherent c ∧ CoherentList cs' := coh
    simp only [goCells, List.map_cons, List.flatten_cons, contentList]
    rw [goCells_content width maxPend cs' indent tcs ccs]
    congr 1
    have := go_content width maxPend c indent true {} tc cc
    simpa [nonWs] using this

theorem goCellsRows_content (width maxPend : Nat) (rows : List (List Doc)) (indent : Nat)
    (tame : TameRows rows) (coh : CoherentRows rows) :
    ((goCellsRows width maxPend rows indent).map (fun r => (r.map nonWs).flatten)).flatten
    = contentRows rows := by
  match rows with
  | [] => simp [goCellsRows, contentRows]
  | r :: rs =>
    have ⟨tr, trs⟩ : TameList r ∧ TameRows rs := tame
    have ⟨cr, crs⟩ : CoherentList r ∧ CoherentRows rs := coh
    simp only [goCellsRows, List.map_cons, List.flatten_cons, contentRows]
    rw [goCellsRows_content width maxPend rs indent trs crs,
        goCells_content width maxPend r indent tr cr]

end

/-- T1 at the public entry point: `render` output carries exactly the doc's
    content (the final newline is whitespace). -/
theorem render_content (style : Lean4Fmt.Style.Style) (d : Doc)
    (tame : Tame d) (coh : Coherent d) :
    nonWs (render style d) = content d := by
  have h := go_content style.layout.lineWidth (style.blankLines.maxConsecutive + 1)
    d 0 false {} tame coh
  simp only [render]
  by_cases he : (go style.layout.lineWidth (style.blankLines.maxConsecutive + 1)
      d 0 false {}).out.endsWith "\n"
  · simp only [he, if_true]
    simpa [nonWs] using h
  · simp only [he, if_false, Bool.false_eq_true]
    rw [nonWs_append]
    have : nonWs "\n" = [] := rfl
    simpa [this, nonWs] using h

end Lean4Fmt.Doc.Proofs
