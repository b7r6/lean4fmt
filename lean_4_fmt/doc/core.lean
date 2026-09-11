/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        // LEAN4FMT // DOC // CORE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The document IR (doc/design.md §5): a Wadler/Leijen algebra extended with
    alignment tables (§7), blank-line requests (§8), and opaque verbatim
    reproduction (§5.2). The walker (`Emit`) produces `Doc` — intent only; the
    renderer (`Doc/Render`) turns it into text under a `Style`.

    Pure, Lean-core only. Depends on nothing.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Lean4Fmt.Doc

/-- Column spec for an alignment table (§7). `maxDelta` caps padding so we never
    produce the ragged-whitespace anti-pattern; a run wider than this opts out. -/
structure col_spec where
  sep      : String := " "
  maxDelta : Nat := 8
  deriving Inhabited, Repr

/-- A request for vertical space (§8), in *desired blank lines*. The renderer
    clamps/contextualizes this against the `BlankLines` policy — it is a request,
    not a command. -/
abbrev blank_req := Nat

/-- The document IR. `text` must not contain '\n'; multi-line content goes through
    `textRaw` (comments) or `verbatim` (opaque reproduction, §4.1). -/
inductive Doc where
  -- Wadler/Leijen core
  | nil
  | text (source : String)
  | cat (leftValue rightValue : Doc)
  | line -- flat: " "  ; break: newline+indent
  | softline -- flat: ""   ; break: newline+indent
  | hardline -- always newline+indent
  | group (document : Doc) -- try flat; break whole group if it won't fit
  | nest (count : Int) (document : Doc) -- shift break-indent of `d` by n
  | align (document : Doc) -- set break-indent to the current column
  -- extensions
  -- container payloads are LISTS (not arrays) so the Doc walkers get
  -- structural nested recursion — total by construction, provable in Proofs
  | alignTable (spec : col_spec) (rows : List (List Doc)) -- §7
  -- §7 with composition: the padded table WHEN the run's column delta is under
  -- spec.maxDelta AND every padded row fits the line width — otherwise the
  -- ordinary fallback layout ("a cell that must wrap opts out of the grid").
  | align_or (spec : col_spec) (rows : List (List Doc)) (fallback : Doc)
  -- §5: pack flat items separated by single spaces, wrapping at the width
  -- (literal pools — byte tables, opcode lists). Items must be flat-capable.
  | fillSep (items : List Doc)
  | blank (req : blank_req)  -- §8
  | flatten (document : Doc) -- force flat
  -- phantom width: renders NOTHING (flat width 0 — T2 exactness holds), but a
  -- group fit counts it via `padWidth` — the reserve for un-breakable text the
  -- CALLER appends after the group on the same line (` := by` after a sig)
  | pad (count : Nat)
  | textRaw (source : String) -- verbatim comment (may contain '\n')
  | verbatim (src : String) (baseIndent : Nat) -- opaque reproduction (§4.1)
  deriving Inhabited

namespace Doc

/-- `cat`/`nil` form a monoid; this instance is that monoid's `<>`. -/
instance : Append Doc := ⟨Doc.cat⟩

instance : HAdd Doc Doc Doc := ⟨Doc.cat⟩

@[inline]
def empty : Doc := .nil

@[inline]
def space : Doc := .text " "

/-- Concatenate a list of docs. -/
def concat (documents : List Doc) : Doc := documents.foldl .cat .nil

/-- Concatenate an array of docs. -/
def concat_arr (documents : Array Doc) : Doc := documents.foldl .cat .nil

/-- Whether a comment carries a line comment `-- …` (the un-flattenable hazard,
    §0.4). A `group` containing one must render in break mode. -/
def is_line_comment (source : String) : Bool := (source.splitOn "--").length > 1

end Doc
end Lean4Fmt.Doc
