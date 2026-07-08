/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        // LEAN4FMT // DOC // CORE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The document IR (DESIGN_V2 §4): a Wadler/Leijen algebra extended with
    alignment tables (§7), blank-line requests (§8), and opaque verbatim
    reproduction (§4.1). The walker (`Emit`) produces `Doc` — intent only; the
    renderer (`Doc/Render`) turns it into text under a `Style`.

    Pure, Lean-core only. Depends on nothing.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Lean4Fmt.Doc

/-- Column spec for an alignment table (§7). `maxDelta` caps padding so we never
    produce the ragged-whitespace anti-pattern; a run wider than this opts out. -/
structure ColSpec where
  sep      : String := " "
  maxDelta : Nat := 8
  deriving Inhabited, Repr

/-- A request for vertical space (§8), in *desired blank lines*. The renderer
    clamps/contextualizes this against the `BlankLines` policy — it is a request,
    not a command. -/
abbrev BlankReq := Nat

/-- The document IR. `text` must not contain '\n'; multi-line content goes through
    `textRaw` (comments) or `verbatim` (opaque reproduction, §4.1). -/
inductive Doc where
  -- Wadler/Leijen core
  | nil
  | text       (s : String)
  | cat        (a b : Doc)
  | line                                    -- flat: " "  ; break: newline+indent
  | softline                                -- flat: ""   ; break: newline+indent
  | hardline                                -- always newline+indent
  | group      (d : Doc)                    -- try flat; break whole group if it won't fit
  | nest       (n : Int) (d : Doc)          -- shift break-indent of `d` by n
  | align      (d : Doc)                    -- set break-indent to the current column
  -- extensions
  | alignTable (spec : ColSpec) (rows : Array (Array Doc))   -- §7
  | blank      (req : BlankReq)                              -- §8
  | flatten    (d : Doc)                                     -- force flat
  | textRaw    (s : String)                                  -- verbatim comment (may contain '\n')
  | verbatim   (src : String) (baseIndent : Nat)             -- opaque reproduction (§4.1)
  deriving Inhabited

namespace Doc

/-- `cat`/`nil` form a monoid; this instance is that monoid's `<>`. -/
instance : Append Doc := ⟨Doc.cat⟩
instance : HAdd Doc Doc Doc := ⟨Doc.cat⟩

@[inline] def empty : Doc := .nil
@[inline] def space : Doc := .text " "

/-- Concatenate a list of docs. -/
def concat (ds : List Doc) : Doc := ds.foldl .cat .nil

/-- Concatenate an array of docs. -/
def concatArr (ds : Array Doc) : Doc := ds.foldl .cat .nil

/-- Whether a comment carries a line comment `-- …` (the un-flattenable hazard,
    §0.4). A `group` containing one must render in break mode. -/
def isLineComment (s : String) : Bool := (s.splitOn "--").length > 1

end Doc
end Lean4Fmt.Doc
