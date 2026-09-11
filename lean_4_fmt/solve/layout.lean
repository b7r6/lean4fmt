/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // SOLVE // LAYOUT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Optimal layout as constraint optimization (Bernardy's measure-algebra DP),
    the principled replacement for greedy `.group` line-breaking.

      • hard constraint : every line's width ≤ W (the roofline)
      • objective       : additive ⇒ MONOTONE cost (the preference map)
      • engine          : bottom-up Pareto frontier — monotonicity is exactly
                          what lets the prune keep the search polynomial
      • feasibility      : decidable; `omega` discharges the affine width
                          obligations in-language (the Farkas/ISL certificate)

    Solver-agnostic by construction: `frontier`/`bestUnder` is one backend; an
    external OMT (Z3/OptiMathSAT) drops in behind the same feasible-set / argmin
    interface. LIVE on the Emit path: `inlineDefFits` / `sigOneLineFits` drive the
    def sig-shape decision per declaration; `.group` and `.alignOr` are proven
    special cases of its `.choice` (the fold).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Lean4Fmt.Solve

/-- A concrete rendering: (indent, text) per line, indent relative to the
    subtree's own left edge. -/
abbrev lines := List (Nat × String)

def lines_maxw (lines : lines) : Nat :=
  lines.foldl (fun maximum line => max maximum (line.1 + line.2.length)) 0

def lines_last (lines : lines) : Nat :=
  match lines.getLast? with
  | some pathValue => pathValue.1 + pathValue.2.length
  | none           => 0

/-- Horizontal join: `b` continues `a`'s last line; `b`'s later lines shift
    right by `a`'s last-line width (they were relative to `b`'s left edge). -/
def cat_lines (leftValue rightValue : lines) : lines :=
  match leftValue.getLast? with
  | none => rightValue
  | some leftPlan =>
    let width := leftPlan.1 + leftPlan.2.length
    match rightValue with
    | [] => leftValue
    | rightPlan :: brest =>
      leftValue.dropLast
          ++ (leftPlan.1, leftPlan.2 ++ rightPlan.2)
              :: brest.map (fun line => (line.1 + width, line.2))

/-- Newline after `a`: the next content starts a fresh line at relative 0. -/
def flush_lines (leftValue : lines) : lines := leftValue ++ [(0, "")]

/-- Indent everything after the first line by `n`. -/
def nest_lines (count : Nat) (leftValue : lines) : lines :=
  match leftValue with
  | []                => []
  | pathValue :: rest => pathValue :: rest.map (fun line => (line.1 + count, line.2))

structure meas where
  lines : lines
  cost  : Nat
  deriving Inhabited

def meas.maxw (modeValue : meas) : Nat := lines_maxw modeValue.lines
def meas.last (modeValue : meas) : Nat := lines_last modeValue.lines

def cat_m (leftValue rightValue : meas) : meas :=
  { lines := cat_lines leftValue.lines rightValue.lines, cost := leftValue.cost + rightValue.cost }

def flush_m (leftValue : meas) : meas := { leftValue with lines := flush_lines leftValue.lines }

def nest_m (count : Nat) (leftValue : meas) : meas :=
  { leftValue with lines := nest_lines count leftValue.lines }

def pen_m (character : Nat) (leftValue : meas) : meas :=
  { leftValue with cost := leftValue.cost + character }

/-- Dominance: `x` is no worse than `y` in every coordinate that constrains the
    future — max width, last-line width, cost. With additive (monotone) cost a
    dominated partial layout can never extend to a strictly better whole, so we
    drop it. This prune is the whole tractability argument. -/
def dominates (inputValue rightValue : meas) : Bool :=
  inputValue.maxw ≤ rightValue.maxw && inputValue.last ≤ rightValue.last
      && inputValue.cost ≤ rightValue.cost

def insert_pareto (modeValue : meas) (frontier : List meas) : List meas :=
  if frontier.any (fun candidate => dominates candidate modeValue) then
    frontier
  else
    modeValue :: frontier.filter (fun candidate => !dominates modeValue candidate)

/-- Reduce a candidate set to its Pareto frontier. -/
def prune (modes : List meas) : List meas := modes.foldr insert_pareto []

def cross_cat (leftFunction rightFunction : List meas) : List meas :=
  leftFunction.foldr (fun left products => rightFunction.map (cat_m left) ++ products) []

/-- The layout problem: a tree of choice points. `choice` is the constraint
    variable (which alternative); `pen` attaches a preference weight. `group`
    is the degenerate 2-candidate case a Wadler printer bakes in. -/
inductive ldoc where
  | text (source : String)
  | cat (leftValue rightValue : ldoc)
  | flush (leftValue : ldoc)
  | nest (count : Nat) (leftValue : ldoc)
  | choice (alts : List ldoc)
  | pen (character : Nat) (leftValue : ldoc)
  deriving Inhabited

/-- The DP: the Pareto frontier of every layout the subtree admits, computed
    bottom-up. `frontier ∘ choice` is the feasible-set union; `crossCat` is the
    horizontal product; both re-pruned. -/
partial
def frontier : ldoc → List meas
  | .text textValue => [{ lines := [(0, textValue)], cost := 0 }]
  | .cat leftValue rightValue => prune (cross_cat (frontier leftValue) (frontier rightValue))
  | .flush leftValue => prune ((frontier leftValue).map flush_m)
  | .nest count leftValue => prune ((frontier leftValue).map (nest_m count))
  | .pen headChar leftValue => prune ((frontier leftValue).map (pen_m headChar))
  | .choice alts =>
    prune (alts.foldr (fun alternative candidates => frontier alternative ++ candidates) [])

/-- Pick the min-cost layout whose every line fits `W` (the hard constraint).
    If none fits, degrade to the narrowest — the never-worse-than-input floor,
    which the token/comment gate then backstops. -/
def best_under (widthBound : Nat) (transform : List meas) : Option meas :=
  let feas := transform.filter (fun candidate => candidate.maxw ≤ widthBound)
  let pool := if feas.isEmpty then transform else feas
  pool.foldl
    (
      fun best candidate => match best with
        | none => some candidate
        | some rightValue =>
          if candidate.cost < rightValue.cost
              || (candidate.cost == rightValue.cost && candidate.maxw < rightValue.maxw) then
            some candidate
          else
            rightValue
    )
    none

def solve (widthBound : Nat) (document : ldoc) : Option meas :=
  best_under widthBound (frontier document)

/-- The greedy caricature: each `choice` commits to the first alternative that
    fits ON ITS OWN, left-to-right, blind to how downstream placement or cost
    will land. This is the local optimum `.group` printers take. -/
partial
def greedy (widthBound : Nat) : ldoc → meas
  | .text textValue => { lines := [(0, textValue)], cost := 0 }
  | .cat leftValue rightValue => cat_m (greedy widthBound leftValue) (greedy widthBound rightValue)
  | .flush leftValue => flush_m (greedy widthBound leftValue)
  | .nest count leftValue => nest_m count (greedy widthBound leftValue)
  | .pen headChar leftValue => pen_m headChar (greedy widthBound leftValue)
  | .choice alts =>
    let cands := alts.map (greedy widthBound)
    match cands.find? (fun candidate => candidate.maxw ≤ widthBound) with
    | some candidate => candidate
    | none           => (cands.getLast?).getD { lines := [(0, "")], cost := 0 }

def render_meas (modeValue : meas) : String :=
  String.intercalate
    "\n"
    (modeValue.lines.map fun line => String.ofList (List.replicate line.1 ' ') ++ line.2)

/-- The affine feasibility of a horizontal composition — the two line-width
    obligations `a fits` and `a.last + b fits` — is exactly what omega discharges
    in the loop. (Scaled up, this is the Farkas/ISL certificate the solver emits.) -/
theorem cat_fits
        (aMax aLast bMax widthBound : Nat)
        (leftProof : aMax ≤ widthBound)
        (rightProof : aLast + bMax ≤ widthBound)
        : aMax ≤ widthBound ∧ aLast + bMax ≤ widthBound := by omega

-- ── sanity: the measure algebra ───────────────────────────────────────────────

#guard lines_maxw [(0, "ab"), (2, "cd")] == 4
#guard lines_last [(0, "ab"), (2, "cd")] == 4
#guard render_meas { lines := cat_lines [(0, "let x =")] [(0, "big")], cost := 0 } == "let x =big"

#guard (cat_m { lines := [(0, "ab")], cost := 0 } { lines := [(0, "c"), (0, "d")], cost := 0 }).maxw == 3

-- ── G-L1: the pruned DP is optimal, and the frontier is sub-exponential ───────

/-- Every layout the tree admits, WITHOUT the Pareto prune — the exhaustive
    ground truth `solve` must match on cost. -/
partial
def brute_force : ldoc → List meas
  | .text textValue => [{ lines := [(0, textValue)], cost := 0 }]
  | .cat leftValue rightValue => cross_cat (brute_force leftValue) (brute_force rightValue)
  | .flush leftValue => (brute_force leftValue).map flush_m
  | .nest count leftValue => (brute_force leftValue).map (nest_m count)
  | .pen headChar leftValue => (brute_force leftValue).map (pen_m headChar)
  | .choice alts =>
    alts.foldr (fun alternative candidates => brute_force alternative ++ candidates) []

def brute_opt (widthBound : Nat) (document : ldoc) : Option meas :=
  best_under widthBound (brute_force document)

/-- A chain of `n` break-or-flat segments (the long-application shape): flat is
    5 wide and free, broken is narrow and +1. `2^n` raw layouts. -/
def seg : ldoc := .choice [.pen 0 (.text "xxxxx"), .pen 1 (.cat (.flush (.text "x")) (.text "x"))]

def chain : Nat → ldoc
  | 0         => .text ""
  | count + 1 => .cat seg (chain count)

/-- A def-sig CHOICE whose body is a nested chain — the outer sig branch and the
    inner chain branches compose through the frontier (def ⊃ body, both breaking).
    The exact sig shape is immaterial; the NESTING is the point the DP optimizes. -/
def nested_def (count : Nat) : ldoc :=
  let sig : ldoc :=
    .choice
      [
        .pen 0 (.text "private def f (a : T) : R :="),
        .pen 2 (.cat (.flush (.text "private def f")) (.text "    (a : T) : R :="))
      ]
  .cat sig (.nest 2 (.cat (.flush (.text "")) (chain count)))

-- optimality: the pruned DP finds the SAME optimal cost as exhaustive search
#guard (solve 12 (chain 6)).map meas.cost == (brute_opt 12 (chain 6)).map meas.cost
#guard (solve 20 (chain 8)).map meas.cost == (brute_opt 20 (chain 8)).map meas.cost
#guard (solve 60 (nested_def 6)).map meas.cost == (brute_opt 60 (nested_def 6)).map meas.cost
#guard (solve 30 (nested_def 5)).map meas.cost == (brute_opt 30 (nested_def 5)).map meas.cost

-- tractability: monotone cost ⇒ the prune keeps the frontier sub-exponential
#guard (brute_force (chain 8)).length == 256 -- 2^8 raw layouts …
#guard (frontier (chain 8)).length ≤ 12 -- … collapse to a handful
#guard (brute_force (chain 12)).length == 4096 -- 2^12 …
#guard (frontier (chain 12)).length ≤ 16 -- … still a handful (grows ~n)
#guard (frontier (nested_def 6)).length ≤ 16

-- ── G-L3: the live def-path decision (byte-identical wiring) ──────────────────

/-- Route a def's INLINE-vs-BREAK decision through the solver: the whole-decl
    inline rung (sig + body on one line, measured width `total`) against an
    always-feasible break rung, selected by `bestUnder` — the hard-width filter
    then the cost argmin, the solver's own selection kernel. Picks inline iff it
    fits, so on a FLAT sig (feasibility is the whole story, greedy meets the
    optimum) it reproduces `total ≤ W` exactly — now COMPUTED by the measure
    algebra, live on the Emit path. The seam G-L4 widens: add the oneLine/fill
    rungs and real preference weights, and this same `bestUnder` starts choosing
    among them. -/
def inline_def_fits (widthBound total : Nat) : Bool :=
  let inlineRung : meas := { lines := [(total, "")], cost := 0 } -- maxw = total, preferred
  let breakRung : meas := { lines := [(0, "")], cost := 2 } -- maxw = 0, always feasible
  (best_under widthBound [inlineRung, breakRung]).map meas.cost == some 0

-- byte-identical to the `total ≤ width` test it replaces, across the boundary
#guard inline_def_fits 100 80 == true -- fits → inline
#guard inline_def_fits 100 100 == true -- exact fit → inline
#guard inline_def_fits 100 101 == false -- over → break
#guard (List.range 220).all
  (fun total => inline_def_fits 100 total == decide (total ≤ 100)) -- ≡ (total ≤ W)

-- ── G-L4: the preference-map choice over sig shapes ───────────────────────────

/-- The solver's selection kernel, TAGGED: return WHICH rung wins under the hard
    width constraint at least cost (the preference weight) — ties to narrower
    `maxw`, then list order. `bestUnder` returns the winning measure; this
    returns its tag, the shape the caller renders. Adding a candidate layout is
    adding one `(tag, Meas)` pair; the preference map is the cost column. This is
    the "select the most-preferred shape that satisfies the constraint" the whole
    campaign is for, one call. -/
def pick_shape
    {valueType : Type}
    (widthBound : Nat)
    (rungs : List (valueType × meas))
    : Option valueType :=
  let feas := rungs.filter (fun rung => rung.2.maxw ≤ widthBound)
  let pool := if feas.isEmpty then rungs else feas
  (
    pool.foldl
      (
        fun best rung => match best with
          | none => some rung
          | some rightValue =>
            if rung.2.cost < rightValue.2.cost
                || (rung.2.cost == rightValue.2.cost && rung.2.maxw < rightValue.2.maxw) then
              some rung
            else
              rightValue
      )
      none
  ).map
    (·.1)

/-- The G-L4 sig-shape choice for a BROKEN def: `oneLine` (binders ride the
    keyword line, the return type breaking after the colon if it must) is
    preferred over `onePerLine` (each binder its own line, always feasible).
    oneLine is feasible while the binders fit on the keyword line
    (`prefixW + bindersW ≤ W`); past that they would overflow, so the solver
    drops to the per-line stack. Returns `true` for oneLine. The adaptivity a
    fixed `binders` knob cannot do: the SAME sig rides one line where it fits and
    stacks where it does not, per declaration. -/
def sig_one_line_fits (widthBound prefixW bindersW : Nat) : Bool :=
  (
    pick_shape
      widthBound
      [
        (true, { lines := [(prefixW + bindersW, "")], cost := 0 }),
        (false, { lines := [(0, "")], cost := 1 })
      ]
  ).getD
    false

-- oneLine while the binders fit on the keyword line, else the per-line stack
#guard sig_one_line_fits 100 12 40 == true -- 12+40=52 ≤ 100 → oneLine
#guard sig_one_line_fits 100 12 90 == false -- 12+90=102 > 100 → onePerLine
#guard (List.range 120).all
  (fun bodyWidth => sig_one_line_fits 100 10 bodyWidth == decide (10 + bodyWidth ≤ 100))

-- ── G-L5: the fold — `.group` and `.alignOr` are degenerate `.choice` ─────────
--
-- A Wadler pretty-printer's `.group` is flat-or-break decided with ONE-token
-- lookahead; `.alignOr` is a fixed cascade of align options. Both are special
-- cases of the solver's `.choice` + measure-algebra DP: `.choice` with FEW
-- candidates, decided GREEDILY. The solver keeps every candidate in the Pareto
-- frontier, so an ENCLOSING choice sees a global optimum a local `.group` — which
-- has already committed — cannot. That is the whole thesis, made mechanical: the
-- combinator vocabulary of greedy pretty-printing is the low-lookahead corner of
-- one constraint problem, and the solver is the general instrument.

/-- A `.group` with an explicit break penalty: FLAT (free) or BROKEN (`+pen`) —
    the 2-candidate `.choice` a Wadler printer bakes in. -/
def group_w (pen : Nat) (flat broken : ldoc) : ldoc := .choice [.pen 0 flat, .pen pen broken]

/-- The standard `.group`: breaking costs 1. -/
def group (flat broken : ldoc) : ldoc := group_w 1 flat broken

/-- An `.alignOr` cascade: N equally-preferred align options, then a fallback —
    the (N+1)-candidate `.choice`. -/
def align_or (opts : List ldoc) (fallback : ldoc) : ldoc :=
  .choice (opts.map (fun option => ldoc.pen 0 option) ++ [.pen 1 fallback])

def groupFixture : ldoc := group (.text "iiiiiiiiii") (.cat (.flush (.text "iii")) (.text "iii"))

-- IN ISOLATION the solver reproduces the greedy `.group` decision, and `solve`
-- and `greedy` AGREE — there is no nesting to exploit.
#guard (solve 20 groupFixture).map meas.cost == some 0 -- flat fits (10 ≤ 20) → flat
#guard (solve 5 groupFixture).map meas.cost == some 1 -- flat overflows (10 > 5) → break
#guard (greedy 20 groupFixture).cost == 0 && (greedy 5 groupFixture).cost == 1 -- greedy makes the same call

-- NESTED, they DIVERGE. Two nested groups: the flat outer+inner overflows at
-- 12+10 = 22 > 20, so greedy commits the OUTER to broken (cost 10). The DP keeps
-- the outer FLAT and breaks only the inner (cost 1) — same feasibility, a tenth
-- the cost. `.group` is myopic; `.choice` + the frontier is not.
def nested_groups : ldoc :=
  group_w
    10
    (.cat (.text "PPPPPPPPPPPP") groupFixture)
    (.cat (.flush (.text "PPPPPPPPPPPP")) groupFixture)

#guard (solve 20 nested_groups).map meas.cost == some 1 -- DP: global optimum
#guard (greedy 20 nested_groups).cost == 10 -- greedy `.group`: myopic
#guard (solve 20 nested_groups).map (fun candidate => decide (candidate.maxw ≤ 20)) == some true
#guard ((solve 20 nested_groups).getD default).cost < (greedy 20 nested_groups).cost

-- `.alignOr`: the first feasible align option wins, else the fallback — the
-- renderer's cascade semantics as an (N+1)-candidate `.choice`.
def alignOrFixture : ldoc := align_or [.text "wwwwwwwwwwwwwwww", .text "wwww"] (.flush (.text "w"))

#guard (solve 8 alignOrFixture).map meas.cost == some 0 -- the 4-wide option fits at W=8 → an align option
#guard (solve 3 alignOrFixture).map meas.cost == some 1 -- both options overflow W=3 → the fallback

end Lean4Fmt.Solve
