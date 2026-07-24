/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // SOLVE // LAYOUT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

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
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Lean4Fmt.Solve

/-- A concrete rendering: (indent, text) per line, indent relative to the
    subtree's own left edge. -/
abbrev lines := List (Nat × String)

def lines_maxw (ls : lines) : Nat := ls.foldl (fun m p => max m (p.1 + p.2.length)) 0

def lines_last (ls : lines) : Nat :=
  match ls.getLast? with
  | some p => p.1 + p.2.length
  | none   => 0

/-- Horizontal join: `b` continues `a`'s last line; `b`'s later lines shift
    right by `a`'s last-line width (they were relative to `b`'s left edge). -/
def cat_lines (a b : lines) : lines :=
  match a.getLast? with
  | none => b
  | some pa =>
    let w := pa.1 + pa.2.length
    match b with
    | []          => a
    | pb :: brest => a.dropLast ++ (pa.1, pa.2 ++ pb.2) :: brest.map (fun p => (p.1 + w, p.2))

/-- Newline after `a`: the next content starts a fresh line at relative 0. -/
def flush_lines (a : lines) : lines := a ++ [(0, "")]

/-- Indent everything after the first line by `n`. -/
def nest_lines (n : Nat) (a : lines) : lines :=
  match a with
  | []        => []
  | p :: rest => p :: rest.map (fun q => (q.1 + n, q.2))

structure meas where
  lines : lines
  cost  : Nat
  deriving Inhabited

def meas.maxw (m : meas) : Nat := lines_maxw m.lines
def meas.last (m : meas) : Nat := lines_last m.lines

def cat_m (a b : meas) : meas := { lines := cat_lines a.lines b.lines, cost := a.cost + b.cost }
def flush_m (a : meas) : meas := { a with lines := flush_lines a.lines }
def nest_m (n : Nat) (a : meas) : meas := { a with lines := nest_lines n a.lines }
def pen_m (c : Nat) (a : meas) : meas := { a with cost := a.cost + c }

/-- Dominance: `x` is no worse than `y` in every coordinate that constrains the
    future — max width, last-line width, cost. With additive (monotone) cost a
    dominated partial layout can never extend to a strictly better whole, so we
    drop it. This prune is the whole tractability argument. -/
def dominates (x y : meas) : Bool := x.maxw ≤ y.maxw && x.last ≤ y.last && x.cost ≤ y.cost

def insert_pareto (m : meas) (acc : List meas) : List meas :=
  if acc.any (fun n => dominates n m) then acc else m :: acc.filter (fun n => !dominates m n)

/-- Reduce a candidate set to its Pareto frontier. -/
def prune (ms : List meas) : List meas := ms.foldr insert_pareto []

def cross_cat (fa fb : List meas) : List meas := fa.foldr (fun a acc => fb.map (cat_m a) ++ acc) []

/-- The layout problem: a tree of choice points. `choice` is the constraint
    variable (which alternative); `pen` attaches a preference weight. `group`
    is the degenerate 2-candidate case a Wadler printer bakes in. -/
inductive ldoc where
  | text (s : String)
  | cat (a b : ldoc)
  | flush (a : ldoc)
  | nest (n : Nat) (a : ldoc)
  | choice (alts : List ldoc)
  | pen (c : Nat) (a : ldoc)
  deriving Inhabited

/-- The DP: the Pareto frontier of every layout the subtree admits, computed
    bottom-up. `frontier ∘ choice` is the feasible-set union; `crossCat` is the
    horizontal product; both re-pruned. -/
partial
def frontier : ldoc → List meas
  | .text s      => [{ lines := [(0, s)], cost := 0 }]
  | .cat a b     => prune (cross_cat (frontier a) (frontier b))
  | .flush a     => prune ((frontier a).map flush_m)
  | .nest n a    => prune ((frontier a).map (nest_m n))
  | .pen c a     => prune ((frontier a).map (pen_m c))
  | .choice alts => prune (alts.foldr (fun d acc => frontier d ++ acc) [])

/-- Pick the min-cost layout whose every line fits `W` (the hard constraint).
    If none fits, degrade to the narrowest — the never-worse-than-input floor,
    which the token/comment gate then backstops. -/
def best_under (W : Nat) (f : List meas) : Option meas :=
  let feas := f.filter (fun m => m.maxw ≤ W)
  let pool := if feas.isEmpty then f else feas
  pool.foldl
    (fun best m => match best with
      | none   => some m
      | some b => if m.cost < b.cost || (m.cost == b.cost && m.maxw < b.maxw) then some m else b)
    none

def solve (W : Nat) (d : ldoc) : Option meas := best_under W (frontier d)

/-- The greedy caricature: each `choice` commits to the first alternative that
    fits ON ITS OWN, left-to-right, blind to how downstream placement or cost
    will land. This is the local optimum `.group` printers take. -/
partial
def greedy (W : Nat) : ldoc → meas
  | .text s => { lines := [(0, s)], cost := 0 }
  | .cat a b => cat_m (greedy W a) (greedy W b)
  | .flush a => flush_m (greedy W a)
  | .nest n a => nest_m n (greedy W a)
  | .pen c a => pen_m c (greedy W a)
  | .choice alts =>
    let cands := alts.map (greedy W)
    match cands.find? (fun m => m.maxw ≤ W) with
    | some m => m
    | none   => (cands.getLast?).getD { lines := [(0, "")], cost := 0 }

def render_meas (m : meas) : String :=
  String.intercalate "\n" (m.lines.map (fun p => String.ofList (List.replicate p.1 ' ') ++ p.2))

/-- The affine feasibility of a horizontal composition — the two line-width
    obligations `a fits` and `a.last + b fits` — is exactly what omega discharges
    in the loop. (Scaled up, this is the Farkas/ISL certificate the solver emits.) -/
theorem cat_fits
        (aMax aLast bMax W : Nat)
        (ha : aMax ≤ W)
        (hb : aLast + bMax ≤ W)
        : aMax ≤ W ∧ aLast + bMax ≤ W := by omega

-- ── sanity: the measure algebra ─────────────────────────────────────────────

#guard lines_maxw [(0, "ab"), (2, "cd")] == 4
#guard lines_last [(0, "ab"), (2, "cd")] == 4
#guard render_meas { lines := cat_lines [(0, "let x =")] [(0, "big")], cost := 0 } == "let x =big"

#guard (cat_m { lines := [(0, "ab")], cost := 0 } { lines := [(0, "c"), (0, "d")], cost := 0 }).maxw == 3

-- ── G-L1: the pruned DP is optimal, and the frontier is sub-exponential ─────

/-- Every layout the tree admits, WITHOUT the Pareto prune — the exhaustive
    ground truth `solve` must match on cost. -/
partial
def brute_force : ldoc → List meas
  | .text s      => [{ lines := [(0, s)], cost := 0 }]
  | .cat a b     => cross_cat (brute_force a) (brute_force b)
  | .flush a     => (brute_force a).map flush_m
  | .nest n a    => (brute_force a).map (nest_m n)
  | .pen c a     => (brute_force a).map (pen_m c)
  | .choice alts => alts.foldr (fun d acc => brute_force d ++ acc) []

def brute_opt (W : Nat) (d : ldoc) : Option meas := best_under W (brute_force d)

/-- A chain of `n` break-or-flat segments (the long-application shape): flat is
    5 wide and free, broken is narrow and +1. `2^n` raw layouts. -/
def seg : ldoc := .choice [.pen 0 (.text "xxxxx"), .pen 1 (.cat (.flush (.text "x")) (.text "x"))]

def chain : Nat → ldoc
  | 0     => .text ""
  | n + 1 => .cat seg (chain n)

/-- A def-sig CHOICE whose body is a nested chain — the outer sig branch and the
    inner chain branches compose through the frontier (def ⊃ body, both breaking).
    The exact sig shape is immaterial; the NESTING is the point the DP optimizes. -/
def nested_def (n : Nat) : ldoc :=
  let sig : ldoc :=
    .choice
      [
        .pen 0 (.text "private def f (a : T) : R :="),
        .pen 2 (.cat (.flush (.text "private def f")) (.text "    (a : T) : R :="))
      ]
  .cat sig (.nest 2 (.cat (.flush (.text "")) (chain n)))

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

-- ── G-L3: the live def-path decision (byte-identical wiring) ────────────────

/-- Route a def's INLINE-vs-BREAK decision through the solver: the whole-decl
    inline rung (sig + body on one line, measured width `total`) against an
    always-feasible break rung, selected by `bestUnder` — the hard-width filter
    then the cost argmin, the solver's own selection kernel. Picks inline iff it
    fits, so on a FLAT sig (feasibility is the whole story, greedy meets the
    optimum) it reproduces `total ≤ W` exactly — now COMPUTED by the measure
    algebra, live on the Emit path. The seam G-L4 widens: add the oneLine/fill
    rungs and real preference weights, and this same `bestUnder` starts choosing
    among them. -/
def inline_def_fits (W total : Nat) : Bool :=
  let inlineRung : meas := { lines := [(total, "")], cost := 0 } -- maxw = total, preferred
  let breakRung : meas := { lines := [(0, "")], cost := 2 } -- maxw = 0, always feasible
  (best_under W [inlineRung, breakRung]).map meas.cost == some 0

-- byte-identical to the `total ≤ width` test it replaces, across the boundary
#guard inline_def_fits 100 80 == true -- fits → inline
#guard inline_def_fits 100 100 == true -- exact fit → inline
#guard inline_def_fits 100 101 == false -- over → break
#guard (List.range 220).all (fun t => inline_def_fits 100 t == decide (t ≤ 100)) -- ≡ (total ≤ W)

-- ── G-L4: the preference-map choice over sig shapes ─────────────────────────

/-- The solver's selection kernel, TAGGED: return WHICH rung wins under the hard
    width constraint at least cost (the preference weight) — ties to narrower
    `maxw`, then list order. `bestUnder` returns the winning measure; this
    returns its tag, the shape the caller renders. Adding a candidate layout is
    adding one `(tag, Meas)` pair; the preference map is the cost column. This is
    the "select the most-preferred shape that satisfies the constraint" the whole
    campaign is for, one call. -/
def pick_shape {α : Type} (W : Nat) (rungs : List (α × meas)) : Option α :=
  let feas := rungs.filter (fun r => r.2.maxw ≤ W)
  let pool := if feas.isEmpty then rungs else feas
  (pool.foldl
    (fun best r => match best with
      | none => some r
      | some b =>
        if r.2.cost < b.2.cost || (r.2.cost == b.2.cost && r.2.maxw < b.2.maxw) then some r else b)
    none).map
    (·.1)

/-- The G-L4 sig-shape choice for a BROKEN def: `oneLine` (binders ride the
    keyword line, the return type breaking after the colon if it must) is
    preferred over `onePerLine` (each binder its own line, always feasible).
    oneLine is feasible while the binders fit on the keyword line
    (`prefixW + bindersW ≤ W`); past that they would overflow, so the solver
    drops to the per-line stack. Returns `true` for oneLine. The adaptivity a
    fixed `binders` knob cannot do: the SAME sig rides one line where it fits and
    stacks where it does not, per declaration. -/
def sig_one_line_fits (W prefixW bindersW : Nat) : Bool :=
  (pick_shape
    W
    [
      (true, { lines := [(prefixW + bindersW, "")], cost := 0 }),
      (false, { lines := [(0, "")], cost := 1 })
    ]).getD
    false

-- oneLine while the binders fit on the keyword line, else the per-line stack
#guard sig_one_line_fits 100 12 40 == true -- 12+40=52 ≤ 100 → oneLine
#guard sig_one_line_fits 100 12 90 == false -- 12+90=102 > 100 → onePerLine
#guard (List.range 120).all (fun b => sig_one_line_fits 100 10 b == decide (10 + b ≤ 100))

-- ── G-L5: the fold — `.group` and `.alignOr` are degenerate `.choice` ────────
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
  .choice (opts.map (fun o => ldoc.pen 0 o) ++ [.pen 1 fallback])

def g1 : ldoc := group (.text "iiiiiiiiii") (.cat (.flush (.text "iii")) (.text "iii"))

-- IN ISOLATION the solver reproduces the greedy `.group` decision, and `solve`
-- and `greedy` AGREE — there is no nesting to exploit.
#guard (solve 20 g1).map meas.cost == some 0 -- flat fits (10 ≤ 20) → flat
#guard (solve 5 g1).map meas.cost == some 1 -- flat overflows (10 > 5) → break
#guard (greedy 20 g1).cost == 0 && (greedy 5 g1).cost == 1 -- greedy makes the same call

-- NESTED, they DIVERGE. Two nested groups: the flat outer+inner overflows at
-- 12+10 = 22 > 20, so greedy commits the OUTER to broken (cost 10). The DP keeps
-- the outer FLAT and breaks only the inner (cost 1) — same feasibility, a tenth
-- the cost. `.group` is myopic; `.choice` + the frontier is not.
def nested_groups : ldoc :=
  group_w 10 (.cat (.text "PPPPPPPPPPPP") g1) (.cat (.flush (.text "PPPPPPPPPPPP")) g1)

#guard (solve 20 nested_groups).map meas.cost == some 1 -- DP: global optimum
#guard (greedy 20 nested_groups).cost == 10 -- greedy `.group`: myopic
#guard (solve 20 nested_groups).map (fun m => decide (m.maxw ≤ 20)) == some true -- and it fits
#guard ((solve 20 nested_groups).getD default).cost < (greedy 20 nested_groups).cost

-- `.alignOr`: the first feasible align option wins, else the fallback — the
-- renderer's cascade semantics as an (N+1)-candidate `.choice`.
def ao : ldoc := align_or [.text "wwwwwwwwwwwwwwww", .text "wwww"] (.flush (.text "w"))

#guard (solve 8 ao).map meas.cost == some 0 -- the 4-wide option fits at W=8 → an align option
#guard (solve 3 ao).map meas.cost == some 1 -- both options overflow W=3 → the fallback

end Lean4Fmt.Solve
