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
    interface. Not yet wired into the Emit path — this is the verified core.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Lean4Fmt.Solve

/-- A concrete rendering: (indent, text) per line, indent relative to the
    subtree's own left edge. -/
abbrev Lines := List (Nat × String)

def linesMaxw (ls : Lines) : Nat := ls.foldl (fun m p => max m (p.1 + p.2.length)) 0

def linesLast (ls : Lines) : Nat :=
  match ls.getLast? with
  | some p => p.1 + p.2.length
  | none   => 0

/-- Horizontal join: `b` continues `a`'s last line; `b`'s later lines shift
    right by `a`'s last-line width (they were relative to `b`'s left edge). -/
def catLines (a b : Lines) : Lines :=
  match a.getLast? with
  | none => b
  | some pa =>
    let w := pa.1 + pa.2.length
    match b with
    | []          => a
    | pb :: brest => a.dropLast ++ (pa.1, pa.2 ++ pb.2) :: brest.map (fun p => (p.1 + w, p.2))

/-- Newline after `a`: the next content starts a fresh line at relative 0. -/
def flushLines (a : Lines) : Lines := a ++ [(0, "")]

/-- Indent everything after the first line by `n`. -/
def nestLines (n : Nat) (a : Lines) : Lines :=
  match a with
  | []        => []
  | p :: rest => p :: rest.map (fun q => (q.1 + n, q.2))

structure Meas where
  lines : Lines
  cost  : Nat
  deriving Inhabited

def Meas.maxw (m : Meas) : Nat := linesMaxw m.lines
def Meas.last (m : Meas) : Nat := linesLast m.lines

def catM (a b : Meas) : Meas := { lines := catLines a.lines b.lines, cost := a.cost + b.cost }
def flushM (a : Meas) : Meas := { a with lines := flushLines a.lines }
def nestM (n : Nat) (a : Meas) : Meas := { a with lines := nestLines n a.lines }
def penM (c : Nat) (a : Meas) : Meas := { a with cost := a.cost + c }

/-- Dominance: `x` is no worse than `y` in every coordinate that constrains the
    future — max width, last-line width, cost. With additive (monotone) cost a
    dominated partial layout can never extend to a strictly better whole, so we
    drop it. This prune is the whole tractability argument. -/
def dominates (x y : Meas) : Bool := x.maxw ≤ y.maxw && x.last ≤ y.last && x.cost ≤ y.cost

def insertPareto (m : Meas) (acc : List Meas) : List Meas :=
  if acc.any (fun n => dominates n m) then acc else m :: acc.filter (fun n => !dominates m n)

/-- Reduce a candidate set to its Pareto frontier. -/
def prune (ms : List Meas) : List Meas := ms.foldr insertPareto []

def crossCat (fa fb : List Meas) : List Meas := fa.foldr (fun a acc => fb.map (catM a) ++ acc) []

/-- The layout problem: a tree of choice points. `choice` is the constraint
    variable (which alternative); `pen` attaches a preference weight. `group`
    is the degenerate 2-candidate case a Wadler printer bakes in. -/
inductive LDoc where
  | text (s : String)
  | cat (a b : LDoc)
  | flush (a : LDoc)
  | nest (n : Nat) (a : LDoc)
  | choice (alts : List LDoc)
  | pen (c : Nat) (a : LDoc)
  deriving Inhabited

/-- The DP: the Pareto frontier of every layout the subtree admits, computed
    bottom-up. `frontier ∘ choice` is the feasible-set union; `crossCat` is the
    horizontal product; both re-pruned. -/
partial
def frontier : LDoc → List Meas
  | .text s      => [{ lines := [(0, s)], cost := 0 }]
  | .cat a b     => prune (crossCat (frontier a) (frontier b))
  | .flush a     => prune ((frontier a).map flushM)
  | .nest n a    => prune ((frontier a).map (nestM n))
  | .pen c a     => prune ((frontier a).map (penM c))
  | .choice alts => prune (alts.foldr (fun d acc => frontier d ++ acc) [])

/-- Pick the min-cost layout whose every line fits `W` (the hard constraint).
    If none fits, degrade to the narrowest — the never-worse-than-input floor,
    which the token/comment gate then backstops. -/
def bestUnder (W : Nat) (f : List Meas) : Option Meas :=
  let feas := f.filter (fun m => m.maxw ≤ W)
  let pool := if feas.isEmpty then f else feas
  pool.foldl
    (fun best m => match best with
      | none   => some m
      | some b => if m.cost < b.cost || (m.cost == b.cost && m.maxw < b.maxw) then some m else b)
    none

def solve (W : Nat) (d : LDoc) : Option Meas := bestUnder W (frontier d)

/-- The greedy caricature: each `choice` commits to the first alternative that
    fits ON ITS OWN, left-to-right, blind to how downstream placement or cost
    will land. This is the local optimum `.group` printers take. -/
partial
def greedy (W : Nat) : LDoc → Meas
  | .text s => { lines := [(0, s)], cost := 0 }
  | .cat a b => catM (greedy W a) (greedy W b)
  | .flush a => flushM (greedy W a)
  | .nest n a => nestM n (greedy W a)
  | .pen c a => penM c (greedy W a)
  | .choice alts =>
    let cands := alts.map (greedy W)
    match cands.find? (fun m => m.maxw ≤ W) with
    | some m => m
    | none   => (cands.getLast?).getD { lines := [(0, "")], cost := 0 }

def renderMeas (m : Meas) : String :=
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

#guard linesMaxw [(0, "ab"), (2, "cd")] == 4
#guard linesLast [(0, "ab"), (2, "cd")] == 4
#guard renderMeas { lines := catLines [(0, "let x =")] [(0, "big")], cost := 0 } == "let x =big"

#guard (catM { lines := [(0, "ab")], cost := 0 } { lines := [(0, "c"), (0, "d")], cost := 0 }).maxw == 3

-- ── the money case: greedy's local commit vs the DP's global optimum ────────
-- W = 20.  A 12-wide prefix P then a nested inner choice.  Something must break
-- to fit.  Breaking the INNER costs 1; breaking the OUTER costs 10; both fit.
-- Greedy tries the whole flat (overflows at 12+10=22), so it breaks the OUTER
-- and lands cost 10.  The DP sees that keeping the outer flat and breaking only
-- the inner also fits — for cost 1.

def inner : LDoc :=
  .choice
    [
      .pen 0 (.text "iiiiiiiiii"), -- flat, 10 wide, free
      .pen 1 (.cat (.flush (.text "iii")) (.text "iii")) -- broken, narrow, +1
    ]

def whole : LDoc :=
  .choice
    [
      .pen 0 (.cat (.text "PPPPPPPPPPPP") inner), -- flat outer
      .pen 10 (.cat (.flush (.text "PPPPPPPPPPPP")) inner) -- broken outer, +10
    ]

-- the optimum is cost 1 and fits; greedy pays 10 for the same feasibility
#guard (solve 20 whole).map Meas.cost == some 1
#guard (solve 20 whole).map (fun m => decide (m.maxw ≤ 20)) == some true
#guard (greedy 20 whole).cost == 10
#guard ((solve 20 whole).getD default).cost < (greedy 20 whole).cost

-- ── a real `def` as a choice-tree: the rung ladder ─────────────────────────
-- Two candidate shapes with preference weights. The solver picks the cheapest
-- that fits — so the SAME signature inlines when there's room and hangs when
-- there isn't, per declaration. A fixed `binders` knob can't do that.

def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

def joinSp (xs : List String) : String :=
  xs.foldl (fun s x => if s.isEmpty then x else s ++ " " ++ x) ""

/-- Rung 0: everything on one line. -/
def defInline (vis kw name : String) (bs : List String) (ret : String) : LDoc :=
  .text (joinSp ([vis, kw, name] ++ bs) ++ " : " ++ ret ++ " :=")

/-- Rung 1: the pinned house shape — `private` own line, `def name` at col 0,
    binders and colon hanging at +4 (indent baked into the line text). -/
def defHang (vis kw name : String) (bs : List String) (ret : String) : LDoc :=
  let ls : List LDoc :=
    [.text vis, .text (kw ++ " " ++ name)] ++ bs.map (fun b => .text (spaces 4 ++ b))
        ++ [.text (spaces 4 ++ ": " ++ ret ++ " :=")]
  match ls.getLast? with
  | none      => .text ""
  | some last => ls.dropLast.foldr (fun l acc => .cat (.flush l) acc) last

def defDoc (vis kw name : String) (bs : List String) (ret : String) : LDoc :=
  .choice [.pen 0 (defInline vis kw name bs ret), .pen 2 (defHang vis kw name bs ret)]

def exBs : List String :=
  ["(pool : Array upstream_slot)", "(slot_predicate : pooled_upstream_state → Bool)"]

def exDef : LDoc := defDoc "private" "def" "find_upstream_slot" exBs "Option Nat"

#guard (solve 200 exDef).map Meas.cost == some 0 -- inline wins
#guard (solve 100 exDef).map Meas.cost == some 2 -- hang forced
#guard (solve 100 exDef).map (fun m => decide (m.maxw ≤ 100)) == some true -- and it fits

-- ── G-L1: the pruned DP is optimal, and the frontier is sub-exponential ─────

/-- Every layout the tree admits, WITHOUT the Pareto prune — the exhaustive
    ground truth `solve` must match on cost. -/
partial
def bruteForce : LDoc → List Meas
  | .text s      => [{ lines := [(0, s)], cost := 0 }]
  | .cat a b     => crossCat (bruteForce a) (bruteForce b)
  | .flush a     => (bruteForce a).map flushM
  | .nest n a    => (bruteForce a).map (nestM n)
  | .pen c a     => (bruteForce a).map (penM c)
  | .choice alts => alts.foldr (fun d acc => bruteForce d ++ acc) []

def bruteOpt (W : Nat) (d : LDoc) : Option Meas := bestUnder W (bruteForce d)

/-- A chain of `n` break-or-flat segments (the long-application shape): flat is
    5 wide and free, broken is narrow and +1. `2^n` raw layouts. -/
def seg : LDoc := .choice [.pen 0 (.text "xxxxx"), .pen 1 (.cat (.flush (.text "x")) (.text "x"))]

def chain : Nat → LDoc
  | 0     => .text ""
  | n + 1 => .cat seg (chain n)

/-- def-sig ladder whose body is a nested chain — def contains body, both
    branching, composed through the frontier. -/
def nestedDef (n : Nat) : LDoc :=
  .cat (defDoc "private" "def" "f" ["(a : T)"] "R") (.nest 2 (.cat (.flush (.text "")) (chain n)))

-- optimality: the pruned DP finds the SAME optimal cost as exhaustive search
#guard (solve 12 (chain 6)).map Meas.cost == (bruteOpt 12 (chain 6)).map Meas.cost
#guard (solve 20 (chain 8)).map Meas.cost == (bruteOpt 20 (chain 8)).map Meas.cost
#guard (solve 60 (nestedDef 6)).map Meas.cost == (bruteOpt 60 (nestedDef 6)).map Meas.cost
#guard (solve 30 (nestedDef 5)).map Meas.cost == (bruteOpt 30 (nestedDef 5)).map Meas.cost

-- tractability: monotone cost ⇒ the prune keeps the frontier sub-exponential
#guard (bruteForce (chain 8)).length == 256 -- 2^8 raw layouts …
#guard (frontier (chain 8)).length ≤ 12 -- … collapse to a handful
#guard (bruteForce (chain 12)).length == 4096 -- 2^12 …
#guard (frontier (chain 12)).length ≤ 16 -- … still a handful (grows ~n)
#guard (frontier (nestedDef 6)).length ≤ 12

-- ── G-L2: the def bridge, validated on real ServeFd signatures ──────────────

/-- The pieces Emit extracts from a `def`'s declModifiers/declId/declSig — the
    bridge's input contract (Emit canonTok's the Syntax into these strings). -/
structure DefPieces where
  vis     : String := ""
  kw      : String := "def"
  name    : String
  binders : List String := []
  ret     : String

/-- The rung ladder for a def signature: inline and hang, with preference
    weights. (Weights become config in G-L4; here inline-when-it-fits.) -/
def defLadder (p : DefPieces) : LDoc :=
  .choice
    [
      .pen 0 (defInline p.vis p.kw p.name p.binders p.ret),
      .pen 2 (defHang p.vis p.kw p.name p.binders p.ret)
    ]

def renderDef (W : Nat) (p : DefPieces) : String :=
  renderMeas ((solve W (defLadder p)).getD default)

def fxFindUpstream : DefPieces :=
  { vis     := "private",
    name    := "find_upstream_slot",
    binders := ["(pool : Array upstream_slot)", "(slot_predicate : pooled_upstream_state → Bool)"],
    ret     := "Option Nat" }

def fxFindIdle : DefPieces :=
  { vis     := "private",
    name    := "find_idle_upstream_slot",
    binders := ["(pool : Array upstream_slot)"],
    ret     := "Option Nat" }

def fxDial : DefPieces :=
  { vis     := "private",
    name    := "dial_upstream_slot",
    binders := ["(loop : Loop)", "(pool : Array upstream_slot)", "(idx : Nat)", "(port : UInt16)"],
    ret     := "IO (Array upstream_slot)" }

def fxAll : List DefPieces := [fxFindUpstream, fxFindIdle, fxDial]

-- byte-lock: at the house width, the bridge reproduces the EXACT pinned shape
#guard renderDef 100 fxFindUpstream == "private\ndef find_upstream_slot\n    (pool : Array upstream_slot)\n    (slot_predicate : pooled_upstream_state → Bool)\n    : Option Nat :="

-- width-optimal (== brute force) and feasible on every real sig at width 100
#guard fxAll.all (fun p => (solve 100 (defLadder p)).map Meas.cost == (bruteOpt 100 (defLadder p)).map Meas.cost)

#guard fxAll.all (fun p => decide (((solve 100 (defLadder p)).getD default).maxw ≤ 100))

-- adaptivity on the real sig: inline with room (W=200), hang without (W=100)
#guard (solve 200 (defLadder fxFindUpstream)).map Meas.cost == some 0
#guard (solve 100 (defLadder fxFindUpstream)).map Meas.cost == some 2

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
def inlineDefFits (W total : Nat) : Bool :=
  let inlineRung : Meas := { lines := [(total, "")], cost := 0 } -- maxw = total, preferred
  let breakRung : Meas := { lines := [(0, "")], cost := 2 } -- maxw = 0, always feasible
  (bestUnder W [inlineRung, breakRung]).map Meas.cost == some 0

-- byte-identical to the `total ≤ width` test it replaces, across the boundary
#guard inlineDefFits 100 80 == true -- fits → inline
#guard inlineDefFits 100 100 == true -- exact fit → inline
#guard inlineDefFits 100 101 == false -- over → break
#guard (List.range 220).all (fun t => inlineDefFits 100 t == decide (t ≤ 100)) -- ≡ (total ≤ W)

-- ── G-L4: the preference-map choice over sig shapes ─────────────────────────

/-- The solver's selection kernel, TAGGED: return WHICH rung wins under the hard
    width constraint at least cost (the preference weight) — ties to narrower
    `maxw`, then list order. `bestUnder` returns the winning measure; this
    returns its tag, the shape the caller renders. Adding a candidate layout is
    adding one `(tag, Meas)` pair; the preference map is the cost column. This is
    the "select the most-preferred shape that satisfies the constraint" the whole
    campaign is for, one call. -/
def pickShape {α : Type} (W : Nat) (rungs : List (α × Meas)) : Option α :=
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
def sigOneLineFits (W prefixW bindersW : Nat) : Bool :=
  (pickShape
    W
    [
      (true, { lines := [(prefixW + bindersW, "")], cost := 0 }),
      (false, { lines := [(0, "")], cost := 1 })
    ]).getD
    false

-- oneLine while the binders fit on the keyword line, else the per-line stack
#guard sigOneLineFits 100 12 40 == true -- 12+40=52 ≤ 100 → oneLine
#guard sigOneLineFits 100 12 90 == false -- 12+90=102 > 100 → onePerLine
#guard (List.range 120).all (fun b => sigOneLineFits 100 10 b == decide (10 + b ≤ 100))

end Lean4Fmt.Solve
