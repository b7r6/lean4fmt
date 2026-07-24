/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                             // LEAN4FMT // RENAME
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The rename PLAN: from collected `(name, axis)` declarations + a `Naming`
    policy, decide which project-defined names get renamed to what. Pure — the
    parse-based collection and the token-aware rewrite ride on top.

    A name is renamed iff its target (a) DIFFERS from the source, (b) is UNIQUE
    (no two distinct declared names resolve to one target — a collision), and (c)
    is not a Lean KEYWORD. Otherwise it is SKIPPED (left byte-exact) and reported.
    Collisions count against the FULL resulting name set, so a `fooBar → foo_bar`
    that would clash an already-existing `foo_bar` is skipped, not silently
    merged. Import-overlaps (a target that shadows a library name) are caught by
    the build, the axis's real floor.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Casing
import Lean4Fmt.Style.Options

namespace Lean4Fmt.Rename

open Lean4Fmt.Casing

/-- Last dotted component of a name (`Foo.bar` → `bar`). The one spelling shared
    by the plan, the rewrite, and the driver — a name's simple form. -/
def last_comp (s : String) : String := (s.splitOn ".").getLastD s

/-- Which naming AXIS a declaration falls on — the map from decl kind to the
    `Naming` policy field. -/
inductive axis
  | ns   -- namespace / module
  | typ  -- structure / inductive / class
  | thm  -- theorem / lemma / axiom (Prop-valued)
  | term -- def / abbrev / instance / field
  deriving Repr, Inhabited, BEq

def axis_case (n : Lean4Fmt.Style.Naming) : axis → Case
  | .ns   => n.namespaces
  | .typ  => n.types
  | .thm  => n.theorems
  | .term => n.terms

/-- Lean keywords a target must not become (leave the name, report). Not
    exhaustive — the build is the backstop; this catches the common snake hits. -/
def keywords : List String :=
  ["case", "def", "theorem", "match", "let", "fun", "do", "if", "then", "else", "by", "with",
    "where", "end", "open", "section", "namespace", "structure", "inductive", "class", "instance",
    "example", "mutual", "deriving", "abbrev", "opaque", "axiom", "variable", "universe", "in",
    "from", "at", "show", "have", "suffices", "calc", "return", "for", "while", "try", "catch",
    "extends", "renaming", "hiding", "attribute", "macro", "syntax", "notation", "elab", "set"]

structure plan where
  renames : List (String × String) := [] -- name → target: APPLY these
  skipped : List (String × String) := [] -- name → target: LEAVE (collision / keyword)
  deriving Repr, Inhabited

/-- Build the rename plan. `modules` are the module basenames in play (the file
    stems): a decl whose SOURCE name equals one is EXEMPTED — renaming it would
    also rewrite the module reference in `import`/`open`/`namespace` (the
    `Options → options` / `bad import` class the dogfood surfaced). These are the
    house style's "local exemptions", reported as skipped, not silent. -/
def build_plan
    (policy : Lean4Fmt.Style.Naming)
    (modules : List String)
    (decls : List (String × axis))
    : plan :=

  -- target for EVERY declared name (no-change ones included, so collisions see them)
  let targets := decls.map (fun (nm, ax) => (nm, convert (axis_case policy ax) nm))
  -- dedup by source name (each name declared once)
  let byName := targets.foldl (fun acc p => if acc.any (·.1 == p.1) then acc else acc ++ [p]) []
  let tgtCount := fun t => (byName.filter (·.2 == t)).length
  -- a target is BLOCKED by: a collision (two sources → one target), a keyword,
  -- or the source colliding a module basename (the local exemption)
  let blocked := fun (nm t : String) => tgtCount t > 1 || keywords.contains t || modules.contains nm
  let changed := byName.filter (fun p => p.1 ≠ p.2)
  { renames := changed.filter (fun (nm, t) => !blocked nm t),
    skipped := changed.filter (fun (nm, t) => blocked nm t) }

/-- Rewrite a (possibly dotted) identifier through the rename `map`, component by
    component: `Foo.bar` under `bar ↦ baz` becomes `Foo.baz`. `none` when nothing
    moves (the caller leaves the token byte-exact). This runs over every `.ident`
    leaf on the apply path — matching ANY dotted component catches use-sites
    regardless of qualification; the build is the floor for the rare over-match. -/
def ident_replacement (map : List (String × String)) (name : String) : Option String :=
  let parts := (name.splitOn ".").map (fun p => ((map.find? (·.1 == p)).map (·.2)).getD p)
  let joined := String.intercalate "." parts
  if joined == name then none else some joined

-- ── #guard-locked: the plan's exclusions + the ident rewrite ─────────────────

private
def snake_all : Lean4Fmt.Style.Naming :=
  { namespaces := .upperCamel, types := .snake, theorems := .snake, terms := .snake }

-- clean case: distinct camel terms → distinct snake targets, all applied
#guard (build_plan snake_all [] [("catLines", .term), ("sigOneLineFits", .term)]).renames
    == [("catLines", "cat_lines"), ("sigOneLineFits", "sig_one_line_fits")]

-- keyword exclusion: `Case → case` is a keyword — skipped, `Meas → meas` applied
#guard (build_plan snake_all [] [("Meas", .typ), ("Case", .typ)]).renames == [("Meas", "meas")]
#guard (build_plan snake_all [] [("Case", .typ)]).skipped == [("Case", "case")]

-- collision vs an EXISTING name: `fooBar → foo_bar` would clash the declared
-- `foo_bar`, so it is skipped (not silently merged), and `foo_bar` doesn't move
#guard (build_plan snake_all [] [("fooBar", .term), ("foo_bar", .term)]).renames == []

#guard (build_plan snake_all [] [("fooBar", .term), ("foo_bar", .term)]).skipped == [("fooBar", "foo_bar")]

-- MODULE-BASENAME exemption: `Options` is a module basename → skipped even though
-- `Options → options` is otherwise clean (the dogfood's bad-import class)
#guard (build_plan snake_all ["Options"] [("Options", .typ)]).renames == []
#guard (build_plan snake_all ["Options"] [("Options", .typ)]).skipped == [("Options", "options")]

-- namespaces stay UpperCamel under this policy: no change, no rename
#guard (build_plan snake_all [] [("Freeside", .ns)]).renames == []

-- identReplacement: dotted component rewrite; `none` when nothing moves
#guard Lean4Fmt.Rename.ident_replacement [("bar", "baz")] "Foo.bar" == some "Foo.baz"
#guard Lean4Fmt.Rename.ident_replacement [("bar", "baz")] "bar" == some "baz"
#guard Lean4Fmt.Rename.ident_replacement [("bar", "baz")] "Foo.qux" == none

-- ── G-L7.4d: the resolution rename — rewrite by resolved IDENTITY ─────────────

/-- Rebuild a FULL name, renaming each PREFIX that is a renamed decl (`map`:
    full-name → new-last-component). `A.Foo.bar` under `{A.Foo↦foo, A.Foo.bar↦
    baz}` → `A.foo.baz`. Namespace-only components (not decls, absent from `map`)
    are kept — which is why import/open module paths ride untouched. -/
def rename_full (map : List (String × String)) (full : String) : String :=
  let step :=
    fun (acc : String × List String) (c : String) =>
      let pfx := if acc.1.isEmpty then c else acc.1 ++ "." ++ c
      (pfx, acc.2 ++ [((map.find? (·.1 == pfx)).map (·.2)).getD c])
  String.intercalate "." ((full.splitOn ".").foldl step ("", [])).2

/-- Rewrite one source TOKEN that resolves to `full`, under the identity `map`.
    `none` if nothing in its prefix chain moves (the disambiguation: a token
    resolving to a decl NOT in the map — a same-spelled name in another package —
    is left byte-exact). The token's qualification level is preserved: keep the
    last k components of the renamed full name, where k = the token's own. -/
def resolved_rewrite (map : List (String × String)) (tokenText full : String) : Option String :=

  -- SANITY: the token must actually SPELL the resolved decl's last component.
  -- The InfoTree attributes some source tokens to GENERATED consts — a `deriving
  -- DecidableEq` item to `…ctorIdx`, an anonymous `⟨…⟩` to `…mk` — and rewriting
  -- those corrupts. If the token's tail doesn't match the const's, it isn't a
  -- real spelled reference; leave it byte-exact.
  if last_comp tokenText != last_comp full then none
  else
    let newFull := rename_full map full
    if newFull == full then none
    else
      let k := (tokenText.splitOn ".").length
      let joined := String.intercalate "." (((newFull.splitOn ".").reverse.take k).reverse)
      if joined == tokenText then none else some joined

/-- The RESOLUTION plan: from the full names of DEFINED decls, `(full-name →
    new-last-component)` renames, keyed by IDENTITY. Cross-namespace same
    spellings COEXIST (distinct full names → distinct targets, no collision).
    Dropped iff the new last-component is a keyword, or two decls in the SAME
    namespace collide on it. No module-basename exemption — resolution never
    touches module paths. -/
def plan_resolved
    (c : Case)
    (decls : List String)
    : List (String × String) × List (String × String) :=
  let rows : List (String × String × String × String) :=
    decls.eraseDups.map
      (fun full =>
        let comps := full.splitOn "."
        let last := comps.getLastD full
        let newLast := convert c last
        (full, last, newLast, String.intercalate "." (comps.dropLast ++ [newLast])))
  let collides := fun (nf : String) => (rows.filter (fun (_, _, _, x) => x == nf)).length > 1
  let ok :=
    fun (last newLast newFull : String) =>
      last != newLast && !keywords.contains newLast && !collides newFull
  (
    rows.filterMap
      (fun (full, last, newLast, newFull) =>
        if ok last newLast newFull then some (full, newLast) else none),
    rows.filterMap
      (fun (full, last, newLast, newFull) =>
        if last != newLast && !ok last newLast newFull then some (full, newLast) else none)
  )

/-- The HYBRID plan (G-L7.4e): resolution DECIDES, a token rewrite ACTS. A simple
    name is renamed iff EVERY resolved occurrence of it points to the SAME full
    name that is AUTHORIZED — a real source declaration (`defs`, the declId-captured
    set). Then a plain token rewrite of that name catches every spelling, including
    the structure binder-type positions the InfoTree doesn't record. A spelling
    shared across packages (`isPure` = build's field AND trust's) resolves to ≥2
    full names → ambiguous → left byte-exact.

    Two distinct sets, because they answer distinct questions:
    • `defs` — what may be renamed (authorize). ONLY real source decls; NEVER a
      generated const (an `extends` `toParent` projection, a recursor, a match arm)
      — renaming those breaks, they have no source token.
    • `exists` — every name that EXISTS (all local consts, incl. generated). The
      collision guard checks targets against THIS: a rename onto a taken name is
      unsafe even if the taken name isn't itself renamable.

    `occs` = (lastComponent, fullName) resolved occurrences. Returns
    `(simpleName → target)` renames + skips (keyword/collision/taken). -/
def plan_hybrid
    (c : Case)
    (modules : List String)
    (occs : List (String × String))
    (defs : List String)
    (exists_ : List String)
    : List (String × String) × List (String × String) :=
  let defSet := defs.eraseDups
  let existSet := exists_.eraseDups
  let simples := (occs.map (·.1)).eraseDups
  let fullsOf := fun (s : String) => ((occs.filter (·.1 == s)).map (·.2)).eraseDups
  -- unambiguous (one full name) AND authorized (a real source decl) AND not a
  -- module basename (the token rewrite hits `import`/`open` paths too, so a type
  -- sharing a module name — `Toolchain` in `Toolchain.lean` — must be exempted)
  let rows : List (String × String × String) :=
    simples.filterMap
      (fun s =>
        if modules.contains s then
          none
        else
          match fullsOf s with
          | [full] => if defSet.contains full then some (s, full, convert c s) else none
          | _      => none)
  -- two distinct safe sources snaking to one target collide (both skipped)
  let collides := fun (t : String) => (rows.filter (fun (_, _, x) => x == t)).length > 1
  -- TARGET-TAKEN (the type↔field guard): a rename `S → t` is unsafe if some OTHER
  -- name already EXISTS as `t`. The token rewrite is global-by-simple-name, so the
  -- new `t` shadows that name wherever they share a scope — `Lang → lang` atop the
  -- `lang` FIELD of `target_def`, or `Attr → attr` atop `def attr` (DIFFERENT
  -- namespaces), so the check is identity-aware but namespace-BLIND. Checked against
  -- `existSet` (ALL local consts) so a clash with a non-renamable name still blocks.
  let taken := fun (sFull t : String) => existSet.any (fun d => d != sFull && last_comp d == t)
  let changed := rows.filter (fun (s, _, t) => s != t)
  let ok := fun (sFull t : String) => !keywords.contains t && !collides t && !taken sFull t
  (
    changed.filterMap (fun (s, full, t) => if ok full t then some (s, t) else none),
    changed.filterMap (fun (s, full, t) => if ok full t then none else some (s, t))
  )

-- ── #guard-locked: identity rewrite + resolution plan ────────────────────────

-- HYBRID: unambiguous + authorized → token-renamed; ambiguous / external → left
#guard (plan_hybrid .snake [] [("Resource", "A.Resource"), ("Resource", "A.Resource")] ["A.Resource"] ["A.Resource"]).1
    == [("Resource", "resource")]

#guard (plan_hybrid .snake [] [("isPure", "B.S.isPure"), ("isPure", "T.D.isPure")] ["B.S.isPure"] ["B.S.isPure"]).1 == []

#guard (plan_hybrid .snake [] [("map", "List.map")] [] []).1 == []
-- module-basename exemption: `Toolchain` is a type AND a module → left byte-exact
#guard (plan_hybrid .snake ["Toolchain"] [("Toolchain", "A.Toolchain")] ["A.Toolchain"] ["A.Toolchain"]).1 == []
-- type↔field: a `lang` FIELD (exists but not declId-authorized, different namespace)
-- blocks `Lang → lang` via the target-taken guard on `exists`
#guard (plan_hybrid .snake [] [("Lang", "A.Lang")] ["A.Lang"] ["A.Lang", "A.T.lang"]).1 == []
-- …but with no term already spelling the target, the type renames
#guard (plan_hybrid .snake [] [("Lang", "A.Lang")] ["A.Lang"] ["A.Lang"]).1 == [("Lang", "lang")]
-- generated const (an `extends` `toParent`) EXISTS but is NOT authorized → never renamed
#guard (plan_hybrid .snake [] [("toParent", "A.S.toParent")] [] ["A.S.toParent"]).1 == []

-- prefix-wise full rename: only the mapped prefixes move
#guard rename_full [("A.foo", "foo_x")] "A.foo" == "A.foo_x"
#guard rename_full [("A.Foo", "foo"), ("A.Foo.bar", "baz")] "A.Foo.bar" == "A.foo.baz"
#guard rename_full [("A.foo", "foo_x")] "A.other" == "A.other"

-- token rewrite preserves qualification level (last k components)
#guard resolved_rewrite [("A.foo", "foo_x")] "foo" "A.foo" == some "foo_x"
#guard resolved_rewrite [("A.foo", "foo_x")] "A.foo" "A.foo" == some "A.foo_x"
-- THE DISAMBIGUATION: token `isPure` resolving to Build's is NOT in a map that
-- only holds Trust's `isPure` → left byte-exact
#guard resolved_rewrite [("Trust.D.isPure", "is_pure")] "isPure" "Build.S.isPure" == none
-- SANITY gate: a token whose tail doesn't spell the resolved const (deriving/
-- anonymous-ctor infos → generated `ctorIdx`/`mk`) is left byte-exact
#guard resolved_rewrite [("A.Foo", "foo")] "DecidableEq" "A.Foo.ctorIdx" == none

-- plan: distinct camel decls → distinct snake targets
#guard (plan_resolved .snake ["A.fooBar", "A.bazQux"]).1
    == [("A.fooBar", "foo_bar"), ("A.bazQux", "baz_qux")]
-- same-namespace collision: `A.fooBar` and existing `A.foo_bar` → skipped
#guard (plan_resolved .snake ["A.fooBar", "A.foo_bar"]).1 == []
-- CROSS-namespace same spelling: NO collision, both rename (identity)
#guard (plan_resolved .snake ["A.fooBar", "B.fooBar"]).1
    == [("A.fooBar", "foo_bar"), ("B.fooBar", "foo_bar")]

end Lean4Fmt.Rename
