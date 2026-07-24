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

end Lean4Fmt.Rename
