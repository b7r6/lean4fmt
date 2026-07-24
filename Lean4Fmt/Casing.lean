/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                             // LEAN4FMT // CASING
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Identifier casing normalization (snake_case ↔ camelCase ↔ UpperCamelCase),
    the verified core of the rename axis. Unlike layout, a rename CHANGES tokens
    — there is no degrade-to-identity floor, so the safety net moves to "the
    project still builds". This core must therefore be right on its own: the
    edges (leading `_`, trailing primes, digit boundaries, idempotence) are
    #guard-locked before a byte is touched.

    Scope: this file is the pure string kernel. The policy (which case per decl
    kind) is config (`Style.Casing`, the packaged straylight preset the default);
    the collection + consistent project-wide rewrite + build validation ride on
    top. Known limit: an all-caps acronym run stays one word (`HTTPServer` →
    `httpserver`), documented rather than mis-split.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Lean4Fmt.Casing

/-- Target casing for an identifier. `preserve` leaves it byte-exact (a per-axis
    opt-out). -/
inductive Case
  | snake
  | camel
  | upperCamel
  | preserve
  deriving Repr, Inhabited, BEq

def Case.of_string? : String → Option Case
  | "snake"      => some .snake
  | "camel"      => some .camel
  | "upperCamel" => some .upperCamel
  | "pascal"     => some .upperCamel
  | "preserve"   => some .preserve
  | _            => none

/-- Capitalize the first character. -/
private
def cap (s : String) : String :=
  match s.toList with
  | []      => ""
  | c :: cs => String.ofList (c.toUpper :: cs)

/-- Split one `_`-free piece on lower/digit → Upper boundaries; each word
    lowercased. An all-caps acronym run stays ONE word (the documented limit). -/
private
def split_piece (s : String) : List String :=
  let (cur, acc) :=
    s.toList.foldl
      (fun (st : List Char × List String) c =>
        let (cur, acc) := st
        let brk := c.isUpper && (cur.getLast?.map (fun p => p.isLower || p.isDigit)).getD false
        if brk then ([c], acc ++ [String.ofList cur]) else (cur ++ [c], acc))
      ([], [])
  (acc ++ (if cur.isEmpty then [] else [String.ofList cur])).map (·.map Char.toLower)

/-- Split an identifier into lowercased words, honoring BOTH snake_case (split on
    `_`) and camel/UpperCamel (split on case boundaries). -/
def split_words (s : String) : List String := (s.splitOn "_").flatMap split_piece |>.filter (· ≠ "")

/-- Join words in the target case. -/
def to_case (c : Case) (ws : List String) : String :=
  match c with
  | .snake => String.intercalate "_" ws
  | .camel =>
    match ws with
    | []        => ""
    | w :: rest => w ++ String.join (rest.map cap)
  | .upperCamel => String.join (ws.map cap)
  | .preserve => String.join ws

/-- Convert an identifier to the target case, preserving a leading `_` run (the
    Lean private/root convention) and a trailing `'` run (primes) as affixes. -/
def convert (c : Case) (s : String) : String :=
  if c == .preserve then
    s
  else
    let cs := s.toList
    let lead := cs.takeWhile (· == '_')
    let rest := cs.drop lead.length
    let trail := (rest.reverse.takeWhile (· == '\'')).reverse
    let core := (rest.reverse.drop trail.length).reverse
    String.ofList lead ++ to_case c (split_words (String.ofList core)) ++ String.ofList trail

-- ── the round-trips, #guard-locked ──────────────────────────────────────────

#guard convert .camel "find_upstream_slot" == "findUpstreamSlot"
#guard convert .snake "findUpstreamSlot" == "find_upstream_slot"
#guard convert .upperCamel "build_system" == "BuildSystem"
#guard convert .snake "BuildSystem" == "build_system"
#guard convert .camel "BuildSystem" == "buildSystem"
#guard convert .upperCamel "findUpstreamSlot" == "FindUpstreamSlot"

-- affixes preserved: leading underscore, trailing prime
#guard convert .camel "_private_helper" == "_privateHelper"
#guard convert .snake "fooBar'" == "foo_bar'"
#guard convert .upperCamel "_root_" == "_Root"

-- digit boundary, single char, already-target, preserve
#guard convert .snake "foo2Bar" == "foo2_bar"
#guard convert .camel "x" == "x"
#guard convert .snake "x" == "x"
#guard convert .camel "already_camel" == "alreadyCamel"
#guard convert .preserve "leave_me_be" == "leave_me_be"

-- IDEMPOTENCE: converting to a case twice equals once (the rename's fixed point)
#guard convert .camel (convert .camel "find_upstream_slot") == convert .camel "find_upstream_slot"
#guard convert .snake (convert .snake "findUpstreamSlot") == convert .snake "findUpstreamSlot"

#guard convert .upperCamel (convert .upperCamel "http_handler") == convert .upperCamel "http_handler"

-- the documented acronym limit (all-caps run collapses to one word)
#guard convert .snake "HTTPServer" == "httpserver"

end Lean4Fmt.Casing
