/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                               // LEAN4FMT // FRONTEND // SESSION
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    THE FRONTEND CONSTRAINT (doc/design.md §4): formatting requires running the
    elaborator over some — as-yet-undetermined — portion of the full artifact,
    because a file's own syntax is extended as it elaborates (notation / macro /
    scoped / open register parser tables; `Type*` only exists post-elaboration).

    The command-loop parser with hand-tracked scope was proven insufficient
    (251/319 commands missing on Mathlib/Logic/Basic). The real path is the
    interleaved parse+elaborate frontend (à la `Lean.Elab.Frontend`), collecting
    each command's `Syntax` as it is elaborated far enough to keep the tables
    current.

    This module will own:
      • the interleaved loop (parse → elaborate-enough → collect syntax),
      • the "how little elaboration" strategy (§14.7: skip proof bodies? a
        parser-tables-only fast path? a per-file budget?),
      • the parse-parallelism strategy (§12: superset-env vs process-per-file).

    Deferred with mathlib. SCAFFOLD ONLY.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import lean_4_fmt.frontend.parse

namespace Lean4Fmt.Frontend.Session

open Lean

/-- How much of a file to elaborate to keep parsing faithful (§14.7). -/
inductive elab_depth
  | importsOnly -- floor: load imports; enough for import-provided notation
  | tablesOnly  -- elaborate just far enough to extend parser tables (skip proofs)
  | full        -- fully elaborate (heaviest; always faithful)
  deriving Repr, Inhabited, BEq

/-- Interleaved parse+elaborate a module against an already-imported `env`: run the
    real frontend (`Lean.Elab.IO.processCommands`), which parses each command with
    the current parser tables and elaborates it far enough to extend them before
    parsing the next — so notation/macros a file introduces (and import-provided
    forms like `Type*`) parse faithfully. Returns a reconstructed `Module.module`
    node `[header, commands]` for the emitter, or `none` if anything is missing.

    This is the `full` depth. It is CPU-heavy (elaborates proof bodies too); the
    caller (`parseFull?`) only reaches it when the cheap parser can't. `tablesOnly`
    (skip proofs) is the planned optimization; the thread pool (Driver.Pool) is the
    planned throughput lever (§12). The env must already be built (imports loaded)
    ONCE per process — re-importing per call is what breaks in-process reuse. -/
unsafe
def parse_module? (env : Environment) (path contents : String) : IO (Option Lean.Syntax) := do
  let ictx := Parser.mkInputContext contents path
  let (hdr, mps, msgs) ← Parser.parseHeader ictx
  -- the tablesOnly depth (§14.7), shipped: `debug.byAsSorry` stubs every
  -- `by` proof during elaboration — parser tables still extend, the
  -- collected SYNTAX is untouched (parsing precedes elaboration), and the
  -- fallback stops inheriting the corpus's proof-elaboration cost (one
  -- mathlib CategoryTheory file burned 9+ CPU-minutes elaborating proofs
  -- it splits "to avoid timeouts" in its own build)
  let opts : Options := Options.empty.setBool `debug.byAsSorry true
  quietly do
    try
      let source ← Lean.Elab.IO.processCommands ictx mps (Lean.Elab.Command.mkState env msgs opts)
      if source.commands.any (·.hasMissing) then pure none
      else pure (some (Syntax.node .none ``Lean.Parser.Module.module #[hdr, mkNullNode source.commands]))
    catch _ => pure none

/-- Flatten every `Info` node of a tree in document order. -/
partial
def collect_infos : Lean.Elab.InfoTree → Array Lean.Elab.Info → Array Lean.Elab.Info
  | .context _ tree, infos => collect_infos tree infos
  | .node info children, infos =>
    children.foldl (fun found child => collect_infos child found) (infos.push info)
  | .hole _, infos => infos

/-- First ident leaf of a subtree — the declId's NAME, dropping any `.{univs}`. -/
partial
def first_ident : Lean.Syntax → Option Lean.Syntax
  | stx@(.ident ..) => some stx
  | .node _ _ args  => args.findSome? first_ident
  | _               => none

private
structure resolution_state where
  resolutions : Array (Nat × Nat × Name × Bool) := #[]
  binders     : Lean.NameSet := {}
  locals      : Array Name := #[]

private
def record_term_info
    (state : resolution_state)
    (term_info : Lean.Elab.TermInfo)
    : resolution_state :=
  let state :=
    if term_info.stx.getKind == `Lean.Parser.Command.declId then
      -- Record the defined constant at the declaration identifier.
      match term_info.expr.getAppFn.consumeMData, (first_ident term_info.stx).bind (·.getRange?) with
      | .const name _, some range =>
        { state with
          resolutions :=
            state.resolutions.push
              (range.start.byteIdx, range.stop.byteIdx, name, true) }
      | _, _ => state
    else
      -- Record every constant-resolving occurrence; the rewrite sanity gate
      -- rejects generated or whole-application ranges that cannot be renamed.
      match term_info.expr.getAppFn.consumeMData, term_info.stx.getRange? with
      | .const name _, some range =>
        { state with
          resolutions :=
            state.resolutions.push
              (range.start.byteIdx, range.stop.byteIdx, name, false) }
      | _, _ => state
  -- Add local binders to the collision set, but never to the rename set.
  term_info.lctx.decls.foldl
    (
      fun state declaration => match declaration with
        | some local_decl =>
          if local_decl.userName.isInternal || local_decl.userName.hasMacroScopes then
            state
          else
            { state with binders := state.binders.insert local_decl.userName }
        | none => state
    )
    state

private
def record_field_info
    (state : resolution_state)
    (field_info : Lean.Elab.FieldInfo)
    : resolution_state :=
  match field_info.stx.getRange? with
  | some range =>
    { state with
      resolutions := state.resolutions.push
        (range.start.byteIdx, range.stop.byteIdx, field_info.projName, false) }
  | none => state

/-- G-L7.4: name-resolution. Elaborate a module with info trees ON, and return,
    for every resolved identifier OCCURRENCE, its source byte range paired with
    the resolved full constant name — a bare `.const` reference, a dot-projection
    (`Term.identProj`, whose node range IS the field and whose const is the app
    head), or a `FieldInfo`. This is exactly what the token map cannot compute:
    it disambiguates two decls that share a spelling across packages (`core/
    build`'s `isPure` vs `core/trust`'s `DischargeProof.isPure`), and it sees
    inside expanded macro/quotation bodies. -/
unsafe
def resolve_idents
    (env : Environment)
    (path contents : String)
    : IO (Array (Nat × Nat × Name × Bool) × Array Name) := do
  let ictx := Parser.mkInputContext contents path
  let (_, mps, msgs) ← Parser.parseHeader ictx
  let st0 := Lean.Elab.Command.mkState env msgs Options.empty
  let commandState := { st0 with infoState := { st0.infoState with enabled := true } }
  quietly
    do
      try
        let processedState ← Lean.Elab.IO.processCommands ictx mps commandState
        let mut state : resolution_state := {}
        -- local BINDER names (fn params, `let`s, `match` vars) in scope at any term.
        -- A type snaking onto a binder name shadows it — `(action : Action)` →
        -- `(action : action)`, where `action → …` then reads the value, not the type.
        -- Binders aren't env consts, so they must be harvested from each term's local
        -- context; they feed the COLLISION set only (never renamed).
        for tree in processedState.commandState.infoState.trees do
          for info in collect_infos tree #[] do
            match info with
            | .ofTermInfo term_info => state := record_term_info state term_info
            | .ofFieldInfo field_info => state := record_field_info state field_info
            | _ => pure ()
        -- the COMPLETE def set the collision/taken guards need — fields,
        -- constructors, every decl — harvested from the SAME elaboration via the
        -- environment's local (stage-2) constant map. One elaboration, so the
        -- worker is DETERMINISTIC; a second parse for fields raced and dropped
        -- defs, letting a type snake onto an unseen term (`Attr` → `attr`). Plus the
        -- local binders (collision-only) that close the type↔binder shadow class.
        state := { state with locals := state.binders.toList.toArray }
        for (name, _) in processedState.commandState.env.constants.map₂.toList do
          unless name.isInternal do state := { state with locals := state.locals.push name }
        -- the elaborator records an ident in several info nodes; dedup exact
        -- (start, stop, name, isDef) so the rewrite never double-edits a range
        pure (state.resolutions.toList.eraseDups.toArray, state.locals)
      catch _ => pure (#[], #[])

end Lean4Fmt.Frontend.Session
