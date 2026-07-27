/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // RULES // NAMING
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Naming-convention lints. Rules inspect DEFINITION sites only: declaration
    names, binder names, and let-bound identifiers. References do not multiply
    one bad name into a module full of duplicate findings.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import Lean4Fmt.Rules.Diagnostic
import Lean4Fmt.Style.Options

namespace Lean4Fmt.Rules.Naming

open Lean Lean4Fmt.Style

/-- The binding-site role carried alongside a symbol before tree-local policy is
    applied. Roles are deliberately syntax-derived: no elaboration is required,
    and an unrecognized construct receives no speculative exemption. -/
inductive symbol_role
  | declaration
  | localBinder
  | patternBinder
  | matchBinder
  | tacticBinder
  | field
  | instanceBinder
  | loopIndex
  deriving Repr, BEq, DecidableEq

/-- Audited parser nodes that can introduce a source-level name, paired with
    the role their names receive. This is the binding-surface manifest: adding
    a harvester requires adding its parser kind here, where laws can exact-cover
    the classification independently of traversal details. -/
def binding_kind_inventory : List (Name × symbol_role) :=
  [
    (``Lean.Parser.Command.declId, .declaration),
    (``Lean.Parser.Command.ctor, .declaration),
    (``Lean.Parser.Command.structSimpleBinder, .field),
    (``Lean.Parser.Term.instBinder, .instanceBinder),
    (``Lean.Parser.Term.doForDecl, .loopIndex),
    (``Lean.Parser.Term.termFor, .loopIndex),
    (``Lean.Parser.Term.matchAlt, .matchBinder),
    (``Lean.Parser.Term.letPatDecl, .patternBinder),
    (``Lean.Parser.Term.doPatDecl, .patternBinder),
    (``Lean.Parser.Tactic.intro, .tacticBinder),
    (``Lean.Parser.Tactic.renameI, .tacticBinder),
    (`Lean.Parser.Tactic.«tacticNext_=>_», .tacticBinder),
    (``Lean.Parser.Tactic.case, .tacticBinder),
    (`«tacticBy_cases_:_», .tacticBinder),
    (`Lean.Parser.Tactic.tacticSuffices_, .tacticBinder),
    (``Lean.Parser.Tactic.generalize, .tacticBinder),
    (``Lean.Parser.Tactic.inductionAltLHS, .tacticBinder),
    (`Lean.Parser.Tactic.rcasesPat.one, .tacticBinder),
    (``Lean.Parser.Tactic.tacticHave__, .tacticBinder),
    (`Lean.Parser.Tactic.tacticLet__, .tacticBinder),
    (`Lean.Parser.Tactic.tacticHaveI__, .tacticBinder),
    (`Lean.Parser.Tactic.tacticLetI__, .tacticBinder),
    (``Lean.Parser.Tactic.replace, .tacticBinder),
    (`Lean.Parser.Tactic.tacticHave', .tacticBinder),
    (`Lean.Parser.Tactic.tacticLet'__, .tacticBinder),
    (``Lean.Parser.Tactic.letrec, .tacticBinder),
    (``Lean.Parser.Tactic.elimTarget, .tacticBinder),
    (`Lean.Parser.Tactic.injection, .tacticBinder),
    (``Lean.Parser.Term.explicitBinder, .localBinder),
    (``Lean.Parser.Term.implicitBinder, .localBinder),
    (``Lean.Parser.Term.strictImplicitBinder, .localBinder),
    (``Lean.Parser.Term.basicFun, .localBinder),
    (``Lean.Parser.Term.doIdDecl, .localBinder),
    (``Lean.Parser.Term.letIdDecl, .localBinder),
    (``Lean.Parser.Term.letIdDeclNoBinders, .localBinder)
  ]

/-- Classify a syntax node through the audited manifest. `none` means the node
    is not a recognized binding site; callers must not infer an exemption. -/
def role_of_kind (kind : Name) : Option symbol_role :=
  (binding_kind_inventory.find? (·.1 == kind)).map (·.2)

/-- Roles stay diagnostic unless a later, explicit policy says otherwise.
    Pattern, match-arm, and tactic binders are intentionally not blanket
    exemptions. -/
def diagnostic_by_default (_role : symbol_role) : Bool := true

def symbol_role.name : symbol_role → String
  | .declaration    => "declaration"
  | .localBinder    => "local-binder"
  | .patternBinder  => "pattern-binder"
  | .matchBinder    => "match-binder"
  | .tacticBinder   => "tactic-binder"
  | .field          => "field"
  | .instanceBinder => "instance-binder"
  | .loopIndex      => "loop-index"

private partial
def first_ident : Syntax → Option Syntax
  | stx@(.ident ..) => some stx
  | .node _ _ args  => args.findSome? first_ident
  | _               => none

private partial
def ident_leaves (stx : Syntax) (found : Array Syntax := #[]) : Array Syntax :=
  match stx with
  | ident@(.ident ..) => found.push ident
  | .node _ _ args    => args.foldl (fun result child => ident_leaves child result) found
  | _                 => found

private partial
def binder_idents_before_colon (stx : Syntax) (found : Array Syntax := #[]) : Array Syntax × Bool :=
  match stx with
  | ident@(.ident ..) => (found.push ident, false)
  | .atom _ ":" => (found, true)
  | .node _ kind args =>
    if kind == ``Lean.Parser.Term.typeSpec then
      (found, true)
    else
      args.foldl
        (fun state child => if state.2 then state else binder_idents_before_colon child state.1)
        (found, false)
  | _ => (found, false)

private partial
def contains_colon : Syntax → Bool
  | .atom _ ":"    => true
  | .node _ _ args => args.any contains_colon
  | _              => false

private
def core_name (stx : Syntax) : String :=
  let raw :=
    match stx with
    | .ident _ raw _ _ => raw.toString
    | _                => ""
  let tail := (raw.splitOn ".").getLast!
  ((tail.dropWhile (· == '_')).dropEndWhile '\'').toString

private
def allowed_in (buckets : List (Nat × List String)) (name : String) : Bool :=
  (buckets.find? (·.1 == name.length)).any (·.2.contains name)

private
def in_range (char : Char) (lower upper : Nat) : Bool := lower ≤ char.toNat && char.toNat ≤ upper

private
def greek (char : Char) : Bool := in_range char 0x0370 0x03ff || in_range char 0x1f00 0x1fff

private
def hebrew (char : Char) : Bool := in_range char 0x0590 0x05ff

private
def subscript_or_modifier (char : Char) : Bool :=
  in_range char 0x1d2c 0x1d6a || in_range char 0x2070 0x209f

/-- Whether a named instance binder obeys the traditional Lean convention:
    one Greek or Hebrew base letter followed only by modifiers/subscripts. -/
def traditional_instance_name (name : String) : Bool :=
  match name.toList with
  | head :: tail => (greek head || hebrew head) && tail.all subscript_or_modifier
  | []           => false

private
def report
    (policy : Linting)
    (role : symbol_role)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  let name := core_name stx
  let traditional :=
    match role with
    | .field => false
    | .instanceBinder => policy.allowTraditionalInstances && traditional_instance_name name
    | _ =>
      name.length == 1
          && ((policy.allowGreekSymbols && name.toList.any greek)
              || (policy.allowHebrewSymbols && name.toList.any hebrew))
  let roleAllowed :=
    allowed_in policy.symbolAllow name || (role == .field && allowed_in policy.fieldAllow name)
  let pos := (stx.getRange?.map (·.start.byteIdx)).getD 0
  if role == .instanceBinder && policy.requireTraditionalInstances && !name.isEmpty
      && !traditional_instance_name name then
    found.push
      {
        severity := .info
        pos
        rule := "symbol-instance"
        role := role.name
        message := s!"`{name}` is a named instance binder; use a Greek or Hebrew base letter with optional modifier/subscript suffixes"
      }
  else if (role == .patternBinder || role == .matchBinder)
      && policy.requireSemanticPatternBinders && policy.symbolMinChars > 0
      && !name.isEmpty && name.length < policy.symbolMinChars && !roleAllowed && !traditional then
    found.push
      {
        severity := .info
        pos
        rule := "symbol-pattern-binder"
        role := role.name
        message := s!"`{name}` is a short {role.name}; use a semantic name with at least {policy.symbolMinChars} characters"
      }
  else if role != .field && policy.symbolDeny.contains name then
    found.push
      {
        severity := .info
        pos
        rule := "symbol-name"
        role := role.name
        message := s!"`{name}` is a placeholder name; use the value's semantic role"
      }
  else if policy.symbolMinChars == 0 || name.isEmpty || name.length ≥ policy.symbolMinChars
      || roleAllowed
      || traditional then
    found
  else
    found.push
      {
        severity := .info
        pos
        rule := "symbol-length"
        role := role.name
        message := s!"`{name}` has {name.length} characters; minimum is {policy.symbolMinChars}"
      }

private
def report_first (policy : Linting) (stx : Syntax) (found : Array Diagnostic) : Array Diagnostic :=
  match first_ident stx with
  | some ident => report policy .declaration ident found
  | none       => found

private
def report_first_role
    (policy : Linting)
    (role : symbol_role)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  match first_ident stx with
  | some ident => report policy role ident found
  | none       => found

private
def report_binder
    (policy : Linting)
    (role : symbol_role)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  let args := stx.getArgs
  if args.size < 3 then
    found
  else
    let names :=
      (args.extract 1 (args.size - 1)).foldl
        (fun state child =>
          if state.2 then state else binder_idents_before_colon child state.1)
        (#[], false)
      |>.1
    names.foldl (fun result ident => report policy role ident result) found

private
def report_child
    (policy : Linting)
    (role : symbol_role)
    (stx : Syntax)
    (index : Nat)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  match stx.getArgs[index]? with
  | some child =>
    match first_ident child with
    | some ident => report policy role ident found
    | none       => found
  | none => found

private partial
def report_pattern
    (policy : Linting)
    (stx : Syntax)
    (role : symbol_role := .patternBinder)
    (head : Bool := false)
    (found : Array Diagnostic := #[])
    : Array Diagnostic :=
  match stx with
  | ident@(.ident ..) => if head then found else report policy role ident found
  | .node _ kind args =>
    let dotted :=
      (stx.getSubstring? false false).any
        (fun source => source.toString.trimAscii.toString.startsWith ".")
    if dotted then
      (ident_leaves stx).toList.drop 1 |>.foldl
        (fun result ident => report policy role ident result)
        found
    else if kind == ``Lean.Parser.Term.app then
      let found :=
        match args[0]? with
        | some function => report_pattern policy function role true found
        | none          => found
      (args.extract 1 args.size).foldl
        (fun result child => report_pattern policy child role false result)
        found
    else if kind == `null then
      args.foldl (fun result child => report_pattern policy child role head result) found
    else
      args.foldl (fun result child => report_pattern policy child role false result) found
  | _ => found

private
def report_basic_fun
    (policy : Linting)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  match stx.getArgs[0]? with
  | none => found
  | some binders =>
    binders.getArgs.foldl
      (fun result binder =>
        if binder.isIdent then
          report policy .localBinder binder result
        else if binder.getKind == ``Lean.Parser.Term.typeAscription then
          report_child policy .localBinder binder 1 result
        else
          result)
      found

private
def report_pattern_child
    (policy : Linting)
    (role : symbol_role)
    (stx : Syntax)
    (index : Nat)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  match stx.getArgs[index]? with
  | some pattern => report_pattern policy pattern role false found
  | none         => found

private
def report_term_binding
    (policy : Linting)
    (kind : Name)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  if kind == ``Lean.Parser.Term.doIdDecl then
    report_child policy .localBinder stx 0 found
  else if kind == ``Lean.Parser.Term.basicFun then
    report_basic_fun policy stx found
  else if kind == ``Lean.Parser.Term.letPatDecl || kind == ``Lean.Parser.Term.doPatDecl then
    report_pattern_child policy .patternBinder stx 0 found
  else if kind == ``Lean.Parser.Term.doForDecl then
    report_pattern_child policy .loopIndex stx 1 found
  else if kind == ``Lean.Parser.Term.matchAlt then
    report_pattern_child policy .matchBinder stx 1 found
  else
    found

private
def report_binder_site
    (policy : Linting)
    (kind : Name)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  if kind == ``Lean.Parser.Term.explicitBinder || kind == ``Lean.Parser.Term.implicitBinder
      || kind == ``Lean.Parser.Term.strictImplicitBinder then
    report_binder policy .localBinder stx found
  else if kind == ``Lean.Parser.Term.instBinder && contains_colon stx then
    report_binder policy .instanceBinder stx found
  else
    found

private
def report_tactic_binders
    (policy : Linting)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  match stx.getArgs[1]? with
  | some binders =>
    (ident_leaves binders).foldl
      (fun result ident => report policy .tacticBinder ident result)
      found
  | none => found

private
def report_tactic_binders_in_child
    (policy : Linting)
    (stx : Syntax)
    (index : Nat)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  match stx.getArgs[index]? with
  | some binders =>
    (ident_leaves binders).foldl
      (fun result ident => report policy .tacticBinder ident result)
      found
  | none => found

private
def report_case_binders
    (policy : Linting)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  match stx.getArgs[1]? with
  | some alternatives =>
    alternatives.getArgs.foldl
      (fun result alternative => match alternative.getArgs[1]? with
        | some binders =>
          (ident_leaves binders).foldl
            (fun output ident => report policy .tacticBinder ident output)
            result
        | none => result)
      found
  | none => found

private
def report_suffices_binder
    (policy : Linting)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  match stx.getArgs[1]? with
  | some declaration => report_child policy .tacticBinder declaration 0 found
  | none             => found

private
def report_generalize_binders
    (policy : Linting)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  match stx.getArgs[1]? with
  | some arguments =>
    arguments.getArgs.foldl
      (fun result argument =>
        let result := report_child policy .tacticBinder argument 0 result
        report_child policy .tacticBinder argument 3 result)
      found
  | none => found

private
def report_induction_alternative_binders
    (policy : Linting)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  match stx.getArgs[2]? with
  | some binders =>
    (ident_leaves binders).foldl
      (fun result ident => report policy .tacticBinder ident result)
      found
  | none => found

private
def report_rcases_pattern_binder
    (policy : Linting)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  match stx.getArgs[0]? with
  | some ident =>
    let isRfl :=
      match ident with
      | .ident _ raw _ _ => raw.toString == "rfl"
      | _                => false
    if isRfl then found else report policy .tacticBinder ident found
  | none => found

private partial
def report_tactic_config_binders
    (policy : Linting)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  let found :=
    if stx.getKind == ``Lean.Parser.Term.letOptEq then
      report_child policy .tacticBinder stx 3 found
    else
      found
  stx.getArgs.foldl (fun result child => report_tactic_config_binders policy child result) found

private
def report_tactic_binding
    (policy : Linting)
    (kind : Name)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  if kind == ``Lean.Parser.Tactic.intro || kind == ``Lean.Parser.Tactic.renameI
      || kind == `Lean.Parser.Tactic.«tacticNext_=>_» then
    report_tactic_binders policy stx found
  else if kind == ``Lean.Parser.Tactic.case then
    report_case_binders policy stx found
  else if kind == `«tacticBy_cases_:_» then
    report_child policy .tacticBinder stx 1 found
  else if kind == `Lean.Parser.Tactic.tacticSuffices_ then
    report_suffices_binder policy stx found
  else if kind == ``Lean.Parser.Tactic.generalize then
    report_generalize_binders policy stx found
  else if kind == ``Lean.Parser.Tactic.inductionAltLHS then
    report_induction_alternative_binders policy stx found
  else if kind == `Lean.Parser.Tactic.rcasesPat.one then
    report_rcases_pattern_binder policy stx found
  else if kind == ``Lean.Parser.Tactic.elimTarget then
    report_child policy .tacticBinder stx 0 found
  else if kind == `Lean.Parser.Tactic.injection then
    report_tactic_binders_in_child policy stx 2 found
  else if kind == ``Lean.Parser.Tactic.tacticHave__ || kind == `Lean.Parser.Tactic.tacticLet__
      || kind == `Lean.Parser.Tactic.tacticHaveI__
      || kind == `Lean.Parser.Tactic.tacticLetI__
      || kind == `Lean.Parser.Tactic.tacticHave'
      || kind == `Lean.Parser.Tactic.tacticLet'__ then
    match stx.getArgs[1]? with
    | some config => report_tactic_config_binders policy config found
    | none        => found
  else
    found

private
def tactic_declaration_kind (kind : Name) : Bool :=
  kind == ``Lean.Parser.Tactic.tacticHave__ || kind == `Lean.Parser.Tactic.tacticLet__
      || kind == `Lean.Parser.Tactic.tacticHaveI__
      || kind == `Lean.Parser.Tactic.tacticLetI__
      || kind == ``Lean.Parser.Tactic.replace
      || kind == `Lean.Parser.Tactic.tacticHave'
      || kind == `Lean.Parser.Tactic.tacticLet'__

private
def report_let_declaration?
    (policy : Linting)
    (kind : Name)
    (stx : Syntax)
    (found : Array Diagnostic)
    (claimedRole : Option symbol_role)
    : Option (Array Diagnostic) :=
  if kind == ``Lean.Parser.Term.letIdDecl || kind == ``Lean.Parser.Term.letIdDeclNoBinders then
    some
        <| match claimedRole with
        | some role => report_first_role policy role stx found
        | none      => report_first_role policy .localBinder stx found
  else if kind == ``Lean.Parser.Term.letEqnsDecl && claimedRole.isSome then
    some
        <| match claimedRole with
        | some role => report_first_role policy role stx found
        | none      => found
  else if kind == ``Lean.Parser.Term.letPatDecl then
    some
        <| match claimedRole with
        | some role => report_pattern_child policy role stx 0 found
        | none      => report_term_binding policy kind stx found
  else
    none

private partial
def visit
    (policy : Linting)
    (stx : Syntax)
    (found : Array Diagnostic)
    (claimedRole : Option symbol_role := none)
    : Array Diagnostic :=
  let kind := stx.getKind
  let found :=
    match report_let_declaration? policy kind stx found claimedRole with
    | some found => found
    | none =>
      if kind == ``Lean.Parser.Command.declId then
        report_first policy stx found
      else if kind == ``Lean.Parser.Command.structSimpleBinder then
        report_child policy .field stx 1 found
      else if kind == ``Lean.Parser.Command.ctor then
        report_child policy .declaration stx 3 found
      else
        report_tactic_binding
          policy
          kind
          stx
          (report_binder_site policy kind stx (report_term_binding policy kind stx found))
  let children := stx.getArgs
  if tactic_declaration_kind kind && !children.isEmpty then
    let precedingChildren := children.extract 0 (children.size - 1)
    let found := precedingChildren.foldl (fun result child => visit policy child result) found
    visit policy children[children.size - 1]! found (some .tacticBinder)
  else if kind == ``Lean.Parser.Tactic.letrec && children.size > 2 then
    let found := visit policy children[0]! found
    let found := visit policy children[1]! found
    let found := visit policy children[2]! found (some .tacticBinder)
    (children.extract 3 children.size).foldl (fun result child => visit policy child result) found
  else if (kind == ``Lean.Parser.Term.letRecDecls || kind == `null) && claimedRole.isSome then
    children.foldl (fun result child => visit policy child result claimedRole) found
  else if kind == ``Lean.Parser.Term.letRecDecl && claimedRole.isSome then
    children.foldl
      (fun result child =>
        if child.getKind == ``Lean.Parser.Term.letDecl then
          visit policy child result claimedRole
        else
          visit policy child result)
      found
  else if kind == ``Lean.Parser.Term.letDecl && claimedRole.isSome && !children.isEmpty then
    let found := visit policy children[0]! found claimedRole
    (children.extract 1 children.size).foldl (fun result child => visit policy child result) found
  else
    children.foldl (fun result child => visit policy child result) found

private partial
def first_for_decl? (stx : Syntax) : Option Syntax :=
  if stx.getKind == ``Lean.Parser.Term.doForDecl then
    some stx
  else
    stx.getArgs.findSome? first_for_decl?

/-- Whether a loop iterable is bracket-range syntax rather than a collection
    expression. Only this syntax receives positional counter names. -/
def positional_loop_iterable (stx : Syntax) : Bool := stx.getKind.toString.contains "Range."

/-- HFT positional counter name at a nesting depth. Three or more nested
    positional loops saturate at `kdx`; deeper nests should be extracted. -/
def positional_loop_name (depth : Nat) : String :=
  if depth == 0 then "idx" else if depth == 1 then "jdx" else "kdx"

private
def positional_for_decl? (stx : Syntax) : Option Syntax := do
  let declaration ← first_for_decl? stx
  let iterable ← declaration.getArgs[3]?
  if positional_loop_iterable iterable then some declaration
  else none

private
def report_positional_loop
    (policy : Linting)
    (depth : Nat)
    (declaration : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  if !policy.requirePositionalLoopNames then
    found
  else
    match declaration.getArgs[1]? >>= first_ident with
    | none => found
    | some ident =>
      let name := core_name ident
      let expected := positional_loop_name depth
      if name == expected then
        found
      else
        found.push
          {
            severity := .info
            pos := (ident.getRange?.map (·.start.byteIdx)).getD 0
            rule := "symbol-loop-index"
            role := symbol_role.loopIndex.name
            message := s!"positional loop binder `{name}` should be `{expected}` at nesting depth {depth}"
          }

private partial
def lint_positional_loops
    (policy : Linting)
    (stx : Syntax)
    (depth : Nat)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  let declaration :=
    if stx.getKind == ``Lean.Parser.Term.doFor then positional_for_decl? stx else none
  let found :=
    match declaration with
    | some declaration => report_positional_loop policy depth declaration found
    | none             => found
  let children := stx.getArgs
  (Array.range children.size).foldl
    (fun result childIndex =>
      let childDepth :=
        if declaration.isSome && childIndex + 1 == children.size then depth + 1 else depth
      lint_positional_loops policy children[childIndex]! childDepth result)
    found

/-- Flag short names at declaration and binding sites according to the style. -/
def lint (style : Style) (stx : Syntax) : Array Diagnostic :=
  lint_positional_loops style.linting stx 0 (visit style.linting stx #[])

end Lean4Fmt.Rules.Naming
