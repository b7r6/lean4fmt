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
import lean_4_fmt.rules.diagnostic
import lean_4_fmt.style.options

namespace Lean4Fmt.Rules.Naming

open Lean Lean4Fmt.Style

/-- The binding-site role carried alongside a symbol before tree-local policy is
    applied. Roles are deliberately syntax-derived: no elaboration is required,
    and an unrecognized construct receives no speculative exemption. -/
inductive symbol_role
  | declaration
  | parameterBinder
  | lambdaBinder
  | letBinder
  | recursiveHelper
  | patternBinder
  | matchBinder
  | tacticBinder
  | field
  | instanceBinder
  | loopIndex
  | collectionElement
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
    (``Lean.Parser.Term.explicitBinder, .parameterBinder),
    (``Lean.Parser.Term.implicitBinder, .parameterBinder),
    (``Lean.Parser.Term.strictImplicitBinder, .parameterBinder),
    (``Lean.Parser.Term.basicFun, .lambdaBinder),
    (``Lean.Parser.Term.letIdDecl, .letBinder),
    (``Lean.Parser.Term.letIdDeclNoBinders, .letBinder),
    (``Lean.Parser.Term.letRecDecl, .recursiveHelper)
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
  | .declaration       => "declaration"
  | .parameterBinder   => "parameter-binder"
  | .lambdaBinder      => "lambda-binder"
  | .letBinder         => "let-binder"
  | .recursiveHelper   => "recursive-helper"
  | .patternBinder     => "pattern-binder"
  | .matchBinder       => "match-binder"
  | .tacticBinder      => "tactic-binder"
  | .field             => "field"
  | .instanceBinder    => "instance-binder"
  | .loopIndex         => "loop-index"
  | .collectionElement => "collection-element"

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

/-- Report a named instance binder that violates the traditional convention. -/
private
def report_instance_name
    (role : symbol_role)
    (name : String)
    (pos : Nat)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  found.push
    {
      severity := .info
      pos
      rule := "symbol-instance"
      role := role.name
      message := s!"`{name}` is a named instance binder; use a Greek or Hebrew base letter with optional modifier/subscript suffixes"
    }

/-- Report a short pattern or match-arm binder that lacks a semantic name. -/
private
def report_pattern_name
    (policy : Linting)
    (role : symbol_role)
    (name : String)
    (pos : Nat)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  found.push
    {
      severity := .info
      pos
      rule := "symbol-pattern-binder"
      role := role.name
      message := s!"`{name}` is a short {role.name}; use a semantic name with at least {policy.symbolMinChars} characters"
    }

/-- Report a collection loop whose binder is short, placeholder-like, or uses
    vocabulary reserved for positional counters. -/
private
def report_collection_element
    (policy : Linting)
    (name : String)
    (pos : Nat)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  found.push
    {
      severity := .info
      pos
      rule := "symbol-loop-collection"
      role := symbol_role.collectionElement.name
      message := s!"`{name}` is a non-semantic collection-loop binder; name the iterated element and reserve idx/jdx/kdx for positional loops (minimum {policy.symbolMinChars} characters)"
    }

/-- Report a short or placeholder-like field that lacks an explicit field-policy
    exception. Fields use their own rule so API-sensitive exceptions remain
    visible and tree-local rather than disappearing into generic symbol debt. -/
private
def report_field_name
    (policy : Linting)
    (qualifiedName : String)
    (pos : Nat)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  found.push
    {
      severity := .info
      pos
      rule := "symbol-field"
      role := symbol_role.field.name
      message := s!"`{qualifiedName}` is a non-semantic field name; spell out its role or admit the exact owner-qualified external/spec name through fieldAllow (minimum {policy.symbolMinChars} characters)"
    }

/-- Report a short or placeholder-like declaration head without a declaration
    policy exception. Constructor diagnostics carry their syntactic owner. -/
private
def report_declaration_name
    (policy : Linting)
    (qualifiedName : String)
    (pos : Nat)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  found.push
    {
      severity := .info
      pos
      rule := "symbol-declaration"
      role := symbol_role.declaration.name
      message := s!"`{qualifiedName}` is a non-semantic declaration name; spell out its role or admit exact conventional/API vocabulary through declarationAllow (minimum {policy.symbolMinChars} characters)"
    }

/-- Report a short term-mode recursive helper head. Recursive helper names have
    their own policy and rule so enabling the semantic gate never also emits the
    generic symbol-floor diagnostic for the same binding site. -/
private
def report_recursive_helper_name
    (policy : Linting)
    (name : String)
    (pos : Nat)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  found.push
    {
      severity := .info
      pos
      rule := "symbol-recursive-helper"
      role := symbol_role.recursiveHelper.name
      message := s!"`{name}` is a non-semantic recursive helper name; spell out the helper's role or admit it through recursiveHelperAllow (minimum {policy.symbolMinChars} characters)"
    }

/-- Report a short lambda binder through its role-local semantic gate. -/
private
def report_lambda_name
    (policy : Linting)
    (name : String)
    (pos : Nat)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  found.push
    {
      severity := .info
      pos
      rule := "symbol-lambda"
      role := symbol_role.lambdaBinder.name
      message := s!"`{name}` is a non-semantic lambda binder; name the callback argument's role or admit it through lambdaAllow (minimum {policy.symbolMinChars} characters)"
    }

/-- Report a short immutable, do-block, or mutable let binder through its
    role-local semantic gate. Assignment targets and resolved uses are not
    binding sites and therefore never reach this reporter. -/
private
def report_let_name
    (policy : Linting)
    (name : String)
    (pos : Nat)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  found.push
    {
      severity := .info
      pos
      rule := "symbol-let"
      role := symbol_role.letBinder.name
      message := s!"`{name}` is a non-semantic let binder; spell out the value's role or admit it through letAllow (minimum {policy.symbolMinChars} characters)"
    }

/-- Whether a named instance binder obeys the traditional Lean convention:
    one Greek or Hebrew base letter followed only by modifiers/subscripts. -/
def traditional_instance_name (name : String) : Bool :=
  match name.toList with
  | head :: tail => (greek head || hebrew head) && tail.all subscript_or_modifier
  | []           => false

private
def report_symbol_floor
    (policy : Linting)
    (role : symbol_role)
    (name : String)
    (traditional roleAllowed : Bool)
    (pos : Nat)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  if role != .field && policy.symbolDeny.contains name then
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
def role_is_traditional (policy : Linting) (role : symbol_role) (name : String) : Bool :=
  match role with
  | .field => false
  | .instanceBinder => policy.allowTraditionalInstances && traditional_instance_name name
  | _ =>
    name.length == 1
        && (
          (policy.allowGreekSymbols && name.toList.any greek)
              || (policy.allowHebrewSymbols && name.toList.any hebrew)
        )

private
def role_is_allowed (policy : Linting) (role : symbol_role) (name : String) : Bool :=
  if role == .lambdaBinder then
    allowed_in policy.lambdaAllow name
  else if role == .letBinder then
    allowed_in policy.letAllow name
  else
    allowed_in policy.symbolAllow name || (role == .field && allowed_in policy.fieldAllow name)
        || (role == .recursiveHelper && allowed_in policy.recursiveHelperAllow name)

private
def semantic_name_valid (policy : Linting) (name : String) (roleAllowed : Bool) : Bool :=
  name.isEmpty || roleAllowed
      || (name.length ≥ policy.symbolMinChars && !policy.symbolDeny.contains name)

private
def report_semantic_role?
    (policy : Linting)
    (role : symbol_role)
    (name : String)
    (roleAllowed : Bool)
    (pos : Nat)
    (found : Array Diagnostic)
    : Option (Array Diagnostic) :=
  if role == .field && policy.requireSemanticFieldNames then
    some found
  else if role == .declaration && policy.requireSemanticDeclarationNames then
    some found
  else if role == .recursiveHelper && policy.requireSemanticRecursiveHelperNames then
    some
        <| if semantic_name_valid policy name roleAllowed then
          found
        else
          report_recursive_helper_name policy name pos found
  else if role == .lambdaBinder && policy.requireSemanticLambdaNames then
    some
        <| if semantic_name_valid policy name roleAllowed then
          found
        else
          report_lambda_name policy name pos found
  else if role == .letBinder && policy.requireSemanticLetNames then
    some
        <| if semantic_name_valid policy name roleAllowed then
          found
        else
          report_let_name policy name pos found
  else
    none

private
def report
    (policy : Linting)
    (role : symbol_role)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  let name := core_name stx
  let traditional := role_is_traditional policy role name
  let roleAllowed := role_is_allowed policy role name
  let pos := (stx.getRange?.map (·.start.byteIdx)).getD 0
  if role == .instanceBinder && policy.requireTraditionalInstances && !name.isEmpty
      && !traditional_instance_name name then
    report_instance_name role name pos found
  else if (role == .patternBinder || role == .matchBinder) && policy.requireSemanticPatternBinders
      && policy.symbolMinChars > 0
      && !name.isEmpty
      && name.length < policy.symbolMinChars
      && !roleAllowed
      && !traditional then
    report_pattern_name policy role name pos found
  else if role == .collectionElement && policy.requireSemanticCollectionLoopNames && !name.isEmpty
      && (
        (
          policy.symbolMinChars > 0 && name.length < policy.symbolMinChars && !roleAllowed
              && !traditional
        )
            || policy.symbolDeny.contains name
            || ["idx", "jdx", "kdx"].contains name
      ) then
    report_collection_element policy name pos found
  else if role == .collectionElement && policy.requireSemanticCollectionLoopNames then
    found
  else
    match report_semantic_role? policy role name roleAllowed pos found with
    | some found => found
    | none       => report_symbol_floor policy role name traditional roleAllowed pos found

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

private
def report_field
    (policy : Linting)
    (owner : Option String)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  match first_ident stx with
  | none => found
  | some ident =>
    if !policy.requireSemanticFieldNames then
      report policy .field ident found
    else
      let name := core_name ident
      let qualifiedName := (owner.map fun ownerName => s!"{ownerName}.{name}").getD name
      let qualifiedAllowed :=
        (policy.fieldAllow.find? (·.1 == name.length)).any fun bucket =>
          bucket.2.any fun entry => entry == qualifiedName || entry.endsWith s!".{qualifiedName}"
      let allowed :=
        allowed_in policy.symbolAllow name || allowed_in policy.fieldAllow name || qualifiedAllowed
      if name.isEmpty || allowed
          || (name.length ≥ policy.symbolMinChars && !policy.symbolDeny.contains name) then
        found
      else
        let pos := (ident.getRange?.map (·.start.byteIdx)).getD 0
        report_field_name policy qualifiedName pos found

private
def report_declaration
    (policy : Linting)
    (owner : Option String)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  match first_ident stx with
  | none => found
  | some ident =>
    if !policy.requireSemanticDeclarationNames then
      report policy .declaration ident found
    else
      let name := core_name ident
      let qualifiedName := (owner.map fun ownerName => s!"{ownerName}.{name}").getD name
      let qualifiedAllowed :=
        (policy.declarationAllow.find? (·.1 == name.length)).any fun bucket =>
          bucket.2.any fun entry => entry == qualifiedName || entry.endsWith s!".{qualifiedName}"
      let allowed := allowed_in policy.declarationAllow name || qualifiedAllowed
      if name.isEmpty || allowed
          || (name.length ≥ policy.symbolMinChars && !policy.symbolDeny.contains name) then
        found
      else
        let pos := (ident.getRange?.map (·.start.byteIdx)).getD 0
        report_declaration_name policy qualifiedName pos found

private
def pattern_ident_is_reference : Syntax → Bool
  | .ident _ raw _ preResolved =>
    raw.toString.contains '.' || preResolved.any fun | .decl .. => true | _ => false
  | _ => false

private
def pattern_is_dotted (args : Array Syntax) : Bool :=
  match (args[0]? : Option Syntax) with
  | some (.atom _ ".") => true
  | _ => false

mutual

  private partial
  def report_pattern
      (policy : Linting)
      (stx : Syntax)
      (role : symbol_role := .patternBinder)
      (head : Bool := false)
      (found : Array Diagnostic := #[])
      : Array Diagnostic :=
    match stx with
    | ident@(.ident ..) =>
      if head || pattern_ident_is_reference ident then found else report policy role ident found
    | .node _ kind args => report_pattern_node policy kind args role head found
    | _ => found

  private partial
  def report_pattern_node
      (policy : Linting)
      (kind : Name)
      (args : Array Syntax)
      (role : symbol_role)
      (head : Bool)
      (found : Array Diagnostic)
      : Array Diagnostic :=
    if kind == ``Lean.Parser.Term.app then
      report_pattern_app policy args role found
    else if kind == ``Lean.Parser.Term.typeAscription then
      match args[1]? with
      | some pattern => report_pattern policy pattern role false found
      | none => found
    else if kind == ``Lean.Parser.Term.inaccessible then
      found
    else if kind == ``Lean.Parser.Term.namedPattern then
      report_named_pattern policy args role head found
    else if pattern_is_dotted args then
      (ident_leaves (.node .none kind args)).toList.drop 1 |>.foldl
        (fun result ident => report policy role ident result)
        found
    else if kind == `null then
      args.foldl (fun result child => report_pattern policy child role head result) found
    else
      args.foldl (fun result child => report_pattern policy child role false result) found

  private partial
  def report_pattern_app
      (policy : Linting)
      (args : Array Syntax)
      (role : symbol_role)
      (found : Array Diagnostic)
      : Array Diagnostic :=
    let found :=
      match args[0]? with
      | some function => report_pattern policy function role true found
      | none => found
    (args.extract 1 args.size).foldl
      (fun result child => report_pattern policy child role false result)
      found

  private partial
  def report_named_pattern
      (policy : Linting)
      (args : Array Syntax)
      (role : symbol_role)
      (head : Bool)
      (found : Array Diagnostic)
      : Array Diagnostic :=
    let found :=
      match args[0]? with
      | some outer => report_pattern policy outer role false found
      | none => found
    let found :=
      match args[2]? with
      | some proof =>
        match first_ident proof with
        | some ident => report policy role ident found
        | none => found
      | none => found
    match args[3]? with
    | some pattern => report_pattern policy pattern role head found
    | none => found

end

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
      (
        fun result binder =>
          if binder.isIdent then
            report policy .lambdaBinder binder result
          else if binder.getKind == ``Lean.Parser.Term.typeAscription then
            report_child policy .lambdaBinder binder 1 result
          else
            result
      )
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

/-- Whether a loop iterable is bracket-range syntax rather than a collection
    expression. Only this syntax receives positional counter names. -/
def positional_loop_iterable (stx : Syntax) : Bool :=
  let kind := stx.getKind
  kind == `Std.Legacy.Range.«term[_:_]» || kind == `Std.Legacy.Range.«term[_:_:_]»
      || kind == `Std.Legacy.Range.«term[:_]»

private
def report_term_binding
    (policy : Linting)
    (kind : Name)
    (stx : Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  if kind == ``Lean.Parser.Term.basicFun then
    report_basic_fun policy stx found
  else if kind == ``Lean.Parser.Term.letPatDecl || kind == ``Lean.Parser.Term.doPatDecl then
    report_pattern_child policy .patternBinder stx 0 found
  else if kind == ``Lean.Parser.Term.doForDecl then
    let role :=
      match stx.getArgs[3]? with
      | some iterable =>
        if positional_loop_iterable iterable then .loopIndex else .collectionElement
      | none => .collectionElement
    report_pattern_child policy role stx 1 found
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
    report_binder policy .parameterBinder stx found
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
      (
        fun result alternative => match alternative.getArgs[1]? with
          | some binders =>
            (ident_leaves binders).foldl
              (fun output ident => report policy .tacticBinder ident output)
              result
          | none => result
      )
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
      (
        fun result argument =>
          let result := report_child policy .tacticBinder argument 0 result
          report_child policy .tacticBinder argument 3 result
      )
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
        | none      => found
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

private
def report_node
    (policy : Linting)
    (kind : Name)
    (stx : Syntax)
    (found : Array Diagnostic)
    (claimedRole : Option symbol_role)
    (fieldOwner : Option String)
    (declarationOwner : Option String)
    : Array Diagnostic :=
  match report_let_declaration? policy kind stx found claimedRole with
  | some found => found
  | none =>
    if kind == ``Lean.Parser.Command.declId then
      match first_ident stx with
      | some declaration => report_declaration policy none declaration found
      | none             => found
    else if kind == ``Lean.Parser.Command.structSimpleBinder then
      match stx.getArgs[1]? with
      | some field => report_field policy fieldOwner field found
      | none       => found
    else if kind == ``Lean.Parser.Command.ctor then
      match stx.getArgs[3]? with
      | some constructor => report_declaration policy declarationOwner constructor found
      | none             => found
    else
      report_tactic_binding
        policy
        kind
        stx
        (report_binder_site policy kind stx (report_term_binding policy kind stx found))

private
def field_owner_at (kind : Name) (stx : Syntax) (inherited : Option String) : Option String :=
  if kind == ``Lean.Parser.Command.structure || kind.toString == "Lean.Parser.Command.class" then
    (stx.getArgs[1]? >>= first_ident).map core_name
  else
    inherited

private
def declaration_owner_at (kind : Name) (stx : Syntax) (inherited : Option String) : Option String :=
  if kind == ``Lean.Parser.Command.inductive then
    (stx.getArgs[1]? >>= first_ident).map core_name
  else
    inherited

private
abbrev descend_fn := Syntax → Array Diagnostic → Option symbol_role → Array Diagnostic

private
def descend_plain
    (descend : descend_fn)
    (children : Array Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  children.foldl (fun result child => descend child result none) found

private
def visit_tactic_declaration
    (descend : descend_fn)
    (children : Array Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  let precedingChildren := children.extract 0 (children.size - 1)
  let found := descend_plain descend precedingChildren found
  descend children[children.size - 1]! found (some .tacticBinder)

private
def visit_tactic_letrec
    (descend : descend_fn)
    (children : Array Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  let found := descend children[0]! found none
  let found := descend children[1]! found none
  let found := descend children[2]! found (some .tacticBinder)
  descend_plain descend (children.extract 3 children.size) found

private
def visit_recursive_declarations
    (descend : descend_fn)
    (children : Array Syntax)
    (claimedRole : Option symbol_role)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  let recursiveRole := claimedRole.getD .recursiveHelper
  children.foldl (fun result child => descend child result (some recursiveRole)) found

private
def visit_claimed_recursive_declaration
    (descend : descend_fn)
    (children : Array Syntax)
    (claimedRole : Option symbol_role)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  children.foldl
    (
      fun result child =>
        if child.getKind == ``Lean.Parser.Term.letDecl then
          descend child result claimedRole
        else
          descend child result none
    )
    found

private
def visit_term_let_declaration
    (descend : descend_fn)
    (declaration : Syntax)
    (siblings : Array Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  if declaration.getKind == ``Lean.Parser.Term.letIdDecl
      || declaration.getKind == ``Lean.Parser.Term.letIdDeclNoBinders then
    let found := descend declaration found (some .letBinder)
    descend_plain descend siblings found
  else
    let found := descend declaration found none
    descend_plain descend siblings found

private
def visit_term_let
    (descend : descend_fn)
    (children : Array Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  children.foldl
    (
      fun result child =>
        if child.getKind == ``Lean.Parser.Term.letDecl then
          match child.getArgs[0]? with
          | some declaration =>
            visit_term_let_declaration
              descend
              declaration
              (child.getArgs.extract 1 child.getArgs.size)
              result
          | none => result
        else
          descend child result none
    )
    found

private
def visit_claimed_let_declaration
    (descend : descend_fn)
    (children : Array Syntax)
    (claimedRole : Option symbol_role)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  let found := descend children[0]! found claimedRole
  descend_plain descend (children.extract 1 children.size) found

private
def visit_reassignment
    (descend : descend_fn)
    (children : Array Syntax)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  children.foldl
    (
      fun result child =>
        if child.getKind == ``Lean.Parser.Term.letIdDeclNoBinders then
          descend_plain descend (child.getArgs.extract 1 child.getArgs.size) result
        else
          descend child result none
    )
    found

private partial
def visit
    (policy : Linting)
    (stx : Syntax)
    (found : Array Diagnostic)
    (claimedRole : Option symbol_role := none)
    (fieldOwner : Option String := none)
    (declarationOwner : Option String := none)
    : Array Diagnostic :=
  let kind := stx.getKind
  let fieldOwner := field_owner_at kind stx fieldOwner
  let declarationOwner := declaration_owner_at kind stx declarationOwner
  let found := report_node policy kind stx found claimedRole fieldOwner declarationOwner
  let children := stx.getArgs
  let descend := fun child result role => visit policy child result role fieldOwner declarationOwner
  if kind == ``Lean.Parser.Term.dynamicQuot then
    found
  else if tactic_declaration_kind kind && !children.isEmpty then
    visit_tactic_declaration descend children found
  else if kind == ``Lean.Parser.Tactic.letrec && children.size > 2 then
    visit_tactic_letrec descend children found
  else if kind == ``Lean.Parser.Term.letRecDecls || kind == ``Lean.Parser.Term.whereDecls then
    visit_recursive_declarations descend children claimedRole found
  else if kind == `null && claimedRole.isSome then
    children.foldl (fun result child => descend child result claimedRole) found
  else if kind == ``Lean.Parser.Term.letRecDecl && claimedRole.isSome then
    visit_claimed_recursive_declaration descend children claimedRole found
  else if kind == ``Lean.Parser.Term.let || kind == ``Lean.Parser.Term.doLet then
    visit_term_let descend children found
  else if kind == ``Lean.Parser.Term.letDecl && claimedRole.isSome && !children.isEmpty then
    visit_claimed_let_declaration descend children claimedRole found
  else if kind == ``Lean.Parser.Term.doReassign then
    visit_reassignment descend children found
  else
    descend_plain descend children found

private partial
def collect_for_declarations (stx : Syntax) (found : Array Syntax := #[]) : Array Syntax :=
  if stx.getKind == ``Lean.Parser.Term.doForDecl then
    found.push stx
  else
    stx.getArgs.foldl (fun result child => collect_for_declarations child result) found

/-- HFT positional counter name at a nesting depth. Three or more nested
    positional loops saturate at `kdx`; deeper nests should be extracted. -/
def positional_loop_name (depth : Nat) : String :=
  if depth == 0 then "idx" else if depth == 1 then "jdx" else "kdx"

private
def loop_declarations (stx : Syntax) : Array Syntax :=
  let children := stx.getArgs
  if children.isEmpty then
    #[]
  else
    (children.extract 0 (children.size - 1)).foldl
      (fun result child => collect_for_declarations child result)
      #[]

private
def positional_for_declaration (declaration : Syntax) : Bool :=
  (declaration.getArgs[3]?).any positional_loop_iterable

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
    match declaration.getArgs[1]? with
    | none => found
    | some pattern =>
      let identifiers := ident_leaves pattern
      match identifiers[0]? with
      | none => found
      | some ident =>
        let name := core_name ident
        let expected := positional_loop_name depth
        if identifiers.size == 1 && name == expected then
          found
        else
          found.push
            {
              severity := .info
              pos := (ident.getRange?.map (·.start.byteIdx)).getD 0
              rule := "symbol-loop-index"
              role := symbol_role.loopIndex.name
              message := s!"positional loop pattern should be the single binder `{expected}` at positional depth {depth}; found `{name}` with {identifiers.size} identifier(s)"
            }

private partial
def lint_positional_loops
    (policy : Linting)
    (stx : Syntax)
    (depth : Nat)
    (found : Array Diagnostic)
    : Array Diagnostic :=
  let children := stx.getArgs
  let loopSyntax :=
    stx.getKind == ``Lean.Parser.Term.doFor || stx.getKind == ``Lean.Parser.Term.termFor
  if loopSyntax && !children.isEmpty then
    let declarations := loop_declarations stx
    let (found, positionalCount) :=
      declarations.foldl
        (
          fun (result, ordinal) declaration =>
            if positional_for_declaration declaration then
              (report_positional_loop policy (depth + ordinal) declaration result, ordinal + 1)
            else
              (result, ordinal)
        )
        (found, 0)
    let bodyIndex := children.size - 1
    let found :=
      (Array.range bodyIndex).foldl
        (fun result childIndex => lint_positional_loops policy children[childIndex]! depth result)
        found
    lint_positional_loops policy children[bodyIndex]! (depth + positionalCount) found
  else
    children.foldl (fun result child => lint_positional_loops policy child depth result) found

/-- Flag short names at declaration and binding sites according to the style. -/
def lint (style : Style) (stx : Syntax) : Array Diagnostic :=
  lint_positional_loops style.linting stx 0 (visit style.linting stx #[])

end Lean4Fmt.Rules.Naming
