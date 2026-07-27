# House-style lint hazards

Layout formatting and structural refactoring are separate operations.
`lean4fmt --lint` reports structural hazards without rewriting source or making
existing findings fail the command.

Run the whole inventory:

```sh
make lint-lean
```

Narrow it with the standard `DIR` parameter:

```sh
make lint-lean DIR=src/apps/freeside
```

## Initial rules

- `symbol-length` — a declaration, field, constructor, lambda/binder, `let`,
  loop, or pattern symbol has fewer than `lint.symbolMinChars` characters after
  leading underscores and trailing primes are removed. The Straylight default
  is three characters. Ordinary expression references are never reported.
- `symbol-name` — a non-field binding uses a configured placeholder name
  (`acc,tmp,foo,bar,baz` by default) instead of its semantic role.
- `symbol-instance` — when `lint.requireTraditionalInstances` is enabled, each
  named typeclass-instance binder uses one Greek or Hebrew base letter followed
  only by optional Unicode modifier/subscript characters. Anonymous instance
  binders remain anonymous.
- `symbol-loop-index` — when `lint.requirePositionalLoopNames` is enabled,
  positional bracket-range loops use `idx`, `jdx`, and `kdx` by positional
  nesting depth. Collection loops keep semantic element names and are excluded.
- `symbol-pattern-binder` — when `lint.requireSemanticPatternBinders` is
  enabled, pattern and match-arm binders must meet the configured symbol floor.
  Constructor names, wildcards, `rfl`, and clear-pattern sentinels are excluded.
- `house/match-arm-operations` — a match arm's `do` sequence contains more than
  one statement. Extract a named handler; layout wrapping is not itself a
  structural hazard.
- `house/match-arm-bind-chain` — a match arm directly uses `>>=` with a
  continuation. This catches bind-chain laundering of multi-step work; use a
  clear `do` block (which is then subject to the operation rule) or extract a
  named handler. Bind composition outside match arms is unaffected.
- `house/function-size` — a definition/theorem/instance spans more than 60
  lines. The house target is a screen-sized function of roughly 50 lines.
- `house/branch-density` — an executable `def` or `opaque` body contains more
  than `lint.branchDensityMax` direct `if`, `match`, or loop dispatch points.
  Nested declarations and theorem/proof/instance declarations are excluded.
  The Straylight default is 12; set it to zero to disable the rule.
- `house/handler-parameter-pack` — a declaration has more than
  `lint.handlerParameterMax` explicit value parameters. The Straylight default
  is six. Implicit, strict-implicit, and instance/typeclass binders are
  excluded; set the maximum to zero to disable the rule for a tree.
- `house/state-bundle` — one declaration introduces at least three `let mut`
  locals. Prefer a state structure threaded through named handlers.
- `house/stanza-comment` — when `lint.requireStanzaComments` is enabled, a
  blank-line break inside an executable definition must be followed immediately
  by a comment introducing the next block. Structural `where`,
  `termination_by`, and `decreasing_by` continuations are excluded.
- `house/ruler-width` — a section ruler or module-banner rule has drifted from
  the 81-column house grid.
- `trivia/trailing-whitespace` — a source line ends in spaces or a tab.
- `trivia/final-newline` — a nonempty file lacks its final newline.

Short-name exceptions are exact-length buckets in `fmt.lean`:

```lean
def lint.symbolMinChars := 3
def lint.branchDensityMax := 12
def lint.handlerParameterMax := 6
def lint.requireStanzaComments := true
def lint.requireTraditionalInstances := true
def lint.requirePositionalLoopNames := true
def lint.requireSemanticPatternBinders := true
def lint.symbolAllow.1 := ""
def lint.symbolAllow.2 := "fd,ud"
def lint.symbolDeny := "acc,tmp,foo,bar,baz"
def lint.fieldAllow.2 := "st"
```

Each value is a comma-separated list. Configuration fails loudly if a spelling
does not have exactly the bucket's character count. This keeps `fd` and `ud` as
systems terms of art without granting a blanket exemption to `p`, `w`, or `n`.
Field buckets are role-local: `slot.st` is admitted while a standalone `st`
binding remains a finding.
Set the floor to zero to disable the rule; non-house presets do so by default.

### Tree-local policy

Every `fmt.lean` from the repository root to the source file is applied
outermost to innermost. A nested tree can admit traditional mathematical names
without resetting layout, casing, or unrelated lint policy:

```lean
def lint.symbolPolicy := "traditionalLean"
```

`traditionalLean` admits one-character Greek ordinary binders. Both policies
admit named instance binders consisting of a Greek or Hebrew base letter plus
Unicode subscript/modifier characters. Latin one-letter names remain findings.

Policy patches obey an identity law, associative right-biased composition, and
sequential-application equivalence. These laws are checked in
`Style/Laws.lean`; named policy parsing and exact-bucket validation have
executable checks in `Style/ConfigLaws.lean`. This makes policy revision a new
deterministic fixed point rather than a one-way migration.

Binding-site classification is data-driven through
`Naming.binding_kind_inventory`. Its parser kinds are unique and every entry
round-trips through `role_of_kind`; executable laws in `Rules/NamingLaws.lean`
seal both properties.

The rules are informational because the initial tree is the baseline. Promotion
to warnings or errors should happen per rule only after its backlog is burned
down or explicitly grandfathered.

## Baseline — 2026-07-25

Current 411-file formatter fixed point:

| rule | findings |
|---|---:|
| `symbol-length` | 8179 |
| `symbol-name` | 37 |
| `house/ruler-width` | 0 |
| `house/branch-density` | 20 |
| `house/handler-parameter-pack` | 0 |
| `house/match-arm-bind-chain` | 0 |
| `house/match-arm-operations` | 56 |
| `house/function-size` | 45 |
| `house/state-bundle` | 10 |
| `trivia/trailing-whitespace` | 0 |

Remaining findings are concrete structural refactors rather than formatter
layout failures.
