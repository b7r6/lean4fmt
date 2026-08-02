# DAG-aware casing

Module casing is a graph migration. A module's path is its identity in Lean, so
renaming a source file without rewriting its incoming import edges produces an
invalid graph. Declaration resolution alone cannot make that operation sound.

`dag.py` is the source-of-truth inventory and module migration planner. It does
not use a merged olean snapshot to infer module identity. It derives identities
from the owning Lake workspace, declared `srcDir` roots, source paths, and import
headers.

## Soundness gates

1. **Inventory:** every migratable source has exactly one workspace, source
   root, module identity, and content hash. Empty or ambiguous scopes fail.
2. **Graph:** internal imports form a deterministic
   `dependent → dependency` graph. SCCs and workspace SCCs are emitted in
   dependency-first order.
3. **Plan:** target module names and paths are unique and unoccupied. Exact
   identity overrides compose after canonical casing to resolve intentional
   collisions. Every source/path/import/Lake operation is recorded before mutation.
4. **Transaction:** every changed source hash is rechecked, original bytes are
   journaled, all target bytes render before old paths are removed, and any
   executor failure restores the original paths and bytes.
5. **Build:** affected Lake workspaces build in dependency-first order. A failed
   build rolls the source transaction back and cleans/rebuilds affected
   workspaces to remove stale oleans.
6. **Fixed point:** the final filesystem is inventoried from scratch. Success
   requires zero path moves, import rewrites, Lake rewrites, and module changes.

The whole owned tree participates. The algebra study has its own Lake workspace.
The historical `Aleph.CLI`/`Aleph.Cli` collision is resolved explicitly as
`aleph.cli_legacy`/`aleph.cli_11`; no module is protected from the house pass.

## Acronyms

`--acronyms preserve` is the default. Established spellings such as `CLI`,
`APIKey`, `EVRing`, and `SHA256` remain atomic in camel/UpperCamel module names.
`--acronyms normalize` selects the older lossy behavior explicitly.

## Commands

Read-only audit:

```sh
make case-lean-plan
```

Apply the journaled transaction:

```sh
make case-lean-modules
```

Select another policy explicitly:

```sh
LEAN4FMT_MODULE_CASE=upperCamel make case-lean-plan
LEAN4FMT_ACRONYMS=normalize make case-lean-plan
```

The module operation intentionally precedes declaration casing. Once module
paths and imports reach their fixed point and affected oleans have been rebuilt,
the existing elaborator-backed declaration rename can resolve against the new
graph rather than a stale pre-migration snapshot. The `make rename-lean`
entrypoint enforces this order and rebuilds `aleph` plus `lean4fmt` between the
module transaction and declaration-resolution pass.

## Gate record — 2026-08-02

- Fixture suite: 15/15, including collision overrides, Lake root/glob rewrites,
  source-hash races, transaction rollback, and byte-exact recovery.
- Repository inventory: 396 modules, 732 internal edges, 396 SCCs, no cycles.
- Snake transaction: 396 module/path moves, 732 import rewrites, 59 Lake
  root/glob rewrites across fourteen workspaces.
- Every workspace built dependency-first; second plan empty with no protected
  module identities.
