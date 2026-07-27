# Trustworthy distributed lint gate

The distributed gate makes the root's view authoritative. Workers do not
discover their own file set or silently resolve a different policy.

Run the complete local simulation:

```sh
make lint-lean-distributed
```

`SHARDS` and the artifact directory are knobs:

```sh
make lint-lean-distributed SHARDS=8 \
  LINT_GATE_DIR=.lean4fmt/ci-run
```

## Monotone clearances

[`clearances.json`](clearances.json) is the checked-in ratchet. Every governed
rule has an independent maximum equal to or below the last trusted root census.
The merge fails when any count rises above its maximum; reductions create
headroom until the same change lowers the checked-in maximum.

This decomposes style convergence into tight, monotone clearances:

- unrelated queues cannot mask a regression;
- a rule may be burned down without waiting for the others;
- zero is absorbing—once a clearance reaches zero, any recurrence fails;
- raising a maximum is an explicit reviewed source change, never worker state.

The default Make target always seals this ledger into the manifest:

```sh
make lint-lean-distributed
```

Require selected informational queues to be genuinely green:

```sh
make lint-lean-distributed \
  LINT_FAIL_ON="trivia/trailing-whitespace house/ruler-width"
```

## Protocol

The root creates `manifest.json`, containing:

- every governed Lean source path in deterministic order;
- its SHA-256 source fingerprint;
- the SHA-256 of the formatter executable;
- the SHA-256 of the distributed-gate coordinator;
- the SHA-256 of the tree runner that establishes the Lean environment;
- the SHA-256 of the checked-in clearance ledger;
- its complete root-to-leaf `fmt.lean` chain and each config fingerprint;
- its unique effective policy scope (the preset or innermost `fmt.lean`), plus
  a deterministic exact-cover summary for every scope;
- merge-time `symbol-length` totals by syntactic role within each policy scope;
- an effective-policy fingerprint, including the base preset;
- stable shard ownership derived from the source path;
- a hash sealing the complete manifest.

A worker receives the immutable manifest and its integer shard:

```sh
scripts/lean4fmt-distributed.py run \
  --manifest manifest.json \
  --shard 2 \
  --out shard-2.json
```

Before linting, the worker verifies the executable, every assigned source, and
every governing config. It invokes `lean4fmt --lint --json`, requires exactly
one structured record for every assigned file, and stamps each result with the
manifest's source and policy fingerprints.

The root merges one result per shard:

```sh
scripts/lean4fmt-distributed.py verify \
  --manifest manifest.json \
  --merged merged.json \
  shard-0.json shard-1.json shard-2.json shard-3.json
```

The merge rejects:

- a changed, foreign, or malformed manifest;
- an unclassified file, duplicate file resolution, ambiguous config chain, or
  inconsistent policy fingerprint within a scope;
- a missing or unknown `symbol-length` role, or any mismatch between role,
  scope, and global diagnostic totals;
- source, formatter, or configuration drift;
- missing, duplicate, extra, or wrongly-owned file records;
- missing or duplicate shards;
- formatter drift (`changed = true`);
- error diagnostics.
- any rule count above its independent checked-in clearance.

Informational lint findings remain inventory rather than gate failures. Their
canonical counts live in `merged.json`; agents report deltas against that
artifact, never against ad hoc greps of human logs. `--fail-on RULE` (or
`LINT_FAIL_ON` through Make) promotes selected inventories to required-zero
merge conditions without changing their source-level severity.
