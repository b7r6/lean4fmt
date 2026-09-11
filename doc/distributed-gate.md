# The Distributed Trust Gate

Parallel execution creates a second correctness problem beyond linting itself:
every worker must evaluate the same tree under the same policy and executable.
The root therefore plans the work and seals its interpretation before workers
run. Workers execute; they do not discover.

This chapter specifies the protocol used by repository coordinators. The
standalone formatter supplies its worker primitive through `--lint --json`.
Transport and scheduling belong to the consuming CI system.

## 1. Threat model

A naive distributed lint job can report green while omitting or misclassifying
work. Common causes include:

- workers discovering different file sets;
- source changing after shard assignment;
- nested configuration resolving differently on two machines;
- a worker running another formatter build;
- duplicate, missing, or incorrectly owned results;
- a global count hiding a regression in one policy scope;
- an exception ledger changing between plan and merge.

The protocol treats each of these as a verification failure.

## 2. Root authority

The root creates an immutable `manifest.json`. It contains:

- every governed Lean source path in deterministic order;
- each source's SHA-256 fingerprint;
- the formatter and coordinator fingerprints;
- the complete root-to-leaf `fmt.lean` chain for every source;
- each configuration fingerprint;
- the resolved policy and its fingerprint;
- a deterministic exact cover of policy scopes;
- stable shard ownership derived from source path;
- the checked-in clearance-ledger fingerprint;
- a hash sealing the complete manifest.

The root rejects an empty, ambiguous, or incompletely classified inventory
before scheduling anything.

## 3. Worker protocol

A worker receives the manifest and one shard number:

```sh
lean4fmt-distributed run \
  --manifest manifest.json \
  --shard 2 \
  --out shard-2.json
```

Before linting, it verifies the formatter, assigned sources, and governing
configurations against the manifest. It invokes:

```sh
lean4fmt --lint --json <assigned-files...>
```

The worker requires exactly one structured record per assigned file. Every
record carries the manifest, source, and policy fingerprints. A worker cannot
substitute a newly discovered file, silently skip a parse failure, or apply its
local filesystem's policy.

## 4. Merge protocol

The root consumes exactly one artifact for every shard:

```sh
lean4fmt-distributed verify \
  --manifest manifest.json \
  --merged merged.json \
  shard-0.json shard-1.json shard-2.json shard-3.json
```

Verification rejects:

- a changed, foreign, or malformed manifest;
- source, executable, coordinator, configuration, or clearance drift;
- an unclassified file or ambiguous configuration chain;
- inconsistent policy fingerprints within a scope;
- missing, duplicate, extra, or wrongly owned file records;
- missing or duplicate shards;
- malformed structured diagnostics;
- formatter drift when the gate requires a fixed point;
- any error diagnostic;
- any governed count above its independent clearance.

Only after these checks does the root aggregate diagnostics.

## 5. Monotone clearances

The clearance ledger is a ratchet checked in beside the coordinator. Every
governed rule has an independent maximum no greater than the last trusted
census.

This decomposition matters:

- unrelated queues cannot mask a regression;
- one rule can be burned down without waiting for another;
- zero is absorbing—once reached, recurrence fails;
- lowering a count creates evidence, not permanent headroom;
- raising a maximum is an explicit reviewed source change.

Selected informational rules may be promoted to required-zero conditions in the
manifest without changing their source-level severity.

## 6. Exact-cover accounting

Global totals are insufficient when different subtrees resolve different
policies. The manifest partitions files into an exact cover of policy scopes.
Every file belongs to one scope, and each scope has one effective-policy
fingerprint.

Role-sensitive diagnostics such as `symbol-length` are counted by syntactic
role inside each scope. The merger requires agreement among role, scope, and
global totals. An unknown or missing role fails closed rather than entering an
“other” bucket that future policy cannot reason about.

## 7. Composition law

Let `M` be a sealed manifest and `Rᵢ` the verified result of shard `i`. The
merged result is the deterministic union of records keyed by the manifest's
path order:

```text
merge(M, R₀ … Rₙ) = order_M(⋃ records(Rᵢ))
```

Because shard ownership is a function of `M`, regrouping or parallel scheduling
does not change the result. Duplicate union is rejected rather than made
idempotent: two workers claiming one file is evidence of a broken execution
plan.

## 8. Operational boundary

The protocol is independent of a CI vendor, queue, object store, or remote-
execution system. Those systems transport sealed artifacts. They do not resolve
policy, discover source, waive diagnostics, or decide completeness.

That separation is the distributed form of lean4fmt's central rule: machinery
may accelerate a decision, but it does not acquire authority by running farther
from the source.
