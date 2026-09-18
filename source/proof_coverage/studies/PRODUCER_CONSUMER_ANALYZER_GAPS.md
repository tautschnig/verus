# Producer, consumer, and analyzer design-gap review

Date: 2026-09-15

## Bottom line

The current implementation is already a useful **proof-dependency coverage**
analyzer. It can report vacuous obligations, unused proof facts, disconnected
proof steps, selected trusted dependencies, and evidence-completeness gaps.

The SAML and YuccaRust pilots exposed a different class of question:

> Does the verified property observe the important executable behavior and
> preserve it through contracts, specifications, calls, and trust boundaries?

The current record cannot answer that question reliably because its independent
source inventory ends at function metadata, contract-clause spans, and coarse
statement artifacts. It does not yet describe the semantic subjects connected
by those constructs: parameters, result variants and fields, mutable effects,
specification projections, configuration-specific code, or the typed identity
of a trust bridge.

This is not a reason to hardcode knowledge of SAML, authorization, parsers, or
particular field names. The generic extension is:

```text
typed semantic source inventory       observed proof-dependency graph
              \                         /
               \---- assurance graph --/
                         |
                 root-scoped findings
```

The producer should record typed facts that cannot be recovered later. The
consumer should join and scope those facts. The analyzer should make
evidence-bounded claims and rank them.

## What works today

| Capability | Current strength |
|---|---|
| Whole- and partial-terminal vacuity | Direct solver evidence; useful now |
| Unused preconditions, invariants, assertions, lemmas, and reveals | Useful when completeness permits an absence claim |
| Checked but unused proof steps | Useful and mutation-confirmed in both the example corpus and YuccaRust |
| Backward proof slices | Useful for explaining the observed proof argument |
| Forward witness impact | Useful as witness-relative reachability, not as proof necessity |
| Explicit `external_body` dependencies and some `assume`/`admit` dependencies | Useful but incomplete and too coarsely typed |
| Measurement, grounding, attribution, placement, projection, and licensing status | Essential protection against overclaiming |
| Per-function declared-goal analysis | Appropriate for local proof maintenance |

These capabilities should remain. Semantic assurance is an additional view,
not a replacement for proof coverage.

## The central mismatch

The current report is primarily organized around:

```text
function → measured terminals → observed proof facts
```

The developer question from the pilots is organized around:

```text
selected public result/effect
    ← contract
    ← specification
    ← executable behavior and callees
    ← runtime/model trust boundaries
```

Those are related graphs, but they are not the same graph.

In particular:

- a proof function with no postcondition should normally use its assertions as
  proof roots;
- a public executable function with no semantic postcondition should normally
  be reported as an assurance gap;
- falling back to `all-measured` is appropriate for the first case and hides
  the important fact in the second.

The analyzer therefore needs separate **proof roots** and **assurance roots**.

## Producer gaps

The producer owns information that is exact at the VIR/SST/AIR construction
site and unreliable or impossible to infer from a finished report.

### 1. Semantic source subjects

The current `SourceFunction` records mode, visibility, body/trust metadata, and
a function span. Contract artifacts retain clause spans. Body artifacts retain
calls, assignments, branches, loop conditions, return bindings, assertions,
assumptions, and reveals.

What is missing is a typed population of subjects such as:

- function parameters and mutable parameters;
- the return value, datatype variants, and result fields;
- read and written state fields;
- specification/view fields;
- call results and mutable call effects;
- contract clauses and the subjects each clause mentions;
- body regions and the subjects they read, write, construct, or return.

Without that population, the analyzer cannot distinguish:

- a contract that constrains every public result field from one that constrains
  only a Boolean decision;
- a field deliberately projected into a specification from one silently
  replaced by a constant, default, empty, or arbitrary value;
- an input that influences the result from one absent from the assurance chain;
- a side effect covered by a contract from one invisible to it.

The producer need not decide whether a field is important. It should only
record typed entities and relations such as `mentions`, `reads`, `writes`,
`constructs`, `returns`, and `projects-to`.

### 2. Body-to-obligation provenance

`goal-without-body-support` currently asks whether a root slice contains a
local assignment, branch condition, return binding, or loop condition.

This is not a sound proxy for body support. A direct accessor or expression
body can be substituted directly into the final obligation rather than appear
as a labeled premise. This produced many false review rows in both pilots.

The missing evidence is an explicit lowering relation:

```text
source return/body/effect
        → instantiated result expression
        → postcondition obligation
```

This relation means “represented in the obligation,” not necessarily
“logically necessary to every proof.” The latter requires finer solver evidence
or a counterfactual check.

Until this relation exists, `goal-without-body-support` should be treated as an
experimental diagnostic rather than a contract-strength finding.

### 3. Typed trust provenance

The analyzer currently reads source files and searches a source line for
`assume(` or `admit(` to distinguish explicit trust from generated protocol
hypotheses. That is exactly the sort of distinction the producer must preserve
before lowering.

The record should distinguish at least:

- explicit user assumption;
- admission;
- assumed function specification;
- `external_body` contract;
- external function/type model;
- imported verified contract whose defining record is unavailable;
- opaque definition boundary;
- generated protocol hypothesis that is licensed by a checked construct.

For an assumed function specification, the record should retain the bridge:

```text
concrete/runtime operation → assumed specification contract
```

This would have allowed the YuccaRust report to aggregate date, IP, numeric,
Base64, and string-model boundaries directly instead of recovering them by
manual source inspection.

### 4. Configuration-aware source inventory

The current pre-simplified VIR snapshot contains the program selected for the
Verus build. It cannot inventory executable blocks removed by
verification-specific `cfg` selection.

A generic solution requires one of:

1. a pre-`cfg` typed source inventory with each item or region's configuration
   predicate; or
2. inventories from the verification and executable configurations, joined by
   stable source identity and compared by the consumer.

This should produce factual differences such as:

> This validation-affecting body region exists in the executable view and is
> absent from the verification view.

It should not infer whether that difference is a bug.

### 5. Contract and expression shape

Clause spans alone cannot support structural contract findings. The producer
should retain a compact typed summary, or a normalized expression graph, that
can answer:

- does the clause mention the result?
- which parameters, fields, and variants does it mention?
- is it a literal `true` or `false`?
- is the result constrained only under one implication direction?
- which callee/spec predicates and projections occur?

The analyzer can then describe a one-way or result-independent contract without
knowing the application's intended semantics.

### 6. Call and contract composition granularity

Call sites exist as source artifacts, but they are not part of the current
implementation-fact gate. Imported contracts are often observed at aggregate
rather than per-clause granularity.

For semantic composition, the record needs:

- the exact call result and mutable arguments;
- the callee guarantee clauses available at that call;
- which parent contract/spec subjects consume those guarantees;
- clause-level identity where the encoding preserves it.

This supports `callee-guarantee-unconsumed` and field-level parent/child
composition findings without recognizing particular validator names.

### 7. Remaining instrumentation joins

Ungrounded selected roots and unmeasured local clauses are not merely report
noise. They prevent the strongest absence claims.

The producer should continue closing typed gaps for constructs such as:

- loop clauses that are inventoried but not measured;
- invariant-block source identity;
- macro-generated assertions and proof regions;
- query forms whose exported assumptions lack a licensing relation;
- non-SMT proof procedures, represented either by evidence or an explicit
  boundary.

The consumer should report the exact missing join or boundary, not only the
aggregate status.

## Consumer gaps

The consumer owns graph construction, cross-record composition, selected
scope, and derived observations.

### 1. Separate proof-root and assurance-root policies

Keep the current per-function policy for proof maintenance:

```text
declared goals → all measured obligations → none
```

Add an independent assurance-root policy:

```text
explicitly selected roots
    → public local executable functions as a default candidate set
```

For an assurance root, no semantic postcondition is itself an observation. It
must not fall back to internal assertions.

Root selection should be configurable by function identity or annotation. This
is declarative scope selection, not project-specific analyzer logic.

### 2. A real project assurance slice

The current project report computes call-graph-root names but otherwise
aggregates per-function results. It does not recompute findings from selected
top-level assurance roots through the modular call graph.

The project consumer should produce:

```text
selected root
    → root contract subjects
    → consumed callee guarantees
    → implementation subjects
    → trusted boundaries
```

Multiple top-level roots should be retained independently, with an optional
union view. A subject may be covered by one API and absent from another.

### 3. Subject-level joins

Once the producer emits semantic subjects, the consumer should calculate:

- source subjects represented by each selected root;
- subjects present only in implementation or only in specification;
- result fields and variants constrained by each contract;
- effects covered by old/new-state relations;
- fields preserved or dropped by executable-to-spec projections.

These are set differences over typed populations. No application names are
required.

### 4. Trust closure and impact

Trust should be traversed and aggregated from assurance roots, not emitted as a
large list of `(consumer function, trusted artifact)` rows.

A useful row is:

```text
trusted bridge
    kind
    source location
    affected selected roots
    affected result fields/effects
    proof paths reaching it
```

This turns YuccaRust's many low-level occurrences into a small review queue of
runtime/model correspondences.

### 5. Configuration comparison

The consumer should join verification and executable inventories and classify:

- present in both, semantically matched;
- verification-only;
- executable-only;
- same source subject with different body/contract/configuration provenance.

The last two categories are review evidence. They should not automatically be
called unsound.

### 6. Explicit evidence strength

The consumer should keep these claims separate:

- **represented**: a typed source subject reaches the obligation structurally;
- **observed**: a selected solver witness contains the corresponding fact;
- **load-bearing in the observed argument**: blocking it ungrounds the current
  certificate;
- **counterfactually necessary**: re-verification fails after removal or
  weakening;
- **must-use**: present in every proof core.

The current analyzer supports the middle two in limited form. It must not label
them as the final two.

### 7. Compact and incremental materialization

Whole-package records and reports can become much larger than the final review
queue. Project analysis should support:

- streaming or indexed record ingestion;
- cached per-record graph construction;
- root-filtered report materialization;
- summaries that retain stable subject and evidence identifiers without
  repeating every query observation.

This is an engineering gap rather than a semantic one, but it affects whether
the richer analysis can scale.

## Analyzer and report gaps

The analyzer owns finding vocabulary, defensibility gates, ranking, aggregation,
and explanation.

### Findings that current evidence supports well

- whole- and partial-terminal vacuity;
- unused proof/specification facts, subject to completeness;
- checked but unused proof steps;
- unobserved context;
- typed trusted dependencies that actually occur in a selected slice;
- instrumentation and completeness diagnostics.

### Findings that need new evidence

| Candidate finding | Minimum evidence required |
|---|---|
| `root-without-semantic-contract` | Selected executable root, result/effect metadata, and absence of a semantic postcondition |
| `contract-does-not-observe-result` | Contract expression subjects and result identity |
| `result-field-unconstrained` | Result-field inventory and per-clause subject references |
| `result-variant-unconstrained` | Result datatype variants and contract variant references |
| `input-unobserved-by-root` | Parameter/field inventory plus root subject closure |
| `effect-uncovered-by-contract` | Typed writes/mutable effects plus old/new-state contract subjects |
| `body-region-unobserved-by-root` | Explicit body-to-obligation provenance, not merely absence of labeled premises |
| `callee-guarantee-unconsumed` | Call-local guarantee clauses and parent subject consumption |
| `spec-projection-drops-field` | Typed executable-to-spec field mapping |
| `spec-placeholder-value` | Typed projection expression shape; presented as review evidence |
| `runtime-verification-divergence` | Joined inventories from executable and verification configurations |
| `trusted-root-dependency` | Typed trust bridge and project assurance-root closure |
| `one-way-contract` | Normalized result/contract expression shape |

These findings should not be approximated with source-line text searches or
project-specific field-name lists.

### Vacuity needs causal subtypes

The pilots showed that “vacuous” can mean materially different things:

- a whole selected root discharged from contradictory reachable context;
- an admitted theorem represented by an assumed false premise;
- an infeasible branch terminal;
- a duplicated defensive path excluded by an earlier guard.

The report should preserve the solver fact while classifying the cause from
typed provenance. Many vacuous terminals caused by one admission should be
aggregated under that admission rather than presented as independent defects.

### Proof health and assurance health need separate sections

Unused proof premises and removable assertions are valuable, but they should
not outrank:

- a public root with no claim;
- a result field absent from the claim;
- executable validation omitted from the verification build;
- a high-impact trusted runtime/model bridge;
- a wholly vacuous selected root.

A default report should therefore separate:

1. **Assurance-chain breaks**
2. **Trusted boundaries**
3. **Coverage incompleteness**
4. **Proof-maintenance findings**
5. **Traceability information**

`auxiliary-only-fact`, ordinary forward reachability, and infeasible-path
counts are generally traceability, not top-level issues.

### Explanations should show the missing link

The ideal source-level explanation is not merely:

> Assignment X is outside the root slice.

It is:

```text
executable field/effect
    ── represented by ──> local result
    ── missing from ────> function contract
    ── therefore absent from ──> selected public root
```

or:

```text
selected public root
    ── depends on ──> specification predicate
    ── assumes correspondence with ──> runtime parser
```

This format tells the developer where to inspect the chain without claiming to
know the intended requirement.

## A minimal generic data model

The exact wire format needs design work, but the missing concepts can remain
small:

```text
SourceSubject
  id, owner, kind, span, type

SubjectKind
  parameter | result | result_field | state_field | variant
  body_region | effect | call_result | contract_clause | spec_field

SourceRelation
  from, relation, to, provenance

Relation
  mentions | reads | writes | constructs | returns | guards
  calls | consumes_guarantee | projects_to | elaborates_to

TrustBoundary
  id, kind, concrete_subject, specification_subject, span

BuildView
  id, configuration, included_subjects
```

This is an ontology of Verus program structure, not an ontology of SAML,
authorization, parsing, or any other application.

Root selection belongs to analyzer input:

```text
AssuranceScope
  selected function ids
  optional selected result/effect subjects
```

An optional project manifest can identify the externally meaningful roots and
critical outputs. The analyzer remains useful without it by proposing public
local executable functions as candidates.

## Recommended implementation order

### P0: stop or qualify misleading claims

1. Separate proof roots from assurance roots.
2. Emit `root-without-semantic-contract` for selected executable roots instead
   of applying the proof-function fallback.
3. Replace source-text `assume`/`admit` detection with typed producer
   provenance.
4. Downgrade or withhold `goal-without-body-support` until explicit
   body-to-obligation provenance exists.

This immediately improves report quality without requiring field-level
analysis.

### P1: add semantic source evidence

5. Inventory parameters, results, fields, variants, calls, and effects.
6. Record contract/spec expression subject references and simple expression
   shape.
7. Record return/body/effect elaboration into obligations.
8. Record typed trust bridges.

This enables the most useful generic contract-adequacy and trust findings.

### P2: compose whole-package assurance

9. Build selected-root project slices rather than only aggregating
   per-function findings.
10. Add field/effect and callee-guarantee joins.
11. Aggregate trust by boundary and affected assurance roots.
12. Rank assurance-chain breaks separately from proof cleanup.

### P3: compare build views and add expensive confirmation

13. Compare executable and verification configuration inventories.
14. Add targeted automatic counterfactual checks for the highest-ranked rows.
15. Consider all-core may/must classification only where its cost is justified.

Computing all proof cores is not required for the first useful semantic
assurance report.

## Generic acceptance fixtures

The design can be tested without encoding knowledge of either pilot project:

1. A public exec function has internal assertions but no postcondition:
   report `root-without-semantic-contract`.
2. A proof function has no postcondition and proves an assertion:
   retain `all-measured` proof roots without reporting an assurance defect.
3. A direct accessor proves `result == self.field`:
   do not report missing body support.
4. A generated state-machine premise lowers as an assumption:
   do not classify it as a user trust boundary.
5. An external parser is connected by an assumed specification:
   report one typed bridge and every selected root affected by it.
6. A returned struct field is assigned but omitted from the postcondition:
   report `result-field-unconstrained`.
7. A mutable argument is changed but no old/new-state relation mentions it:
   report `effect-uncovered-by-contract`.
8. A spec view replaces one source field with a constant:
   report a projection difference as review evidence.
9. A validation branch exists only in the executable configuration:
   report configuration divergence.
10. A parent calls a verified child but does not consume a relevant guarantee:
    report the unconsumed guarantee at the parent/root boundary.

## Conclusion

The largest remaining gap is not another solver query or another subtype of
unused premise. It is the absence of a typed, independently collected semantic
source graph that can be joined to proof evidence.

The ownership rule is:

- **Producer:** preserve exact typed provenance before lowering erases it.
- **Consumer:** compose source, proof, calls, trust, configuration, and selected
  roots.
- **Analyzer:** issue only evidence-supported claims, aggregate them into
  developer-sized review items, and rank assurance before cleanup.

With that separation, the analyzer can generalize the most interesting pilot
discoveries without hardcoding either project.
