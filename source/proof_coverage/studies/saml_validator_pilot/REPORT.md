# Rust SAML Validator proof-coverage pilot

Date: 2026-09-15

## Conclusion

The analyzer is ready for guided pilots and data collection on application-sized
Verus packages, including whole-package findings review.

This package produced concrete, developer-judgeable findings. Three sampled
findings were confirmed by source deletion: two loop-invariant clauses were
unnecessary, and one proof branch was unreachable from its precondition. The
analyzer also usefully distinguished intentional dead paths, proof-only
scaffolding, and a clean control function.

The initial whole-package report exposed a consumer scalability defect: the
nominal batch slicer recomputed two whole-graph grounding fixed points for every
terminal. After preparing those policy-specific structures once, the complete
5,283-slice opaque report takes 11.94 seconds. The remaining scaling concern is
materialization: the exhaustive JSON is 369 MB and peaks at 3.5 GB resident
memory, even though the human-readable findings report is only 285 KB. Some
finding kinds also need stronger presentation and severity distinctions before
developers should act on them without inspection.

## Subject and method

The subject was:

```text
/workplace/wmahasai/Verus/src/RustSAMLValidatorPrototype
package commit aef3b82071e55398abc233e949901714df05a922
```

The package working tree already contained local changes. The study used that
exact working tree and did not modify it. Mutations were made in an isolated
copy under `/tmp`.

The analyzer was built from:

```text
Verus commit b3e63d1bc5540a87d551c042a8936af6739f84d7
record pc_r%90bcaa06336554315131979cc74595ca0fc231e9707af566f9573583c20de70b
```

The package contains 32,480 Rust/Verus source lines under `src`, `verus/spec`,
and `verus/proof`. Its custom verification command reports 710 verified and
0 errors.

The pilot performed:

1. A normal verification baseline.
2. A proof-coverage verification and record audit.
3. Function-scoped inspection of five deliberately varied functions.
4. Three deletion-based validation experiments in an isolated package copy.
5. Whole-package report and findings generation.

## Scale and evidence quality

| Measurement | Result |
|---|---:|
| Baseline verification | 710 verified, 0 errors; 53.77 s |
| Coverage verification | 710 verified, 0 errors; 2 min 19 s |
| Coverage record | 51,731,793 bytes |
| Queries | 6,021 |
| Premise occurrences | 19,212; 0 unresolved |
| Source obligations | 4,772; 0 unresolved |
| Measured queries | 5,972 |
| Used premises | 11,093 / 18,784 measured premises |
| Focused queries | 5,311; 5,279 measured |
| Focused average support | 9 labels |
| Audit | all invariants hold |
| Unsupported occurrences with evidence | 0 |
| Whole-package opaque report | 11.94 s; 369,317,623 bytes; 3.5 GB peak RSS |
| Human-readable findings | 11.03 s; 284,576 bytes; 3.2 GB peak RSS |
| Findings | 995 total; 857 defensible; 138 withheld; 182 functions |

As a follow-up to this pilot, evidence collection now reports exact progress
from the buffered query population. A fresh package run identified 5,976
eligible queries across 56 solver contexts, reported completed/total,
percentage, elapsed time, throughput, and ETA at roughly 5% intervals, and
finished evidence collection in 1 min 18 s. Total verification took 2 min 21 s.
The denominator and completed count are exact; ETA remains approximate because
individual solver-query costs vary substantially.

Forty-five focused measurements were not requested because their canonical
batch did not discharge, and four focused checks returned invalid. These were
retained as unmeasured rather than assigned guessed evidence. The analyzed graph
therefore reports 32 unmeasured obligations.

The SST audit reports a high raw span-collision rate—4,118 of 7,161 assumption
rows, or 58%—but exact identities resolved all occurrences in this run. This is
good evidence that source identity cannot safely be recovered from spans alone.

## Confirmed findings

Each mutation below was applied alone to a fresh copy of the original package.
The package still reported 710 verified and 0 errors.

| Analyzer finding | Source change | Result | Interpretation |
|---|---|---:|---|
| `checked-but-unused-proof-step` | Removed `(start as int) < (len as int)` from the first loop in `src/saml/validator/attribute_value_types.rs:259` | Pass, 21.02 s | Confirmed redundant invariant clause |
| `checked-but-unused-proof-step` | Removed `len == s@.len()` from the second loop in `src/saml/validator/attribute_value_types.rs:297` | Pass, 21.12 s | Confirmed redundant invariant clause |
| `vacuous-postcondition` on one terminal | Removed the `if pos >= end { return; }` branch from `lemma_rdn_after_plus_strict_implies_lenient` in `verus/proof/ldap/validator/rfc4514.rs:126` | Pass, 21.09 s | Confirmed dead proof branch; the precondition already excludes it |

The third case is especially important for interpreting vacuity. The lemma's
postcondition is proved normally on its feasible terminal. Only the terminal in
the `pos >= end` branch is vacuous: the branch condition contradicts
`spec_rdn_after_plus_with_eq(..., true, true)`. This is useful dead-path
information, not evidence that the entire lemma is unproved.

## Other useful sampled findings

### Intentional unreachable execution paths

`is_valid_xs_decimal` rechecks whether `dot_char` is a digit after leaving a
loop that would have continued on a digit. The analyzer reports both the return
at `attribute_value_types.rs:281` as `goal-disconnected-code` and the associated
postcondition terminal as vacuous. The source already labels the branch
“Unreachable.” The finding is accurate, but should be informational rather than
presented as a contract defect.

`readback_unreserved_decoded` checks `rlen <= colon_pos` at
`src/uri/validator/uri_normalize.rs:1580`, despite requiring
`colon_pos < result_str@.len()`. The analyzer identifies its early return as
goal-disconnected. This exposes a real contract/body mismatch, but the runtime
guard may be intentional defensive code. It is not automatically a deletion
recommendation.

### Proof-only relevance

Several loop increments, branches, helper postconditions, and invariants were
reported as `auxiliary-only-fact`: they support invariant maintenance,
termination, or other checked auxiliary obligations, but not the selected
postcondition roots. This is useful traceability. In particular, an assignment
such as `j = j + 1` is executable program behavior and should not be rendered as
“unnecessary proof code.”

### Clean negative control

The sampled `has_action` function produced no root-scoped findings. The analyzer
is therefore not merely producing a warning for every inspected function.

## Vacuity interpretation

The graph contains 59 vacuous obligation vertices, while the recorder's
source-obligation summary reports 39 vacuous measured obligations. Inspection
shows many are intentional contradiction checks or infeasible terminals:

- explicit `assert(false)` branches in exhaustive matches;
- contradiction proofs in NameID validation;
- uniqueness and parser lemmas whose branches are excluded by assumptions;
- the decimal and fractional parser rechecks described above;
- strict-to-lenient RFC4514 lemmas with precondition-infeasible branches.

Raw vacuity counts therefore overstate likely defects. Reports should aggregate
by source goal and show extent:

- **all terminals vacuous**: high-priority “goal is not substantively proved”;
- **some terminals vacuous**: dead/infeasible path, normally informational;
- **explicit contradiction proof**: expected proof pattern unless surprising.

## Analyzer defect exposed by the pilot

The first package audit found four occurrences where
`join.emitted_clause` lacked a typed local-clause role. Each involved a final
loop invariant whose expression was a negation. Exact emission metadata had
correctly identified the clause as a loop-exit invariant, but the legacy
positional fallback ran afterward and reclassified it as the loop's negated exit
condition.

The fallback now runs only when exact emission metadata is absent. A regression
probe, `negated_final_invariant`, covers this shape. After rebuilding and
recording the package again:

- all record audit invariants hold;
- all 19,212 premise occurrences and 4,772 source obligations resolve;
- the emission-slot probe passes;
- 79 relevant Rust and integration tests pass.

The pilot fix is confined to `source/proof_coverage`; the subject package was not
changed.

## Consumer scalability defect exposed by the pilot

The first whole-package report attempt produced no output after 16 min 45 s and
was interrupted. Evidence production was already complete; the delay was in
`pc_analyze`.

The graph has 5,311 focused terminals, of which 5,283 require slicing. The
consumer's `backward_slices` implementation called the single-target slicer for
each terminal. Every call rebuilt the strong-arc head index and recomputed two
target-independent whole-graph grounding fixed points. A single slice added
roughly 1.8 seconds beyond record loading, implying a 2.5–3 hour whole-package
run.

The consumer now prepares, once per call policy:

- the strong-arc index by head;
- demand calls indexed by head;
- definite grounding ranks;
- explanation grounding ranks.

The same prepared state is reused across every target. Results:

| Consumer operation | Before | After |
|---|---:|---:|
| Complete opaque report | More than 16 min 45 s; interrupted | 11.94 s |
| List all targets with status | More than 60 s; interrupted | 4.81 s |
| Render findings | Not practical through the whole report | 11.03 s |

The exhaustive report still constructs all query slices and JSON in memory.
That explains its 3.5 GB peak and 369 MB output. This is no longer a latency
blocker on the pilot machine, but should be compacted or streamed before using
the raw report as a routine CI artifact.

## Scaling assessment

### Ready now

- Recording evidence for a package of this size.
- Auditing identity, licensing, and evidence completeness.
- Function-scoped diagnosis.
- Finding redundant invariant clauses.
- Finding infeasible proof branches and selected dead execution paths.
- Showing which facts support goals versus only auxiliary obligations.
- Collecting pilot-study data, provided findings are manually reviewed.
- Whole-package findings rendering and target enumeration.

### Not ready yet

- Treating the 369 MB exhaustive JSON report as a routine CI artifact; it
  currently peaks at approximately 3.5 GB RAM.
- Unattended cleanup based on findings. `goal-disconnected-code`,
  `auxiliary-only-fact`, and partial vacuity have legitimate intentional cases.
- Using raw vacuity or finding-row counts as defect counts.

## Recommended next work

1. Let `findings` render directly from compact report data rather than
   materializing the full 369 MB query-slice JSON. Add streaming or selectable
   detail levels for the exhaustive report.
2. Rank vacuity by extent and recognize explicit contradiction proofs.
3. Present `goal-disconnected-code` on precondition-excluded defensive guards as
   a contract/body observation, not a deletion recommendation.
4. Describe executable `auxiliary-only-fact` rows as proof relevance, and reserve
   “unnecessary proof code” for proof/spec artifacts that survive ablation.
5. Continue the pilot with a stratified sample of high-confidence findings:
   checked-but-unused proof steps, all-terminal vacuity, unused preconditions,
   and unused assertions. Validate a sample from each family by mutation.

The practical recommendation is to continue the pilot at whole-package scale,
using the compact findings view for review and mutation validation. Semantic
ranking remains the main prerequisite for unattended deployment; compact report
materialization is the remaining engineering prerequisite for routine CI use.

The follow-up source-level investigation and mutation results are recorded in
`FINDINGS_TRIAGE.md`.
