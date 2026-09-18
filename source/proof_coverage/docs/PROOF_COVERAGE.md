# Proof Coverage for Verus
* [Design](PROOF_COVERAGE_DESIGN.md)
* [Limitations](PROOF_COVERAGE_GAPS.md)

## Motivation

A successful verification run establishes that its proof obligations were discharged, 
but does not provide information about which proof facts were used to establish 
these obligations.

In this work, we present a proof coverage tool for Verus, that traces proof dependencies 
through the verification-condition generation pipeline, and uses solver evidence to 
identify important proof facts. As a result, it provides source-level explanations 
of successful proofs, and actionable findings including vacuity, unused specifications, 
and redundant proof facts. This aims to help developers understand, debug, and maintain 
verified software.

## Invariants


01. Canonical verification is not instrumented, and not affected by other changes to TCB.
02. Use thee observer architecture (from proof state) for minimal changes to TCB.
03. Analysis should never be done over regexes.
04. Every attributed proof fact has a registered provenance rule. 
05. Coverage information and analysis is deterministic for a fixed seed.


## Coverage Record

We use five tables to store VCG metadata for coverage analysis.

```rust
Artifact         // written by user, or constructed by encoding
SstSite          // location in lowered body
Occurrence       // { id, role, carrier } - info for single AIR query
Emission         // proof facts semantics via encoding
SourceProjection // what source construct it represents
Evidence         // observed by solver
```

```text
Query        1 : N  Occurrence
Occurrence   1 : 1  Emission
Occurrence   0 : N  SourceProjection
Obligation   1 : N  Terminal
Terminal     1 : 1  FocusedQuery   1 : 1  Evidence
```

### Identity

A function is its raw VIR path ( `crate::impl&%0::view` ), which is `FunX.path`
and therefore injective. Verus's friendly rendering discards the impl disambiguator 
and the self type's type arguments, so it is not injective and is display metadata 
only ( `SourceFunction.friendly` )

Across records an artifact is identified by the crate that defines its owner, so
a callee's contract aggregate imported into a caller is the same vertex as the
aggregate in the record that verified the callee. 

### Typed fields

* `artifacts[].kind`,   `.owner`,   `.parent`,   `.callee`,   `.cfg_node`
* `artifacts[].group` for loop invariant clauses (`invariant_except_break`, 
`invariant` , `loop_ensures` ), from `vir::sst::LoopInv` 's flag pairing
* `refinements`: `(impl method, trait method)` pairs from
`vir::ast::FunctionKind::TraitMethodImpl`  
* `occurrences[].emission`: typed `EmissionRole`
* `source_functions[]`: every function of the pre-simplified crate, local or
  imported, with its mode, kind, item, module, visibility, body visibility, 
  opaqueness, `has_body` , `external_body` , `broadcast` and span

## Solver Evidence

A measured focused query contributes one atomic evidence edge. When the
terminal is observed it is a support witness,

```text
{premise occurrence 1, ..., premise occurrence n, background}
    jointly supports
terminal occurrence
```

- If the terminal is absent, the remaining accepted core is a contradiction
witness, that is, it explains verificaiton succeeded without any obligation
- We use sets to represent joint dependencies
- A batch core is one joint observation `{core premises} → {core obligations}` . It
cannot say which obligation consumed which premise, so it is weak and excluded
from derivation. Each obligation's available-premise scope is stored separately; 
terminal children inherit their parent obligation's scope.

## Checked-export protocols

An established fact is licensed by one shape, instantiated per construct. A
checked export is a triple `(hypotheses H, goal obligation G, exported
assumption E) ` whose construction guarantees ` E ` is admitted only after ` G` is
discharged under `H` . The analyzer materializes `CertifiedBy(H ∪ {G}) → E` .

| instance | H | G | E |
|---|---|---|---|
| user assert | — | `assert.check` | `assert.establish` |
| assert-by (nonlinear, bit_vector) | `lemma.requires_assume` | `lemma.goal` | `lemma.ensures_assume` |
| assert-forall | `forall.hypothesis` | `forall.goal` | `forall.establish` |
| loop clause | `loop.body_assume` | `loop.maintain` | `loop.exit_assume` |
| guarded recursion | decreases guard | — | `call.post` |

Loop licensing tails come from the clause's declared group, not from one assumed
shape:

```text
invariant_except_break  at_entry, not at_exit   entry ⊢ body; no exit export
invariant               at_entry and at_exit    entry ⊢ body; entry+latch ⊢ exit
loop_ensures            at_exit only            latch/transfer ⊢ exit
```

An assert-forall region is identified structurally: a `DeadEnd` whose premises
open with `AssertForallRequire` , whose last obligation is the forall goal, 
followed by a sibling statement carrying the exported `AssertForallEnsures`

assumption. Pairing uses the exact sibling statement path, so nested regions
stay distinct.

A user assertion is one `assertion` artifact ( `<fun>#assert@<cfg-node>` ) with
two occurrences: the check at `assert.check` and the exported assumption at
`assert.establish` , paired construction-exactly by the producer walk
( `join.assert_site` ). Asserts without exact CFG placement stay unjoined.
Generated checked conditions that are re-assumed (overflow checks, for example)
are paired the same way and receive no invented source artifact.

A trait-method implementation's obligations project onto the trait's clause
artifacts through the recorded `(impl, trait)` relation; the impl's own ensures
checks then license those clauses through the ordinary contract certificate, 
which is refinement. The owner check is not relaxed — the audit requires the
recorded relation.

## 6. Slices

An intraprocedural result is parameterized by a set of selected terminal roots.
For roots `R` , the slice is the least grounded fixed point of the productive
strong hyperedges reachable backwards from `R` .

An edge `T → h` is productive only when every member of its joint tail `T` was
grounded before `h` . So a loop or recursion cycle cannot justify itself, and a
certified cycle becomes traversable through its independently checked base and
step obligations. Nested loops need no nested algorithm: one global monotone
fixed point reaches inner certificates while expanding the outer slice.

Roots are an explicit, reported parameter:

```text
declared-goals   postcondition terminals of the function (default)
all-measured     every measured terminal
call-graph-roots functions no observed call site targets (project scope)
```

Because a slice is relative to a root set, a finding that says "unused" names the
root set it is relative to. Every function reports `root_policy` and, when it is
not the default, `root_reason`:

```text
declared-goals  postcondition terminals            "unused by declared goals"
all-measured    fallback, root_reason =            "unused by all measured
                no-declared-goals-fallback          obligations"
none            root_reason = no-measured-terminals no findings emitted
```

A function with no postcondition — typically a `proof fn` whose purpose *is* its
assertions — has no declared goals, and falls back to `all-measured`. Without
the fallback its root set is empty, every candidate is trivially "outside every
root slice", and the survivor rule does no filtering at all. A function with no
measured terminal either selects nothing and reports only its state.

### Boundaries

* Ordinary calls are opaque in intraprocedural mode: the caller can depend on an
  imported callee postcondition and its local precondition check, but the slice
  stops before the callee body.
* Calls and recursion are call-local licensing relations, not static arcs. An
  ordinary call is based on the callee's ensures aggregate; a recursive call on
  *that call's* own decrease guard, so the hypothesis is never licensed by the
  function's own ensures check and well-foundedness is decided per call rather
  than per component. No component certificate is materialized.
* A call's tail also carries every precondition check the caller discharged.
  Restricting it to the clauses the callee's proof used needs a per-clause
  measurement that v0.1 does not take ( `PROOF_COVERAGE_GAPS.md` §4.1a).
* In opaque mode a guarded call to another member of a mutual-recursion
  component is an imported boundary; the local precondition and decreases checks
  remain in the slice. Modular mode follows the same edge into the other
  member's proof.
* Trait method calls follow what the encoding emitted. A statically resolved
  call ( `CallTargetKind::DynamicResolved` ) assumes the implementation's own
  postcondition, so the callee is the implementation and modular mode expands
  into its proof. A generic call assumes the trait method's postcondition; its
  clauses are certified, in modular mode, by the refinement checks of every
  recorded implementation jointly — one `CertifiedBy` tail — and the slice
  records a `trait_contract` boundary naming them, since implementations in
  other crates are outside the record.
* An unmeasured focused query contributes possible in-scope facts and an
  explicit unmeasured boundary. It contributes no observed witness.
* An unresolved attribution stays a typed gap. It is not repaired by name, 
  span or source-text heuristics.

### Forward direction

`pc_analyze RECORD... impact TARGET [opaque|modular]` answers what depends on a
fact. `TARGET` is an artifact id or a vertex; an artifact expands to everything
it elaborates to. Two witness-relative relations are printed:

* `reaches`: may-depend — every vertex whose observed argument mentions the
  target somewhere in a productive tail, split into obligations and premises
  reached through certificates, and the functions those obligations belong to; 
* `load-bearing`: the obligations that lose their grounding in the observed
  argument when the target is blocked.

Neither claims the proof would fail without the fact. `impact` traverses the
same relations as the slice, so the two directions cannot drift.

## 7. Findings

The finding vocabulary is `PROOF_COVERAGE_FINDINGS.md` §2; the report serializes
it under schema `verus-proof-coverage-report/0.2`. Findings live on
`functions[]` and `files[]`. The top-level `query_observations` array is *not*
findings: it holds one row per (source fact, terminal) and carries observation
names ( `available-not-observed` , `vacuous-terminal` ), because summing a
query-scope observation across queries is meaningless.

Every finding row carries:

* `kind` — the §2 subtype ( `goal-unused-precondition` , 
`vacuous-postcondition` , `unobserved-context` , ...);
* `claim` — what sort of statement it makes. This is for rendering and
  severity, and is the field a consumer should key on instead of enumerating
  subtypes:

```text
absence   goal-unused-*, auxiliary-only-fact,
          checked-but-unused-proof-step, unobserved-context,
          goal-disconnected-code
vacuity   vacuous-*
trust     trusted-dependency
coupling  goal-without-body-support
```

* `evidence_basis` — *how the row was derived*, which is a different axis from
  `claim` and is what decides defensibility:

```text
slice-absence        the row says a fact is not in the slice
terminal-core        the row is read off the terminal's own core
slice-reachability   the row says a fact is in the slice
```

  The two axes must not be conflated. `goal-without-body-support` renders as
  `coupling` but is derived by absence ("no local implementation fact in the
  slice"), so an unlicensed export that drops the very assignment which would
  have satisfied it can invent one.

* `defensible` — false when the root slice rests on an unlicensed exported
  assumption, with `withheld_reason` naming why. Withholding is keyed on
  `evidence_basis == slice-absence`, never on `claim`. Rows read from a core or
  established by reachability cannot be invented by a licensing hole.

  Defensibility is decided against `rooted.completeness`, not the function-wide
  `completeness`: a finding is scoped to the selected roots, so a licensing hole
  in an unrelated auxiliary query of the same function must not withhold it.
* `root_policy` and `finding_relation` — which obligations the finding is
  relative to (below).

A vacuity is keyed on its **parent obligation**, not on a terminal, because
`extent` is a property of the obligation: `all` means every terminal of it was
discharged by contradiction, so nothing about it is proved; `some` means the
vacuous terminals are infeasible branches, which is what `assert(false)` and
`assert_by_contradiction!` produce by design.

Vacuity is direct terminal evidence, so unlike an absence claim it is not gated
on root selection — strict gating would delete every subtype except
`vacuous-postcondition` from any function that has a postcondition. Each row
carries `root_relation`:

```text
selected-root  any extent      a finding
non-root       extent = all    a finding: that obligation is not proved at all
non-root       extent = some   `rooted.infeasible_paths`, collapsed by default
```

An infeasible path is real information — the branch is dead — but it is not a
defect, so it is reported separately rather than in `findings`.

`trusted-dependency` is one **(consumer function, trusted subject)** relation.
Function scope reports the relation; file and project scope aggregate by subject
and carry `affected_functions` , `affected_function_count` and `root_policies` ,
so one subject reached by N proofs reads as one subject rather than N findings.
Other findings aggregated to file scope keep the consuming `function` : a
finding's span names where the subject is *written*, not whose proof failed to
use it.

At function scope the candidate population is every `available-not-observed`

observation made by a measured terminal of the function — including terminals of
queries the roots never see directly, such as an isolated loop body, which a
root reaches only through the loop certificate. A candidate remains a finding
only when its source artifact is absent from every selected root's direct and
transitive slice. Observation by a non-root terminal qualifies the finding
( `auxiliary-support` ) and never suppresses it; vacuity of a non-root terminal
creates no finding.

Source-artifact/terminal pairs have one of four aggregate states:

* `observed-all`: observed by every measured terminal where it was available; 
* `observed-some`: observed by some and uncovered by others; 
* `observed-none`: observed by none — the only state that produces a
  function-level uncovered-premise finding; 
* `incomplete`: at least one available pair has no usable focused evidence, and
  produces no aggregate finding.

The `files` array recomputes these states from the underlying pairs rather than
combining already-aggregated function classifications, so mixed evidence across
functions stays `observed-some` .

Each query and function carries a conservative `status` and a `completeness`

object over six independent dimensions: `evidence` ( `Measured` , 
`Overapproximated` , `NotApplicable` ), `grounding` ( `Grounded` , `Ungrounded` , 
`NotEvaluated` ), `attribution` , `placement` , `artifact_projection` , and
`licensing` . `Complete` means all required dimensions are complete for the
reported slice; `Partial` names which are missing and by how much.

`licensing` counts the graph roots in the slice that are really an assumption
some checked construct exported — holes in the licensing relation
( `PROOF_COVERAGE_FINDINGS.md` §5, `PROOF_COVERAGE_GAPS.md` §4.1). Such a root is
taken on trust, so every fact that supported only its discharge drops out of the
slice and would be reported unused. It is a dimension rather than a side
diagnostic because without it a slice resting on an unlicensed export reports
`Complete` and its absence findings look defensible.

### Text vocabulary

`pc_analyze RECORD study FUNCTION opaque` emits `proof-coverage-text 0.1` .

* `support-witness` / `contradiction-witness`: an atomic focused core whose
  terminal was, or was not, observed; 
* `certificate`: a VCG protocol edge (loop, local lemma, assert establishment, 
  contract licensing); 
* `demand-refined-call`: a call-local edge whose tail contains the callee proof
  or that call's decrease guard, plus the precondition checks it discharged.
`demand-refined` names the licensor being call-local; the check set is not
  refined per clause; 
* `reach=direct|transitive`: in the terminal witness, or reached through
  provenance; 
* `direct-support` / `direct-contradiction`: the function-level partition of
  directly observed evidence. Both count as observed coverage; only the former
  is a dependency of a discharged terminal; 
* `generated-support`: typed generated or derived facts (branch conditions, type
  invariants, assignment equalities, SSA reconciliations, fuel, decreases
  checks) observed in a root witness. These have typed origins and often spans, 
  but no stable source-artifact identity; 
* `ambient-support`: ambient axioms observed in a root witness, shown with the
  recorded owner and typed installation op ( `SpecDefinition` , `ReqEns` , 
`Broadcast` , `TraitImpl` ). Axiom labels remain opaque transport tokens; 
* `locality=local|imported`: whether traversal stays in the selected function; 
* `boundary`: an intentional stopping point;   `gap`: missing evidence or
  attribution; 
* `observation available-not-observed` (query scope): the fact was in one
  query's validated scope and absent from that one witness. Summing it across
  queries is meaningless; 
* `finding available-not-observed` (function scope): the root-scoped survivor.
`finding vacuous-terminal` is a finding at both scopes; 
* `occluded`: a verdict withheld because unidentified source evidence of the
  same family exists in this scope; 
* `auxiliary-support`: a qualifier on a function-scope
`available-not-observed` finding — the artifact was observed in a measured
  non-root terminal's witness in the same function. It does not suppress the
  finding and does not claim the fact is removable.

### Root-scoped function results

Each function report carries a `rooted` object with the same results the study
text derives, so consumers do not reconstruct them from raw cores: `roots` , 
`classification` (one row per source artifact with its strongest class and
`locality` ), `generated_support` , `ambient_support` , `witnesses` (each measured
root's atomic core, kept as one joint set — consumers must not flatten one into
pairwise edges), `steps` , `boundaries` , `findings` , and `vertices` (a descriptor
table resolving every ref used above).

The study text and the report's `rooted` section are two projections of one
builder and must not drift.

## 8. Self-measurement

`analysis_coverage` reports what the analysis does not cover, separately from
proof findings, by set difference over audited relations:

```text
Declared(a)   a source clause inventoried in the artifact table
Measured(a)   some occurrence carries an audited projection onto a

instrumentation_gaps  = Declared \ Measured        (local and imported)
unprojected_evidence  = source-like occurrences with no artifact
unresolved_residue    = occurrences whose rules all failed, by bucket
```

An imported clause is expected to be unmeasured: a callee contract enters a
caller as one aggregate. A verdict about an artifact whose family has
unprojected evidence in the same scope is reported `occluded` , because the
unidentified rows could be that clause at another protocol position. Every
coverage claim therefore carries its own denominator.

## 9. Deliberate boundary

v0.1 observes ordinary `CheckValid` SMT queries. Singular queries and constructs
without an observed `FuncCheckSst` are outside this version's source-provenance
claim. Within ordinary SMT queries, unsupported lowering populations stay
explicit as unresolved occurrences or ungrounded protocol boundaries.

## 10. Commands

From `source/` :

```text
VERUS_PROOF_COVERAGE_OUT=record.json \
  ./target-verus/release/verus FILE.rs -V proof-coverage

./target-verus/release/pc_audit record.json     # --families --recursion --rules
./target-verus/release/pc_analyze record.json targets
./target-verus/release/pc_analyze record.json unlicensed
./target-verus/release/pc_analyze record.json findings [opaque] [--all]
./target-verus/release/pc_analyze record.json study FUNCTION opaque
./target-verus/release/pc_analyze record.json report opaque
./target-verus/release/pc_analyze record.json project
./target-verus/release/pc_analyze record.json impact TARGET modular
./target-verus/release/pc_analyze crate-a.json crate-b.json project
```

`report opaque` stops at ordinary call boundaries and is the intraprocedural
view; `project` defaults to modular traversal and expects records from one
coherent project or evaluation population. `study` is the research text view.

`VERUS_PROOF_COVERAGE_MINIMIZE_CORES=1` makes shadow contexts set Z3's
`smt.core.minimize=true` ; canonical contexts are unchanged. It is not the
default because it pushed the mergesort probe beyond its 180-second budget.

Evidence collection reports exact progress after verification has buffered the
complete shadow-query population. Progress lines include completed and total
queries, percentage, elapsed time, throughput, and an ETA. Set
`VERUS_PROOF_COVERAGE_TRACE_SHADOW=1` for the verbose context and per-query
start/finish trace when diagnosing an individual slow query.
