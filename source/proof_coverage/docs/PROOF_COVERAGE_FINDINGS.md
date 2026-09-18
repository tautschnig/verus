# Proof-Coverage Findings and Data Collection

This document proposes a small finding vocabulary grounded in what the
proof-coverage analyzer can currently defend. Earlier work motivates vacuous
goals, unused assumptions or specifications, and unconstrained implementation
as the main families. The aim here is to turn those broad categories into
precise, testable Verus findings while separating them from future
counterfactual and synthesis analyses.

## 1. Principles

Every finding should identify:

- an actionable source subject;
- the measured evidence supporting the finding;
- the selected roots and analysis scope;
- the completeness of the relevant measurement and attribution;
- any boundary, qualification, or occlusion that limits the claim.

Query-local observations are not automatically findings. A source fact absent
from one terminal's witness becomes a function-level finding only if it remains
outside every selected root's grounded, transitive slice.

Findings should remain witness-relative and root-relative unless an explicit
counterfactual solver experiment establishes a stronger result. In particular,
core absence does not by itself establish semantic removability.

Finding promotion also follows two dominance rules:

- if every selected root is vacuous, slice-absence observations are secondary
  to the contradiction and are not promoted as unused-fact or weak-coupling
  findings;
- a proof step is not simultaneously reported as vacuous and
  `checked-but-unused-proof-step`.

The no-declared-goals `all-measured` fallback treats each measured assertion or
lemma check as a goal in its own right. If that proof step's exported fact
reaches no later selected root, the analyzer retains a secondary standalone
obligation observation rather than calling the proof step unused.

## 2. Recommended findings

| Finding | Concrete evidence | Developer interpretation |
|---|---|---|
| `vacuous-goal` | A measured focused core omits its terminal | The goal was discharged by contradictory context |
| `goal-unused-fact` | A source fact is available but absent from every selected root's grounded slice | Candidate unnecessary precondition, invariant, assertion, lemma, or assumption |
| `auxiliary-only-fact` | Outside every declared-goal slice, but observed by a non-root safety or proof obligation | Useful only for overflow, bounds, termination, or another auxiliary check |
| `checked-but-unused-proof-step` | An assertion, invariant, or lemma is genuinely established, but its exported fact reaches no selected goal | Proof scaffolding that may be removable |
| `trusted-dependency` | A goal slice reaches `assume`, `admit`, or an `external_body` contract | A verified result rests on trusted material |
| `goal-without-body-support` | An executable function's declared-goal slice contains no local implementation facts | The contract may be weakly coupled to the implementation |
| `goal-disconnected-code` | A measured assignment, branch, call, or return artifact reaches no declared goal | Candidate unconstrained or unreachable implementation |
| `unobserved-context` | A named broadcast lemma or axiom is installed but absent from all eligible goal witnesses | Candidate unnecessary proof context |
| `high-impact-fact` | Forward analysis reaches many roots or functions, or blocking the fact ungrounds the observed argument | Maintenance hotspot or central proof fact |

These findings have different purposes:

- `vacuous-goal` is a correctness and confidence warning.
- Unused and weak-coupling findings are review suggestions.
- `high-impact-fact` is a traceability result, not a defect.
- Incomplete instrumentation is an analyzer diagnostic, never a program
  finding.

### 2.1 Vacuous-goal subtypes

The finding should retain the obligation kind:

- `vacuous-postcondition`
- `vacuous-assertion`
- `vacuous-call-precondition`
- `vacuous-loop-establishment`
- `vacuous-loop-maintenance`
- `vacuous-termination-check`
- `vacuous-safety-check`

The evidence should be shown as one joint contradiction witness. Its members
must not be presented as individually sufficient causes.

Useful qualifiers include:

- contradiction contains a user assumption;
- contradiction contains an `external_body` contract;
- contradiction contains an imported or ambient fact;
- contradiction is local to an infeasible branch;
- the same contradiction witness discharges several goals.

### 2.2 Goal-unused-fact subtypes

The source artifact kind should refine the finding:

- `goal-unused-precondition`
- `goal-unused-loop-invariant`
- `goal-unused-assertion`
- `goal-unused-local-lemma`
- `goal-unused-assumption`
- `goal-unused-callee-contract`
- `goal-unused-program-fact`

The existing root-scoped verdicts provide important qualifications:

- `unlinked`: outside every selected root slice and not observed by another
  measured terminal;
- `auxiliary-only`: outside every selected root slice but observed by a
  measured non-root terminal;
- `occluded`: the verdict is withheld because incomplete source attribution
  could change it.

An artifact observed by some eligible terminals and omitted by others should
retain `observed-some` as coverage data rather than becoming an aggregate
unused finding.

### 2.3 Checked-but-unused proof steps

This is a protocol-aware specialization of an unused proof fact:

- an assertion's check is discharged, but its established assumption reaches
  no selected goal;
- a local lemma's goal is discharged, but its exported conclusion reaches no
  selected goal;
- a loop invariant is established and maintained, but its exit export and
  downstream consequences reach no selected goal.

This distinguishes genuinely verified but apparently unnecessary proof
scaffolding from vacuous proof code.

### 2.4 Trusted dependencies

A selected goal should report when its grounded slice reaches:

- a user `assume`;
- an admitted proof;
- an `external_body` contract;
- another explicitly trusted source construct.

Imported contracts are not inherently trusted: when the defining record is
available, modular analysis should cross into its proof. Opaque or missing
project boundaries should be reported as boundaries rather than silently
treated as verified or trusted.

A trusted dependency becomes especially important when it participates in a
contradiction witness. A useful high-severity presentation is:

> This postcondition was discharged vacuously by a contradiction involving
> trusted assumption `A`.

Forward impact can report how many roots and functions transitively depend on
each trusted fact.

Generated protocol hypotheses that lower through the same internal
`UserAssumption` role as source `assume` are not trusted dependencies. Until the
record gives these constructs separate typed roles, the analyzer uses the exact
source span to distinguish explicit `assume`/`admit` syntax from state-machine
operations such as `require`, `remove`, and `have`; unavailable source fails
conservatively and retains the trust row.

### 2.5 Weak proof coupling

Two related findings are useful:

1. `goal-without-body-support`: a declared goal of an executable function has
   no local implementation artifact in its grounded slice;
2. `goal-disconnected-code`: a measured implementation artifact reaches no
   declared goal.

These are structural proof-coupling findings, not claims that the
specification is semantically weak.

They should normally be restricted to executable functions with visible
bodies. Proof functions, specification functions, trusted declarations, and
functions with no declared goals require different interpretations.

The eligible implementation population must also be explicit. A statement
that never received a source artifact is an instrumentation gap, not
goal-disconnected code.

### 2.6 Unobserved context

For ambient axioms, broadcast lemmas, specification definitions, and imported
proof context, the defensible name is `unobserved-context`, not
`unnecessary-context`.

Core absence establishes only that the named context item was not observed in
the measured argument. It does not exclude:

- an alternative proof core;
- trigger or solver-search effects;
- use by an unmeasured query;
- use under another project configuration.

A useful report would say:

> Broadcast lemma `L` was installed in 83 solver contexts and observed by 0
> of 412 eligible declared-goal terminals.

This provides concrete evidence without claiming removability.

### 2.7 Forward impact and proof centrality

Forward analysis should expose two relations:

- `reaches`: roots, obligations, premises, and functions whose observed
  arguments transitively mention the selected fact;
- `observed-load-bearing`: roots that lose grounding when the fact is blocked
  in the recorded verification argument.

Useful derived insights include:

- facts with high root or function fan-out;
- trusted facts on which many verified contracts depend;
- central lemmas or invariants;
- source facts that connect otherwise separate proof regions.

These are maintenance and traceability results. `Observed-load-bearing` does
not mean that the fact belongs to every solver proof or that deleting it from
the program must make canonical verification fail.

## 3. Preconditions and postconditions

The current result should not be called `overly-strong-precondition`.

The defensible findings are:

- `goal-unused-precondition`: the clause was not used in proving the selected
  declared goals;
- `auxiliary-only-precondition`: the clause was used only for safety,
  termination, or another auxiliary obligation;
- `project-unconsumed-precondition`: a future interprocedural result, once
  clause-level caller measurements exist.

“Overly strong” implies that a weakening is known to preserve the required
proofs. Establishing that requires mutation, logical weakening, or sufficiently
precise interprocedural evidence.

The same distinction applies to postconditions. The current aggregate contract
encoding can support findings such as:

- a callee's ensures aggregate was not consumed at a particular call;
- an ensures aggregate was unconsumed by all observed callers in the project.

It cannot reliably establish that one imported ensures clause is caller-unused
until caller-side postconditions are measured at clause granularity.

## 4. May and must proof elements

“Belongs to any proof core” is not useful for arbitrary, non-minimal cores,
because the complete unsatisfiable constraint set is itself a core. The useful
domain is minimal unsatisfiable cores:

- `may`: belongs to at least one minimal core;
- `must`: belongs to every minimal core;
- `alternative`: belongs to some but not all minimal cores;
- `irrelevant`: belongs to no minimal core.

A minimized observed core witnesses `may` membership for its members, but one
core cannot establish `must` or `irrelevant`.

Identifying a must element does not require enumerating every core. Disable one
candidate in the focused query:

- if the remaining query becomes satisfiable, every unsatisfiable core needed
  the candidate;
- if the remaining query remains unsatisfiable, an alternative proof exists.

This still requires one additional solver experiment per candidate and can be
expensive at scale, but it is substantially cheaper than enumerating all
minimal cores.

For the current analyzer, the preferred vocabulary is:

- `observed-support`
- `observed-load-bearing`

The term `must` should be reserved for the additional counterfactual solver
check.

## 5. Analysis diagnostics

Proof findings must remain separate from limitations of the measurement and
analysis. The report should retain explicit diagnostics for:

- unmeasured focused queries;
- shadow queries that fail to reproduce canonical validity;
- non-SMT proof backends;
- unresolved occurrence attribution;
- source evidence without an artifact;
- declared artifacts without measured occurrences;
- exported assumptions lacking a licensing relation;
- opaque call and trait-contract boundaries;
- imported contract aggregation;
- occluded findings.

Every finding population should report its eligible, incomplete, and occluded
denominators.

## 6. Data collected per finding

Each finding row should include:

```text
finding_kind
subject artifact, kind, span, and owner
scope: query | function | file | project
selected roots
call policy: opaque | modular
reach: direct | transitive | auxiliary-only
locality: local | imported
witness or contradiction-witness id
affected roots and functions
observed-load-bearing count
measurement and completeness status
occlusion and boundary details
counterfactual_checked: yes | no
```

Each aggregate should also report:

```text
eligible subjects
measured subjects
incomplete subjects
occluded subjects
reported findings
```

Without these denominators, rates from different projects or construct
families are not comparable.

## 7. Initial data study

The first study should collect six headline categories:

1. vacuous declared goals;
2. goal-unused preconditions;
3. goal-unused invariants, assertions, and lemmas;
4. auxiliary-only proof facts;
5. trusted dependencies;
6. goal-disconnected implementation facts.

For each sampled finding, manually classify it as:

- genuine defect;
- intentional design;
- maintenance opportunity;
- solver artifact;
- analyzer gap;
- unclear.

Where practical, perform a confirmation mutation:

- weaken or remove an unused clause;
- remove an unobserved broadcast lemma;
- replace a vacuous goal with `false`;
- block an observed-load-bearing fact.

The mutation result should be stored separately from the original finding. A
successful mutation strengthens the diagnosis, but a failed mutation may
reflect solver sensitivity, trigger behavior, or an analysis gap rather than
invalidating the original witness-relative observation.

## 8. Deferred analyses

The following are promising extensions, but should not be required for the
initial finding study:

- all-core or targeted may/must classification;
- automated precondition weakening;
- postcondition strengthening;
- backchaining from a successor block's required precondition;
- contract synthesis from implementation dependencies;
- semantic redundancy across alternative solver proofs;
- subexpression-level weakening of contract clauses.

These analyses require additional solver experiments or synthesis. The initial
finding vocabulary above is already concrete, measurable, and suitable for
evaluating developer usefulness.

## 9. Prior work

- Aaron Tomb and Anjali Joshi. “Static Coverage in Deductive Software
  Verification.” FMCAD 2025.
  <https://www.amazon.science/publications/static-coverage-in-deductive-software-verification>
- Elaheh Ghassabani, Andrew Gacek, Michael W. Whalen, Mats P. E. Heimdahl,
  and Lucas Wagner. “Proof-Based Coverage Metrics for Formal Verification.”
  ASE 2017. <https://loonwerks.com/publications/pdf/ghassabani2017ase.pdf>
- Elaheh Ghassabani, Andrew Gacek, and Michael W. Whalen. “Efficient
  Generation of Inductive Validity Cores for Safety Properties.” FSE 2016.
  <https://arxiv.org/abs/1603.04276>
