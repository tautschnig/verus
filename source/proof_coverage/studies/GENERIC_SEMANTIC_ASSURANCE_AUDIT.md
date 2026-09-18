# Generic semantic assurance-chain audit

## Goal

Proof coverage should identify where assurance can disappear between executable
behavior and the property ultimately presented to a caller:

```text
inputs/state → executable behavior → contract → specification → proof goal
                                      ↓
                              trust boundaries
```

This should be project-independent. A project supplies its top-level roots;
the analyzer supplies evidence about the links. Public executable functions
are useful automatic root candidates, with annotations or command-line
selection available when the meaningful boundary is different.

The report should describe review evidence rather than infer application
semantics. For example:

> Field `x` is not observed by any selected goal.

This is defensible. Claiming that field `x` is unimportant or that the program
is incorrect requires application knowledge or a counterfactual experiment.

## Questions for every root

### 1. What is claimed?

- Does the root have a semantic postcondition?
- Is the postcondition tautological or vacuous?
- Are all meaningful result variants characterized?
- Is the contract soundness-only, completeness-only, or biconditional?
- Does the contract constrain the public result, rather than only internal
  metadata?

### 2. What behavior does the claim observe?

- Which parameters and state fields reach the root?
- Which parameters or fields are absent from every root slice?
- Which branches, assignments, calls, and return bindings reach no root?
- Are some result variants unconstrained?
- Are child validators called without their guarantees reaching the parent
  result?

### 3. Does composition preserve the guarantee?

- Does a parent specification include the validity of its children?
- Do spec views or projections omit fields?
- Are fields replaced by `arbitrary`, empty, default, constant, or stub values?
- Are callee contracts checked but unconsumed by the top-level result?
- Does the verified object correspond to the object used at runtime?

### 4. What is outside verification?

- Runtime-only configuration blocks.
- `external_body`, `assume`, `admit`, opaque definitions, or missing crates.
- Different control paths or values in verified and ordinary builds.
- Imported or trait contracts whose implementations are unavailable.

### 5. How meaningful is the proof?

- Whole-goal or partial-path vacuity.
- Contradiction witnesses.
- Tautological goals such as `ensures true`.
- Goals independent of their parameters or preconditions.
- Unused preconditions, assertions, invariants, lemmas, and reveals.
- Proof steps that are established but disconnected from the selected roots.

## Required architecture

The analysis needs two independently collected populations:

```text
Source inventory
  public functions, parameters, fields, branches, calls, cfg paths, contracts
                          ↕
Proof-dependency graph
  roots, solver evidence, specifications, implementation facts, trust
```

The differences and missing joins between these populations produce the most
important findings. This prevents selection bias: source omitted from
verification still exists in the source inventory.

The source inventory should be collected early enough to retain:

- functions with no verification query;
- contract direction and expression shape;
- fields and parameters referenced by specifications;
- code removed by verification-specific configuration;
- public visibility and API boundaries.

The proof graph should retain:

- multiple selected roots;
- source-level facts and proof obligations;
- backwards support and forward impact;
- call and composition boundaries;
- trusted dependencies;
- evidence and attribution completeness.

## Recommended default priority

1. Root without a semantic contract.
2. Whole-goal vacuity.
3. Runtime behavior outside verification.
4. Input, field, or result variant unobserved by a root.
5. Parent/child composition gap.
6. Specification placeholder or tautology.
7. Executable behavior disconnected from declared goals.
8. Trusted dependency.
9. Unused proof or specification fact.
10. High-impact proof or trust dependency.

The first seven primarily ask whether the verified property adequately observes
the implementation. The final three support maintenance, cleanup, and
traceability.

## Generic finding candidates

- `root-without-semantic-contract`
- `vacuous-root`
- `result-variant-unconstrained`
- `input-unobserved-by-root`
- `state-field-unobserved-by-root`
- `body-region-unobserved-by-root`
- `callee-guarantee-unconsumed`
- `parent-child-composition-gap`
- `spec-projection-drops-field`
- `spec-placeholder-value`
- `runtime-only-validation`
- `trusted-root-dependency`
- `goal-unused-fact`
- `checked-but-unused-proof-step`
- `high-impact-fact`

Every finding should name its selected roots, source subject, evidence,
analysis completeness, and any boundary that weakens the claim.

## Confirmation

The static analysis produces a ranked review queue. Targeted mutation can
confirm the highest-value cases:

- replace a public result with a constant variant;
- delete a supposedly unused clause or proof step;
- disable a disconnected branch;
- replace a predicate implementation with `true` or `false`;
- remove a child validation call;
- alter a projected field.

A surviving mutation shows that the current proof does not observe that
behavior. It does not by itself prove that the original behavior was required.

## Boundary of automation

The analyzer can determine whether a behavior, field, contract, or proof fact
participates in the measured assurance chain. It cannot determine from solver
evidence alone whether the resulting specification expresses the intended
domain requirement.

Project-specific requirement adequacy remains a human judgment, optionally
supported by a small machine-readable policy or requirement manifest. The
generic analysis should remain useful without one.

