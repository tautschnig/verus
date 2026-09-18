# Violations of the documented proof-chain policy

The project defines its intended proof chain as:

```text
exec code → type invariant → is_valid(ctx) → proof
```

Its active design also states that changing validation logic in executable code
should cause a Verus failure. The current package reports **710 verified,
0 errors**, but the following cases violate that documented policy or its
coverage claims.

## Five issues

### 1. The public validation result has no contract

`src/saml/validator/mod.rs:60` defines `validate_assertion` without an
`ensures` clause. `validate_assertion_with_depth` also has no postcondition
relating its result to assertion validity.

Replacing the public function with unconditional `ValidationResult::Valid`
still produced **710 verified, 0 errors**.

This contradicts:

- `.kiro/specs/strengthen-proof-chain/design.md`: modifying any validation
  logic should cause verification failure.
- `PROOF_REVIEW_GUIDE.md`: every arrow in the proof chain must be
  machine-checked.
- `README.md` and `verification-audit.md`: every core validator is claimed to
  have an `ensures` linking it to a specification.

**Consequence:** Verus does not protect what callers may conclude from the
public `Valid` result.

### 2. Validation-affecting code remains outside the verified build

The `close-adversarial-proof-gaps` requirements say that every cfg-gated block
which mutates validation results must be moved into Verus-visible code. Its
task list marks this work completed.

Current source still contains validation-affecting
`#[cfg(not(verus_keep_ghost))]` blocks, including:

- `src/saml/types/subject.rs:549`
- `src/saml/types/statements.rs:564`
- `src/saml/types/statements.rs:1064`

These perform checks such as IP-address validation, URI-fragment rejection,
URI normalization, and action-negation exclusion, but are compiled away during
verification.

**Consequence:** runtime behavior can lose security checks without invalidating
the Verus proof.

### 3. The “100% linkage” audit excludes missing links by construction

`reports/review/dual-coverage-spec-code-matrix.md` says its methodology walks
exec functions that already have a corresponding specification or an
`ensures` clause. It then reports **100% linkage across 56 functions**.

The primary public function `validate_assertion` is consequently absent from
the matrix.

**Consequence:** the metric cannot discover precisely the class of unlinked
function that it claims is absent.

### 4. Type invariants are incorrectly described as biconditional linkage

The spec-code matrix grades several constructors `S1-TI` and describes a type
invariant as “biconditional-equivalent” and stronger than a biconditional
constructor contract.

A type invariant establishes:

```text
constructed value ⇒ specification holds
```

It does not establish:

```text
specification holds ⇒ constructor accepts the input
```

Thus it proves soundness of accepted values, not completeness. A reject-all
implementation can preserve the invariant.

**Consequence:** the S1-TI grade overstates the guarantee and can hide
over-restrictive or disabled validators.

### 5. A vacuous theorem is graded as a full proof

`verus/proof/saml/validator/conditions.rs:455` defines
`lemma_clock_skew_widens_window`, but its entire postcondition is `true`.

Nevertheless,
`reports/review/dual-coverage-ac-proof-matrix.md` grades this lemma P1—full
machine-checked proof—for the clock-skew requirement.

This conflicts with `PROOF_REVIEW_GUIDE.md`, where P1 means that the proof
function actually establishes the acceptance criterion.

**Consequence:** successful verification of this lemma provides no evidence
that clock skew widens the acceptance window.

## Bottom line

These are not solver failures. The solver is discharging the obligations it
receives. The gap is between the project's documented assurance policy and the
contracts, compilation paths, and coverage accounting used to enforce that
policy.

The highest-priority repair is to give the public validation entry point a
semantic postcondition. Without that final link, strong internal proofs do not
protect the meaning of the API result.

