# Rust SAML Validator findings investigation

Date: 2026-09-15

## Conclusion

The SAML findings are useful, but they should not yet be presented as one
undifferentiated warning list.

The strongest absence findings performed well. Twelve isolated,
behavior-preserving or deliberately behavior-changing mutations confirmed 15
finding rows while the package continued to report 710 verified and 0 errors.
A negative-control mutation to a directly verified accessor was correctly
rejected with 709 verified and 1 error.

The investigation also found two analyzer presentation/classification problems:

1. Three `goal-unused-assumption` rows are generated match-arm hypotheses, not
   authored `assume` statements.
2. At least 27 of 35 `goal-without-body-support` rows are direct accessors whose
   body expression participates in the VC but is not represented as a labeled
   premise. These should not be reported as weakly coupled.

The practical result is a valuable high-confidence review queue of redundant
proof steps, unused preconditions, unnecessary reveals, and specification
adequacy observations. Traceability and auxiliary rows remain useful as
on-demand information, not default warnings.

## Finding population

The whole-package opaque analysis reported 995 rows:

| Finding kind | Defensible | Assessment |
|---|---:|---|
| `auxiliary-only-fact` | 378 | Traceability; not a deletion recommendation |
| `trusted-dependency` | 140 | Trust inventory; aggregate by dependency |
| `goal-disconnected-code` | 102 | Potentially valuable specification-adequacy finding |
| `checked-but-unused-proof-step` | 79 | High-value cleanup candidate |
| `goal-unused-callee-contract` | 74 | Mostly caller/contract telemetry; low default actionability |
| `goal-unused-precondition` | 36 | High-value contract simplification candidate |
| `goal-without-body-support` | 35 | Mixed: one useful weak-contract case, at least 27 accessor artifacts |
| `vacuous-postcondition` | 4 | All partial-path vacuity; informational |
| `vacuous-assertion` | 3 | Intentional contradiction assertions |
| `unobserved-context` | 3 | High-value cleanup; all three confirmed |
| `goal-unused-assumption` | 3 | Misclassified generated control hypotheses |

Another 138 absence rows were withheld because evidence was incomplete or
source attribution was occluded. The withholding policy behaved as intended:
these rows should not enter the actionable queue.

## Mutation evidence

Every successful mutation below was applied alone in a temporary copy of the
package. The original package was not modified.

| Finding | Mutation | Result | Interpretation |
|---|---|---:|---|
| `checked-but-unused-proof-step` | Removed `(start as int) < (len as int)` from the first decimal loop invariant | 710/0 | Redundant invariant clause |
| `checked-but-unused-proof-step` | Removed `len == s@.len()` from the second decimal loop invariant | 710/0 | Redundant invariant clause |
| `vacuous-postcondition` | Removed the precondition-infeasible `pos >= end` branch from `lemma_rdn_after_plus_strict_implies_lenient` | 710/0 | Partial vacuity correctly identified a dead proof path |
| `goal-unused-precondition` | Removed `pos <= s@.len()` from `parse_octet` | 710/0 | Genuine overly strong executable-function precondition |
| `checked-but-unused-proof-step` | Removed `assert(s_start < s_eq_pos)` from `parse_attribute_type_and_value` | 710/0 | Redundant witness assertion |
| `checked-but-unused-proof-step` | Removed duplicate invariant `pos >= start + 1` from `parse_hexstring` | 710/0 | Redundant invariant clause |
| `unobserved-context` | Removed `reveal_with_fuel(spec_dn_after_rdn_with_eq, 2)` | 710/0 | Unnecessary reveal |
| `unobserved-context` | Removed `reveal_with_fuel(spec_rdn_continuation_with_eq, 2)` | 710/0 | Unnecessary reveal |
| `unobserved-context` | Removed `reveal_with_fuel(spec_find_first_at, 2)` | 710/0 | Unnecessary reveal |
| Four `goal-unused-precondition` rows | Simultaneously removed the length, `"2."`, and digit-shape premises from `proof_version_higher_minor_flag_off`; retained only `spec_parse_digits_value(...) > 0` | 710/0 | The semantic premise already implies all four structural premises |
| `goal-disconnected-code` | Replaced the `first == '0'` special-case condition in `parse_number` with `false` | 710/0 | A behavior-changing leading-zero regression is admitted by the local contract |
| `goal-without-body-support` | Changed public `is_valid_rfc4514_dn` to return `false` unconditionally | 710/0 | Its one-way soundness contract permits a reject-all implementation |

The first ten experiments validate 13 rows from the 128-row high-confidence
subset: four checked proof steps, five preconditions, all three unobserved
reveals, and one vacuity row. The final two validate coupling findings by
showing that materially changed behavior remains verified.

### Negative control

`ValidatedSamlDateTime::month` is reported as
`goal-without-body-support`. Changing its body from `self.inner.month` to the
same-typed `self.inner.day` was rejected:

```text
error: postcondition not satisfied
verification results:: 709 verified, 1 errors
```

The accessor's goal does depend on its body. The dependency is encoded directly
in the VC rather than as a labeled premise visible to the current slice. This
finding is therefore an instrumentation blind spot, not weak proof coupling.

## Detailed assessment

### Redundant proof steps

The 79 defensible rows comprise 55 assertions and 24 loop-invariant clauses.
Four diverse samples have now survived deletion. This is the best default
cleanup category: it names exact source spans, has a clear developer action,
and has shown good precision under mutation.

The 32 withheld proof-step rows should remain visible only in a diagnostic view
until their root evidence is complete.

### Unused preconditions

There are 36 defensible rows: 28 in proof/spec functions and 8 in executable
functions. The sampled findings exposed both:

- a genuinely unnecessary executable precondition on `parse_octet`; and
- four documentary/structural proof premises implied by one stronger semantic
  premise in the version lemma.

These are useful findings, but proof-function rows should be described as
contract simplification or documentation cleanup rather than runtime API
weakening.

### Unobserved context

All three rows were independently confirmed by deletion. This category is both
small and precise enough to be enabled by default.

### Goal-disconnected code

The 102 rows comprise 55 assignments, 31 branch conditions, and 16 return
bindings. They are not automatic deletion candidates: executable behavior may
matter even when the declared proof goals do not observe it.

The `parse_number` experiment demonstrates the category's real value. Disabling
the leading-zero path changes parser behavior while all verification still
passes. The appropriate action is to review or strengthen the contract, not to
delete the branch.

The report should therefore rename or explain this category as “behavior not
observed by declared goals” and show an example input or affected path where
possible.

### Goals without body support

This category is mixed:

- The RFC4514 public wrapper is a true positive: its implication-only contract
  permits an always-false implementation.
- At least 27 of 35 rows are direct accessor-like functions. The wrong-field
  negative control proves that at least this shape is currently a false
  coupling warning.
- The remaining eight rows are wrappers, dispatch methods, or clone-like
  functions and require individual review.

The finding should be suppressed for direct expression bodies until the graph
records body-to-goal support that is encoded in the VC conclusion rather than
in labeled premises.

### Vacuity

No postcondition is vacuous on all of its terminals:

- all four `vacuous-postcondition` rows have extent `some`;
- they correspond to infeasible early-return or recheck paths;
- one RFC4514 path was confirmed removable.

The three all-terminal `vacuous-assertion` rows are explicit `assert(false)`
statements in branches the source already treats as unreachable. They are
accurate dead-path observations, not proof failures.

Partial postcondition vacuity and explicit contradiction assertions should be
informational by default.

### Generated assumptions

The three `goal-unused-assumption` rows point to:

- `Ok(()) => {}` in `validate_extension_statements`; and
- the `Ok` and `Err` arms of a `match` in `ValidatedIssuer::try_new`.

None is authored `assume` or `admit` syntax. Match simplification introduces
`AssertAssume` control hypotheses with source-looking arm spans, and
`source_body_inventory` currently records every such node as an assumption.

The analyzer already has `assumption_source`, which filters generated protocol
hypotheses from trust findings by checking for explicit `assume`/`admit`
syntax. The short-term fix is to apply the same distinction to unused
assumption findings. The durable fix is a typed producer origin distinguishing
authored assumptions from generated control hypotheses.

### Unused callee contracts

Of 74 defensible rows, 56 name library contracts and 18 name package contracts.
The largest subjects are `String::from_str`, vector indexing, and empty-vector
construction.

These rows answer a useful traceability question—what part of a callee contract
did this caller's goals need—but they do not justify changing a shared callee
contract. They should be aggregated by callee and exposed as a contract-usage
view rather than mixed into the primary cleanup list.

### Auxiliary facts and trusted dependencies

The 378 auxiliary rows show facts used for invariant maintenance, call
preconditions, termination, or other non-root obligations. Their presence is
evidence that the analyzer distinguishes “not needed by the selected goals”
from “dead.” They should remain informational.

The 140 trusted-dependency rows are dominated by external `get_char`,
`unicode_len`, `from_str`, and vector-index contracts. They are useful for a
trust-base or impact view, but should stay collapsed in the normal report.

## Recommended default SAML review queue

Show these first:

1. `checked-but-unused-proof-step`
2. `goal-unused-precondition`
3. `unobserved-context`
4. `goal-disconnected-code`, labeled as specification adequacy
5. whole-goal vacuity, if any appears in future runs

Keep these secondary or collapsed:

1. partial-path vacuity and explicit contradiction assertions
2. `auxiliary-only-fact`
3. `trusted-dependency`
4. `goal-unused-callee-contract`

Withhold or fix before display:

1. generated match hypotheses reported as unused assumptions
2. direct accessors reported as goals without body support
3. any absence row with incomplete evidence or occluded attribution

## Immediate package actions supported by evidence

Without changing semantics, the package can safely be cleaned up by removing
the four confirmed redundant proof steps, the three confirmed reveals, the
dead RFC4514 proof branch, and the five confirmed unnecessary precondition
clauses.

The two behavior-changing coupling experiments should not be applied as
cleanup. They identify contracts worth reviewing:

- specify the intended leading-zero behavior of `parse_number`; and
- decide whether `is_valid_rfc4514_dn` needs a completeness direction in
  addition to soundness.

