# DaffodilAuthzRust semantic proof-coverage review

Date: 2026-09-15

## Bottom line

DaffodilAuthzRust has a meaningful verified core. In particular, its internal
authorization-context builder has a semantic result contract, and three
important top-level properties are grounded and complete:

- a valid operation produces at least one authorization entry;
- each enabled action produces an authorization entry;
- resource-owner information is valid.

The most important gap appears immediately after that core:

```text
runtime inputs and validation
        ↓
verified Vec<AuthorizationInfo>
        ↓  unverified conversion; cross-account mismatch
public Vec<ARC Authorization>
```

The public conversion passes the caller account to ARC even when the verified
resource context contains a different resource account. ARC rejects that
mismatch, and the conversion unwraps the error. Thus a supported cross-account
resource can panic after the verified builder has produced the correct
`AuthorizationInfo`.

The analyzer was useful here, but the complete diagnosis required joining its
proof graph with an independent inspection of runtime-only source. The public
entry point and conversion do not occur in the proof record.

## Subject and run

The subject was the current working tree at:

```text
/local/home/wmahasai/workplace/Verus/src/DaffodilAuthzRust
commit 4515eacadd50678882a7636a68de53581414c6fe
```

The working tree already contained local changes. It was inspected without
modification. Verification used a disposable compatibility copy because the
package's captured dependency environment did not directly match the analyzer
checkout.

Verification and coverage results:

| Measurement | Result |
|---|---:|
| Verification | 1,003 verified, 0 errors |
| Queries | 6,761 |
| Queries with measured evidence | 6,642 |
| Premise occurrences | 30,655; 0 unresolved |
| Source obligations | 5,514; 0 unresolved |
| Declared local clauses | 4,428 |
| Measured local clauses | 4,008 |
| Structural audit | All invariants hold |
| Producer time | About 29 minutes |
| Consumer time | About 26 seconds |
| Findings | 3,052 total; 1,454 defensible; 1,598 withheld |

The producer is the scalability cost. Rendering and analyzing the completed
record is comparatively fast.

## Top 10 review items

| # | Finding or gap | Assurance break | Evidence |
|---:|---|---|---|
| 1 | Cross-account public conversion can panic. | **Verified object → public object** | `src/lib.rs:103-114` passes the caller account to `auth_info_to_authorization`. `src/creation.rs:33-39` supplies it as the resource account to `Authorization::try_new` and unwraps. The internal cross-account tests expect ARN/resource account `456` for caller `123` (`src/tests/test_cross_account.rs:50-71`). ARC explicitly rejects a supplied account that differs from the ARN account. |
| 2 | The production API result is outside the verified claim. | **Verification boundary** | `make_authorization_infos` and the `creation` module are compiled only under `cfg(not(verus_keep_ghost))` (`src/lib.rs:10-11,69-80`). Neither `make_authorization_infos` nor `auth_info_to_authorization` appears in the proof record. Verification constrains the internal `Vec<AuthorizationInfo>`, not the returned `Vec<Authorization>`. |
| 3 | `ValidatedAuthSpec` does not preserve its validation invariant. | **Runtime input → verified precondition** | The wrapper says callers must not bypass validation, but `auth_spec` is a public mutable field (`src/impl_verified/rust_context_builder.rs:12-20`). An external caller holding the wrapper can replace it after validation. A separate two-crate Rust check confirmed that `#[non_exhaustive]` does not prohibit public-field mutation. The verified root nevertheless requires `auth_spec.is_valid()` (`:396-424`). |
| 4 | The override safety decision is unverified and has no semantic contract. | **Public control flow → verified core** | `DaffodilContextBuilder::build` calls `safe_to_proceed` and returns a denial only when it says false (`src/impl_verified/rust_context_builder.rs:241-255`). The trait method has no Verus contract (`src/impl_verified/override_safety.rs:1-7`), and this wrapper path is absent from the proof record. |
| 5 | The theorem claiming cross-account PassRole rejection is wholly vacuous. | **Proof goal** | `theorem_cross_account_pass_role_fails` advertises RFC requirements `REQ-PASSROLE-REJ` and `REQ-PASSROLE-REJ-VRC` (`src/verus/theorems/pass_role_properties.rs:34-49`). Coverage reports its sole postcondition as **all terminals vacuous**, with status `Ungrounded`. Separately, the internal builder has a trusted dependency on `check_pass_role_is_in_data_plane`'s contract. |
| 6 | `populate_on_type_level` is omitted from both specification and implementation. | **Requirement → specification** | The specification says ByType should check `populate_on_type_level`, but currently returns `true` for every non-create operation (`src/verus/specs/context_builder_spec.rs:279-297`). The implementation contains the matching TODO and always adds the key (`src/impl_verified/context_builder.rs:3913-3915`). Verification therefore proves conformance to an explicitly incomplete model. |
| 7 | ARN parsing correctness rests on admitted split axioms. | **Runtime/string model → specification** | Four split/splitn lemmas in `src/verus/specs/dafny_specs.rs` are admitted and used throughout `arn_spec.rs` and `impl_verified/arn.rs`. Coverage reports their postconditions as wholly vacuous/trusted. These axioms support security-relevant resource identity and account parsing. |
| 8 | The main specification translation is not fully validated. | **Intended policy → formal model** | `src/verus/specs/specs.rs:1-7` states that the specification is an LLM-based translation that was spot-checked but not checked in detail. The proof can establish implementation/model agreement without establishing that the model faithfully expresses all Daffodil requirements. |
| 9 | The proof foundation contains a broad custom trust surface. | **Trusted foundation** | The source contains 25 `admit()`/`assume()` sites. The analyzer reports 241 trusted-dependency relations over 43 distinct subjects, including custom string, hash-key, split, closure, and resource-key models. These should be grouped and ranked by forward impact rather than reviewed as isolated rows. |
| 10 | Root evidence is incomplete, and the remaining absence findings are mainly a maintenance queue. | **Coverage evidence** | Only 4,008 of 4,428 declared local clauses were measured. The main internal builder is `Partial`; its absence findings are appropriately withheld. Overall, 1,598 of 3,052 findings are withheld. Defensible cleanup candidates still include 98 unused preconditions, 116 checked-but-unused proof steps, 91 unobserved-context rows, and 192 goal-disconnected-code rows. |

## Direct confirmation of the cross-account failure

The failure follows from four independently visible facts:

1. The package supports cross-account resource ARNs and tests that the internal
   `AuthorizationInfo` uses the ARN account rather than the caller account.
2. The public wrapper discards that `aws_account` when constructing the ARC
   object and supplies `authn_success.subject().account()` instead.
3. ARC documents and implements a requirement that a separately supplied
   resource account match the account embedded in the ARN.
4. ARC's own unit test confirms that mismatched accounts return an error, while
   Daffodil calls `.unwrap()` on that result.

For an ARN containing account `456` and caller account `123`, the verified core
can construct the intended internal object, after which the ordinary runtime
conversion deterministically reaches the unwrap error.

A likely correction is to pass the resource account already present in the
verified `AuthorizationInfo`, propagate constructor failure instead of
unwrapping it, and add an end-to-end test through `make_authorization_infos`.

## What the analyzer showed well

The report distinguishes strong and weak parts of the proof:

- `theorem_at_least_one_entry_in_authorization_info` is `Complete` and has no
  findings.
- `theorem_auth_info_per_enabled_action` is `Complete`; its only finding is an
  unused reveal.
- `theorem_resource_owner_always_valid` is `Complete` and has no findings.
- `theorem_cross_account_pass_role_fails` is `Ungrounded` and wholly vacuous.
- `build_authorization_context` has a strong deep-view postcondition, but its
  slice is `Partial` and it reaches a trusted PassRole contract.

This is substantially more useful than treating “1,003 verified” as one
undifferentiated assurance result.

## What required source-level analysis

The highest-priority items were not discoverable from the proof graph alone:

- the public API is removed by verification-specific configuration;
- the final internal-to-ARC conversion is unverified;
- the validated wrapper's public field permits invariant destruction;
- the override safety gate is outside the verified root;
- the formal specification itself documents an intended field that it omits.

This supports the proposed generic architecture:

```text
independent source/API inventory
             ↕
proof dependency and solver-evidence graph
```

Without the source inventory, the analyzer cannot report that important public
functions have no proof query at all.

## How to interpret the raw findings

The 3,052 rows are not 3,052 defects.

- Do not act on the 1,598 withheld absence findings until the 420 local
  instrumentation gaps are reduced.
- The 37 vacuous-postcondition rows mostly describe the own postconditions of
  admitted axioms. Present those as trust boundaries, not as 37 independent
  implementation failures.
- `auxiliary-only-fact` dominates the output and is mostly traceability or
  maintenance information.
- Trusted dependencies need subsystem and impact aggregation. Forty-three
  distinct trust subjects are more understandable than 241 caller/subject
  relations.
- Unused proof steps and preconditions are useful cleanup candidates, but rank
  below public-boundary, vacuity, and model-adequacy gaps.

## Recommended review order

1. Fix and test the cross-account `Authorization` conversion.
2. Make `ValidatedAuthSpec.auth_spec` private and expose only immutable access.
3. Add a semantic contract or verified adapter for the public API boundary,
   including ARC conversion and error behavior.
4. Investigate the contradiction behind the cross-account PassRole theorem and
   verify the executable data-plane check.
5. Decide and implement the intended `populate_on_type_level` semantics in both
   model and code.
6. Validate the LLM-translated specification against its source requirements.
7. Reduce or independently test the ARN/string/hash trust foundation.
8. Close the 420 local measurement gaps, rerun, and only then triage the
   withheld absence findings.

## What “verified” means here

The accurate statement is:

> DaffodilAuthzRust verifies a substantial internal authorization-context
> implementation against its Verus model, including several grounded
> top-level properties. The public runtime path still contains unverified
> validation, safety, and conversion boundaries, including a concrete
> cross-account conversion failure.

