# YuccaRust semantic proof-coverage review

Date: 2026-09-15

## Bottom line

YuccaRust has a substantially stronger end-to-end proof story than the SAML
package. Its public `Engine::evaluate` result is connected to an authorization
specification, and deleting the authorization call makes verification fail.

The main assurance gap is elsewhere:

```text
runtime parser/library behavior
        ↓  trusted or admitted correspondence
Verus specification
        ↓  mostly verified implementation chain
public authorization result
```

The highest-priority review is therefore the trusted conversion layer used by
IP, date, numeric, binary, and case-insensitive condition operators. A green
verification run proves authorization relative to those assumed models; it
does not prove that each concrete parser or library operation implements its
model.

## Subject and run

The subject was the current working tree at:

```text
/workplace/wmahasai/Verus/src/YuccaRust
commit 2bfcfadbf03350bf1dd898cb18757d337738eb09
```

The working tree already contained local changes. It was inspected and
verified without modification. Counterfactual mutations were made only in a
temporary copy.

Verification results:

| Crate | Result |
|---|---:|
| `common` | 156 verified, 0 errors |
| `engine` | 381 verified, 0 errors |

Coverage evidence:

| Measurement | Result |
|---|---:|
| Queries | 3,198 |
| Queries with measured evidence | 3,108 |
| Premise occurrences | 11,956; 0 unresolved |
| Source obligations | 2,561; 0 unresolved |
| Declared local clauses | 1,853 |
| Measured local clauses | 1,794 |
| Report status | `Overapproximated` |
| Findings | 873 total; 407 defensible; 466 withheld |

Both records pass the analyzer's structural audit. Evidence completeness is
not perfect: 59 local clauses were not measured, and the producer reported 85
requested measurements unavailable across the two crates.

## Top 10 review items

| # | Finding or gap | Assurance break | Evidence |
|---:|---|---|---|
| 1 | Non-integer date parsing is trusted. | **Runtime → specification** | `engine/src/type_conversion.rs:33` delegates to the ordinary Rust datetime parser, while `:349` supplies an `assume_specification`. Replacing the parser result with `None` still produced **381 verified, 0 errors**. |
| 2 | IP parsing and range behavior are trusted. | **Runtime → specification** | Most of `engine/src/ip_address.rs` and `ip_range.rs` is `external_body`; `parse_v4_in_v6_address` is explicitly “intentionally unverified.” Replacing top-level IP parsing with `None` still produced **381/0**. |
| 3 | Numeric condition semantics depend on assumed parsing and comparison models. | **Runtime/library → specification** | `parse_i64` is `external_body`; `parse_bigdecimal` is external and connected by `assume_specification`; `BigDecimal` uses an abstract view and assumed comparison contracts. This underlies all `Numeric*` policy operators. |
| 4 | Binary condition semantics depend on assumed Base64 models. | **Runtime/library → specification** | Base64 encode/decode are external functions with assumed contracts. The encode/decode round-trip theorem at `type_conversion_spec.rs:263` is admitted and reported wholly vacuous. |
| 5 | Case-insensitive and wildcard matching rest on an admitted Unicode foundation. | **Trusted proof foundation** | Thirteen `admit()` sites define lowercase/string-length properties across `string_utils_spec.rs`, `verus_utils.rs`, and `verus/stdlib.rs`. Coverage reports their theorem postconditions as wholly vacuous/trusted. |
| 6 | The analyzer cannot currently explain the public authorization roots. | **Coverage evidence** | `Engine::evaluate`, `evaluate_gen`, and legacy evaluation have strong semantic postconditions, but their root slices are `Ungrounded`. Their absence findings are correctly withheld. This is an analyzer limitation, not evidence that the functions failed verification. |
| 7 | The central operator dispatcher has two vacuous paths. | **Proof path** | `eval_operator::apply` has partial vacuity on **2 of 31** postcondition terminals. The source shape indicates the duplicated `None => return false` branches at lines 49 and 72 are already excluded by the initial missing-value guard. This looks like dead defensive code, not whole-contract vacuity. |
| 8 | Important policy loops are missing local coverage evidence. | **Coverage instrumentation** | The 59 unmeasured local clauses include 42 loop invariants in policy, principal, statement, and request validation code; 11 requires clauses; and 6 ensures clauses. |
| 9 | Proof-function contracts contain unnecessary premises. | **Proof maintenance** | The analyzer reports 71 defensible unused preconditions. Every one is in proof mode, concentrated in condition theorems, bit-set lemmas, and ARN lemmas. No executable API precondition is implicated by this category. |
| 10 | There is removable proof scaffolding. | **Proof maintenance** | There are 42 defensible checked-but-unused proof steps and 16 unobserved reveals. Deleting the reported assertion at `engine/src/arn.rs:329` still produced **381/0**, confirming one representative cleanup finding. |

## Counterfactual evidence

Each experiment was applied alone in a temporary package copy.

| Experiment | Verification result | Interpretation |
|---|---:|---|
| Replace `parse_arbitrary_object_to_epoch_millis` with `None` | 381 verified, 0 errors | Concrete ISO-8601 parsing is outside the proof |
| Replace `ip_address::parse` with `None` | 381 verified, 0 errors | Concrete IP parsing is outside the proof |
| Remove the `evaluate_gen` call from public `Engine::evaluate` | 380 verified, 1 error; all three result postconditions fail | The public authorization contract is meaningful and observes the authorization call |
| Delete the assertion equating ARN split results with the specification | 381 verified, 0 errors | Confirmed redundant proof step |

The IP source also contains a test accepting a malformed-looking trailing
triple-colon address as equivalent to a canonical IPv6 address. This may be an
intentional Java-compatibility rule, but because parser correctness is trusted,
the intended language should be reviewed and documented independently of the
Verus proof.

## How to interpret the raw findings

The 873 rows are not 873 defects.

- The 466 withheld rows have incomplete root evidence and should not be acted
  on.
- The 349 `auxiliary-only-fact` rows are traceability information.
- Most of the 188 `goal-without-body-support` rows are direct accessors,
  constructors, clones, or expression bodies whose support is not represented
  as a labeled premise. They should not be presented as 188 weak contracts.
- The 71 unused preconditions are proof-contract cleanup, not runtime API
  failures.
- Trusted dependencies should be aggregated by semantic subsystem: IP, date,
  numeric, Base64, lowercase/string, hashing, and clone/view models.

## Recommended review order

1. Validate or replace the assumed date-parser correspondence.
2. Validate the IP parser/range correspondence, including compatibility edge
   cases.
3. Audit numeric and Base64 assumed specifications against their libraries.
4. Reduce or justify the admitted lowercase and string-length axioms.
5. Fix root grounding and the 59 local instrumentation gaps, then rerun the
   package before making strong absence claims about the authorization path.
6. Clean up sampled unused proof steps, reveals, and proof preconditions.

## What “verified” means here

The encouraging result is that the public authorization API is not merely
decorated with a weak contract: a behavior-changing mutation to its core call
is rejected.

The qualification is that several values entering that verified authorization
chain are interpreted through trusted parsers, library models, and admitted
Unicode lemmas. The most accurate statement is:

> YuccaRust verifies the authorization algorithm against its Verus model, while
> several security-relevant runtime-to-model correspondences remain trusted.

