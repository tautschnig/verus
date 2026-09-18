# Top semantic proof-coverage gaps

The package reports **710 verified, 0 errors**. This means that Verus proved the
generated obligations against the contracts and specifications that were
written. It does **not** mean that every intended SAML rule is present in those
contracts, or that every runtime validation path is included in the verified
build.

Most findings below are therefore not claims that the current implementation is
wrong. They show behavior-changing regressions that the present proof would not
detect.

## Top 10

| # | Gap | Where the connection breaks | Evidence |
|---:|---|---|---|
| 1 | The public assertion validator has no semantic postcondition. | **Exec → contract** | Coverage reports `has_declared_goals=false`. Replacing `validate_assertion` with unconditional `ValidationResult::Valid` still produced **710 verified, 0 errors**. |
| 2 | Cryptographic authenticity is outside the verified claim. | **Verification boundary** | The public validator performs structural signature checks only. The real crypto implementation is excluded from Verus; its stub proves field presence, not digest or signature correctness. |
| 3 | Action/negation exclusion is absent from the verified statement model. | **Spec + verification boundary** | The production check is under `cfg(not(verus_keep_ghost))`; the specification observes only the action count. Replacing the checker with an empty result still produced **710/0**. |
| 4 | Duplicate attributes within one `AttributeStatement` are not established. | **Exec → spec** | The helper has no postcondition connecting its result to uniqueness. Returning no violations still produced **708/0**. |
| 5 | Duplicate attributes across statements are not established. | **Exec → spec** | The helper guarantees only that the violation vector does not shrink. Returning immediately still produced **706/0**. |
| 6 | Attribute-value semantics are represented by a predicate whose body is `true`. | **Specification** | `SpecAttribute` contains the values, but `spec_attribute_value_semantics_valid` places no constraint on them. Any proof using this conjunct gets no value-level guarantee. |
| 7 | Several validation-affecting runtime blocks are excluded from Verus. | **Verification boundary** | Subject IP-address enforcement, URI-fragment rejection, URI normalization, and related checks mutate the runtime violation list only inside `cfg(not(verus_keep_ghost))` blocks. |
| 8 | Some validators prove soundness but not completeness. | **Contract strength** | `is_valid_rfc4514_dn` guarantees only `result ==> valid`. An implementation returning `false` for every input still produced **710/0**. Extension validators similarly permit rejecting valid extensions. |
| 9 | Parser behavior can change outside the stated contract. | **Exec → contract** | `parse_number` specifies only result bounds and digit characters. Disabling its leading-zero rejection branch still produced **710/0**. |
| 10 | A theorem advertised as proving clock-skew behavior proves only `true`. | **Proof goal** | `lemma_clock_skew_widens_window` has `ensures true`; its positive-skew precondition is consequently unused. |

## Representative locations

- Public entry point: `src/saml/validator/mod.rs:60`
- Cryptographic stub: `src/saml/validator/signature_crypto_stub.rs:36`
- Action exclusion and skipped call: `src/saml/validator/action.rs:50`,
  `src/saml/types/statements.rs:1060`
- Duplicate checks: `src/saml/types/attribute.rs:792`,
  `src/saml/types/assertion.rs:666`
- Vacuous attribute-value predicate:
  `verus/spec/saml/validator/attribute.rs:115`
- Other skipped runtime checks: `src/saml/types/subject.rs:547`,
  `src/saml/types/statements.rs:561`
- One-way RFC4514 contract: `src/ldap/validator/rfc4514.rs:609`
- Under-specified parser branch: `src/ldap/validator/rfc4514.rs:96`
- Vacuous clock-skew theorem:
  `verus/proof/saml/validator/conditions.rs:455`

## Where the fault is

The current implementation often contains the intended check. The dominant
problem is that the check is not connected to the property ultimately claimed:

```text
intended SAML rule
        ↓
specification predicate
        ↓
function contract
        ↓
executable implementation
        ↓
public validation result
```

A green verification result covers only links that were actually stated and
included in the Verus build. In this package, gaps appear at every link except
solver discharge: the solver is generally proving the obligations it was
given.

The clearest summary is:

> The executable code frequently implements more security policy than the
> verified specification observes.

For the analyzer, a public validation entry point with no declared goal should
itself be a high-priority finding. Falling back to internal measured obligations
does not answer what callers are entitled to conclude from `Valid`.

## Important reachability correction

`validate_time_bounds` also has a weak metadata-only contract and can be
replaced by an empty result while preserving **710/0**. However, it is currently
called only by its tests; production condition constructors implement and
verify their time checks separately. It is therefore a real contract gap, but
not currently a production validation bypass.

All mutations were performed independently in a temporary copy. The subject
package was not modified.
