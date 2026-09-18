#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Dual-solver cross-checking (design 05 §2): with `-V cross-check`, every default-prover
// query runs on a cvc5 secondary alongside the Z3 primary over the identical solver-neutral
// stream, and the two verdicts are reconciled. These tests exercise the two ends of the
// reconciliation table: agreement (no diagnostics) and an unsat/sat disagreement (hard
// error + dump).

// (a) A normal program verifies under cross-check with NO warnings: both z3 and cvc5
// independently discharge every obligation, so reconcile() returns UsePrimary throughout.
test_verify_one_file_with_options! {
    #[test] cross_check_agreement_no_warnings ["-V cross-check"] => verus_code! {
        fn add_one(x: u32) -> (r: u32)
            requires x < 10,
            ensures r == x + 1,
        {
            x + 1
        }

        proof fn mono(a: int, b: int)
            requires a <= b,
            ensures a + 1 <= b + 1,
        {
        }

        spec fn f(n: nat) -> nat { n + 1 }

        proof fn about_f(n: nat)
            ensures f(n) > n,
        {
        }
    } => Ok(err) => {
        assert!(
            err.warnings.is_empty(),
            "expected no cross-check warnings, got: {:?}",
            err.warnings.iter().map(|w| w.message.clone()).collect::<Vec<_>>(),
        );
    }
}

// (b) The injected-disagreement path (test-only `-V cross-check-inject-disagreement` forces
// the secondary to report `sat` on a primary `unsat`) produces a hard error. Under the async
// (detached-secondary) design the secondary answers off the critical path, so the
// disagreement is discovered on the background worker and surfaced at CRATE END: it must
// still fail the build (non-zero exit) with an `error:` diagnostic naming the function and
// pointing at the dump under `.verus-solver-log/disagreement-<n>.smt2`.
test_verify_one_file_with_options! {
    #[test] cross_check_injected_disagreement_is_hard_error
        ["-V cross-check", "-V cross-check-inject-disagreement"] => verus_code! {
        fn add_one(x: u32) -> (r: u32)
            requires x < 10,
            ensures r == x + 1,
        {
            x + 1
        }
    } => Err(err) => {
        // The crate-end join surfaced the disagreement as a build-failing error (this is the
        // `Err` arm, so the process exited non-zero) naming both solvers, the function, and
        // the dump file.
        assert!(
            err.errors.iter().any(|e| {
                e.message.contains("cross-check disagreement")
                    && e.message.contains("add_one")
                    && e.message.contains("z3 reported unsat")
                    && e.message.contains("cvc5 reported sat")
                    && e.message.contains("disagreement-")
            }),
            "expected a crate-end cross-check disagreement hard error naming the function, both \
             solvers, and the dump file, got: {:?}",
            err.errors.iter().map(|e| e.message.clone()).collect::<Vec<_>>(),
        );
    }
}

// (c) Under `-V cross-check-strict`, the same injected disagreement is still a build-failing
// hard error surfaced at crate end (Strict is a superset of Warn for the disagreement rows of
// the reconciliation table).
test_verify_one_file_with_options! {
    #[test] cross_check_strict_injected_disagreement_is_hard_error
        ["-V cross-check-strict", "-V cross-check-inject-disagreement"] => verus_code! {
        fn add_one(x: u32) -> (r: u32)
            requires x < 10,
            ensures r == x + 1,
        {
            x + 1
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| {
                e.message.contains("cross-check disagreement") && e.message.contains("add_one")
            }),
            "expected a crate-end cross-check disagreement hard error naming the function, got: \
             {:?}",
            err.errors.iter().map(|e| e.message.clone()).collect::<Vec<_>>(),
        );
    }
}
