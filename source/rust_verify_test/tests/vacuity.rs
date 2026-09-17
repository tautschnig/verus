#![feature(rustc_private)]
#![allow(unused_imports)]
//! Regression tests for the `-V vacuity-checks` lint (precondition satisfiability).
//!
//! The lint emits a *warning* (never an error, and never changes a verification verdict) for any
//! verified function whose `requires` clauses are jointly unsatisfiable: every obligation in such a
//! function is vacuously discharged. See `poc/4/` for the measured "creative false" corpus that
//! motivates this check.

#[macro_use]
mod common;
use common::*;

const VACUITY_MSG: &str = "vacuously verified";

// ----------------------------------------------------------------------------
// Vectors that the precondition-satisfiability probe SHOULD catch.
// ----------------------------------------------------------------------------

// V2: directly contradictory `requires`.
test_verify_one_file_with_options! {
    #[test] v2_contradictory_requires ["-V vacuity-checks"] => verus_code! {
        fn f(x: u64) -> (r: u64)
            requires x > 0, x < 0,
            ensures r == 42,
        { 0 }
    } => Ok(err) => {
        assert!(err.warnings.iter().any(|w| w.message.contains(VACUITY_MSG)),
            "expected a vacuity warning, got: {:?}", err.warnings);
    }
}

// V3: contradiction hidden behind a `closed spec fn` (the probe pierces the opaque definition
// because it discharges `assert(false)` under the entry assumptions, not via an unsat core).
test_verify_one_file_with_options! {
    #[test] v3_opaque_false_spec ["-V vacuity-checks"] => verus_code! {
        closed spec fn p(x: u64) -> bool { x != x }
        fn f(x: u64) -> (r: u64)
            requires p(x),
            ensures r == 42,
        { 0 }
    } => Ok(err) => {
        assert!(err.warnings.iter().any(|w| w.message.contains(VACUITY_MSG)),
            "expected a vacuity warning, got: {:?}", err.warnings);
    }
}

// V13: an API precondition that no caller can ever satisfy.
test_verify_one_file_with_options! {
    #[test] v13_unsatisfiable_api ["-V vacuity-checks"] => verus_code! {
        fn api(x: u64) -> (r: u64)
            requires x == 42 && x == 43,
            ensures r == 0,
        { 0 }
    } => Ok(err) => {
        assert!(err.warnings.iter().any(|w| w.message.contains(VACUITY_MSG)),
            "expected a vacuity warning, got: {:?}", err.warnings);
    }
}

// Contradiction expressed via integer arithmetic that the solver can decide.
test_verify_one_file_with_options! {
    #[test] arith_contradiction ["-V vacuity-checks"] => verus_code! {
        fn f(x: u64) -> (r: u64)
            requires x >= 10, x <= 5,
            ensures r == 42,
        { 0 }
    } => Ok(err) => {
        assert!(err.warnings.iter().any(|w| w.message.contains(VACUITY_MSG)),
            "expected a vacuity warning, got: {:?}", err.warnings);
    }
}

// The lint must not change the verdict: the same contradictory-`requires` function reports
// exactly zero warnings when the flag is absent (default behaviour).
test_verify_one_file! {
    #[test] no_flag_no_warning verus_code! {
        fn f(x: u64) -> (r: u64)
            requires x > 0, x < 0,
            ensures r == 42,
        { 0 }
    } => Ok(())
}

// ----------------------------------------------------------------------------
// Controls with SATISFIABLE preconditions: the probe must NOT warn (no false positives).
// ----------------------------------------------------------------------------

test_verify_one_file_with_options! {
    #[test] control_satisfiable_single ["-V vacuity-checks"] => verus_code! {
        fn c1(x: u64) -> (r: u64)
            requires x > 0,
            ensures r == x,
        { x }
    } => Ok(err) => {
        assert!(!err.warnings.iter().any(|w| w.message.contains(VACUITY_MSG)),
            "unexpected vacuity warning (false positive): {:?}", err.warnings);
    }
}

test_verify_one_file_with_options! {
    #[test] control_satisfiable_multi ["-V vacuity-checks"] => verus_code! {
        fn c2(x: u64, y: u64) -> (r: u64)
            requires x < y, x > 0,
            ensures r >= 0,
        { x }
    } => Ok(err) => {
        assert!(!err.warnings.iter().any(|w| w.message.contains(VACUITY_MSG)),
            "unexpected vacuity warning (false positive): {:?}", err.warnings);
    }
}

test_verify_one_file_with_options! {
    #[test] control_satisfiable_equality ["-V vacuity-checks"] => verus_code! {
        fn c3(x: int) -> (r: int)
            requires x == 42,
            ensures r == 42,
        { x }
    } => Ok(err) => {
        assert!(!err.warnings.iter().any(|w| w.message.contains(VACUITY_MSG)),
            "unexpected vacuity warning (false positive): {:?}", err.warnings);
    }
}

// A function with no `requires` at all is outside the probe's scope: it must not warn.
test_verify_one_file_with_options! {
    #[test] control_no_requires ["-V vacuity-checks"] => verus_code! {
        fn c4() -> (r: u64)
            ensures r == 0,
        { 0 }
    } => Ok(err) => {
        assert!(!err.warnings.iter().any(|w| w.message.contains(VACUITY_MSG)),
            "unexpected vacuity warning (false positive): {:?}", err.warnings);
    }
}

// ----------------------------------------------------------------------------
// Soundness boundary: the probe reports only *provable* unsatisfiability.
// ----------------------------------------------------------------------------

// V4: the precondition `forall|i| g(i) > g(i)` is semantically unsatisfiable, but the solver never
// instantiates the quantifier, so it cannot *prove* unsatisfiability. The honest behaviour is to
// NOT warn (no false claim of detection). The function itself still fails its postcondition, which
// the lint must not disturb.
test_verify_one_file_with_options! {
    #[test] v4_quant_contradiction_not_claimed ["-V vacuity-checks"] => verus_code! {
        uninterp spec fn g(i: int) -> int;
        fn f() -> (r: u64)
            requires forall|i: int| g(i) > g(i),
            ensures r == 42,
        { 0 }
    } => Err(err) => {
        assert!(!err.warnings.iter().any(|w| w.message.contains(VACUITY_MSG)),
            "vacuity probe must not claim unprovable unsatisfiability: {:?}", err.warnings);
    }
}
