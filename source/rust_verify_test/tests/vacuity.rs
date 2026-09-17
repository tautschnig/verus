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

// ----------------------------------------------------------------------------
// Obligation-reachability probe (item 1b).
// ----------------------------------------------------------------------------

const UNREACHABLE_MSG: &str = "obligation is unreachable";

// V9: an obligation guarded by `if false { .. }`. The assertion is dead code, discharged only
// because its path condition is unsatisfiable. The probe must flag it.
test_verify_one_file_with_options! {
    #[test] v9_dead_code_if_false ["-V vacuity-checks"] => verus_code! {
        fn f(x: u64) -> (r: u64)
            ensures r == 42,
        {
            if false { assert(1 == 2); }
            42
        }
    } => Ok(err) => {
        assert!(err.warnings.iter().any(|w| w.message.contains(UNREACHABLE_MSG)),
            "expected an unreachable-obligation warning for the dead assert, got: {:?}", err.warnings);
    }
}

// assume(false) / admit() render every following obligation unreachable: the reachability probe
// catches the downstream assert (V1 / V7 shapes).
test_verify_one_file_with_options! {
    #[test] reach_after_assume_false ["-V vacuity-checks"] => verus_code! {
        proof fn p() {
            assume(false);
            assert(1 == 2);
        }
    } => Ok(err) => {
        assert!(err.warnings.iter().any(|w| w.message.contains(UNREACHABLE_MSG)),
            "expected an unreachable-obligation warning after assume(false), got: {:?}", err.warnings);
    }
}

// Control: plainly reachable assertions (including a reachable `if` branch and a postcondition)
// must NOT be flagged. This guards against reachability false positives, which would be fatal on
// real code such as vstd.
test_verify_one_file_with_options! {
    #[test] reach_control_no_false_positive ["-V vacuity-checks"] => verus_code! {
        fn f(x: u64) -> (r: u64)
            requires x > 0,
            ensures r == x,
        {
            assert(x > 0);
            if x == 1 {
                assert(x <= 1);
            }
            x
        }
        proof fn g(b: bool) {
            if b { assert(b); } else { assert(!b); }
        }
    } => Ok(err) => {
        assert!(!err.warnings.iter().any(|w| w.message.contains(UNREACHABLE_MSG)),
            "unexpected unreachable-obligation warning (false positive): {:?}", err.warnings);
    }
}

// ----------------------------------------------------------------------------
// Ambient-axiom consistency probe (item 2).
// ----------------------------------------------------------------------------

const AMBIENT_MSG: &str = "ambient axioms are inconsistent";

// Two `external_body` broadcast lemmas whose ensures clauses contradict each other, revealed at
// module scope. The installed broadcast axioms alone entail `false`, so every proof in the module
// is vacuous. The probe must flag this at error level. (Cross-module to avoid Verus's cyclic
// self-reference rejection for a module-level reveal of same-module lemmas — the V6 broadcast
// shape.)
test_verify_one_file_with_options! {
    #[test] ambient_inconsistent_broadcast ["-V vacuity-checks"] => verus_code! {
        mod m {
            use vstd::prelude::*;
            pub uninterp spec fn g() -> int;

            #[verifier::external_body]
            pub broadcast proof fn a()
                ensures #[trigger] g() == 0
            { }

            #[verifier::external_body]
            pub broadcast proof fn b()
                ensures #[trigger] g() == 1
            { }
        }

        broadcast use {m::a, m::b};

        proof fn p() { }
    } => Err(err) => {
        assert!(err.errors.iter().any(|e| e.message.contains(AMBIENT_MSG)),
            "expected an ambient-inconsistency error, got errors: {:?} warnings: {:?}",
            err.errors, err.warnings);
    }
}

// Control: a consistent broadcast lemma. The ambient theory is satisfiable, so the probe must
// stay silent (no false positive that would break every consistent module, incl. vstd).
test_verify_one_file_with_options! {
    #[test] ambient_consistent_broadcast ["-V vacuity-checks"] => verus_code! {
        mod m {
            use vstd::prelude::*;
            pub uninterp spec fn g() -> int;

            #[verifier::external_body]
            pub broadcast proof fn a()
                ensures #[trigger] g() == 0
            { }
        }

        broadcast use m::a;

        proof fn p() { }
    } => Ok(err) => {
        assert!(!err.errors.iter().any(|e| e.message.contains(AMBIENT_MSG)),
            "unexpected ambient-inconsistency error (false positive): {:?}", err.errors);
    }
}

// ----------------------------------------------------------------------------
// Trusted-construct inventory (item 3).
// ----------------------------------------------------------------------------

const INVENTORY_MSG: &str = "trusted-construct inventory";

// The inventory summary lists every trusted construct in the crate. Here: an external_body fn, an
// assume, and an admit. It is emitted as a note.
test_verify_one_file_with_options! {
    #[test] inventory_lists_trusted ["-V vacuity-checks"] => verus_code! {
        #[verifier::external_body]
        fn trusted_ext() -> (r: u64) ensures r == 0 { 0 }

        proof fn uses_assume(x: int) {
            assume(x == x);
        }

        proof fn uses_admit()
            ensures false,
        {
            admit();
        }
    } => Ok(err) => {
        let inv = err.notes.iter().find(|n| n.message.contains(INVENTORY_MSG));
        assert!(inv.is_some(), "expected a trusted-construct inventory note, got notes: {:?}", err.notes);
        let inv = &inv.unwrap().message;
        assert!(inv.contains("external_body") && inv.contains("trusted_ext"),
            "inventory should list the external_body fn: {}", inv);
        assert!(inv.contains("assume") || inv.contains("admit"),
            "inventory should list the assume/admit sites: {}", inv);
    }
}
