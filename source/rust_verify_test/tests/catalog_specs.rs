#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// These tests demonstrate that catalogue examples which previously failed
// (see /home/ubuntu/verus-work/catalog/CATALOG.md) now verify thanks to the
// new `vstd` specifications added in this branch.

/////////////////////////////////////////////////////////////////////////////
// Catalogue id `println` (class R/L)
//
// Before: `println!` desugars to `std::io::_print`, which had no spec, so the
// frontend reported `std::io::stdio::_print is not supported`. Projects had to
// add their own `assume_specification` (cf. the pre-existing `std::print_ok`
// test). Now `vstd::std_specs::io` ships the spec, so a bare
// `use vstd::prelude::*;` suffices.
/////////////////////////////////////////////////////////////////////////////

test_verify_one_file! {
    #[test] catalog_println_verifies verus_code! {
        use vstd::prelude::*;

        fn show(x: u64)
            requires x < 100,
        {
            println!("x = {}", x);
        }

        fn caller() {
            show(42);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] catalog_eprintln_verifies verus_code! {
        use vstd::prelude::*;

        fn warn(code: u32) {
            eprintln!("warning code {}", code);
            eprint!("done");
        }
    } => Ok(())
}

/////////////////////////////////////////////////////////////////////////////
// Catalogue id `iterator-adaptor` (class S): `for` over `StepBy`.
//
// Before: `StepBy is not supported` (no `std_specs/iter.rs` spec). Now the
// adaptor has an `IteratorSpecImpl` + postcondition axiom, so the loop is
// accepted and the ghost loop name exposes `it.index()` for invariants.
/////////////////////////////////////////////////////////////////////////////

test_verify_one_file! {
    #[test] catalog_step_by_verifies verus_code! {
        use vstd::prelude::*;

        fn count_stepped(n: usize) -> (r: usize) {
            let mut c: usize = 0;
            for _x in it: (0..n).step_by(2)
                invariant c == it.index(),
            {
                c = c + 1;
            }
            c
        }
    } => Ok(())
}
