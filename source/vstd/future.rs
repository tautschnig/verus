#![feature(rustc_attrs)]
#![allow(unused_imports)]

use super::prelude::*;
use core::future::*;
verus! {

#[verifier::external_trait_specification]
pub trait ExFuture {
    type ExternalTraitSpecificationFor: core::future::Future;

    type Output;
}

pub trait FutureAdditionalSpecFns<T>: Future<Output = T> {
    #[verifier::prophetic]
    spec fn view(&self) -> T;

    #[verifier::prophetic]
    spec fn awaited(&self) -> bool;
}

impl<V, T: Future<Output = V>> FutureAdditionalSpecFns<V> for T {
    #[verifier::prophetic]
    uninterp spec fn view(&self) -> V;

    #[verifier::prophetic]
    uninterp spec fn awaited(&self) -> bool;
}

// Do not call this function. Call the regular Rust `await` keyword instead.
/// The future of an `async { .. }` block. Don't call this directly; Verus inserts it. The
/// block's body `c` has been verified; nothing is known about the future (its `view`, the
/// value an `.await` yields, is unconstrained).
#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::future::async_block_future")]
pub fn async_block_future<C, F>(#[allow(unused_variables)] c: C) -> F
    opens_invariants none
    no_unwind
{
    unimplemented!()
}

#[verifier::external_body]
fn exec_await<F: Future>(
    #[allow(unused_variables)]
    future: F,
) -> (ret: F::Output)
    ensures
        future.awaited() == true,
        ret == future@,
    opens_invariants any
{
    unimplemented!()
}

} // verus!
