//! `core::future::Future` and `IntoFuture`: declared, content-free. Verus verifies an
//! `async fn` body as a function and treats the future it returns as an opaque value
//! (`rust_to_vir` for async blocks); these declarations let specifications name the traits
//! as bounds (`tokio::time::timeout<F: IntoFuture>`, `tokio::spawn<F: Future>`).
use super::super::prelude::*;

verus! {

#[verifier::external_trait_specification]
pub trait ExFuture {
    type ExternalTraitSpecificationFor: core::future::Future;

    type Output;

    /// Content-free: whether the future is ready, and with what, is not modelled.
    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output>;
}

#[verifier::external_type_specification]
#[verifier::accept_recursive_types(T)]
pub struct ExPoll<T>(core::task::Poll<T>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExContext<'a>(core::task::Context<'a>);

#[verifier::external_trait_specification]
pub trait ExIntoFuture {
    type ExternalTraitSpecificationFor: core::future::IntoFuture;

    type Output;

    type IntoFuture: core::future::Future<Output = Self::Output>;

    /// `.await` calls this. Nothing is said about the future (Verus does not model futures).
    fn into_future(self) -> Self::IntoFuture;
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(F)]
pub struct ExPollFn<F>(core::future::PollFn<F>);

/// `poll_fn(f)` (used by `tokio::select!`): content-free.
pub assume_specification<T, F: FnMut(&mut core::task::Context<'_>) -> core::task::Poll<T>>[
    core::future::poll_fn
](f: F) -> core::future::PollFn<F>;

} // verus!
