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
}

#[verifier::external_trait_specification]
pub trait ExIntoFuture {
    type ExternalTraitSpecificationFor: core::future::IntoFuture;

    type Output;

    type IntoFuture: core::future::Future<Output = Self::Output>;
}

} // verus!
