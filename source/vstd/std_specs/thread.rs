//! Specifications for `std::thread::spawn`, `std::thread::JoinHandle` and `core::any::Any`.
//!
//! These are the contracts of `vstd::thread::{spawn, JoinHandle}` (the verified-code
//! wrappers), attached directly to the `std` items so that unmodified code calling
//! `std::thread::spawn(..).join()` is accepted.
use super::super::prelude::*;
use core::any::{Any, TypeId};
use std::thread::JoinHandle;

verus! {

/// `Any` is declared so that `dyn Any + Send` (the payload of a panicked thread, in
/// `join`'s error type) is a Verus type. No method has a specification: `type_id` and the
/// downcasts are unspecified, so code can pass the payload along but learns nothing
/// about it.
#[verifier::external_trait_specification]
pub trait ExAny: 'static {
    type ExternalTraitSpecificationFor: core::any::Any;

    fn type_id(&self) -> TypeId;
}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExTypeId(TypeId);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExJoinHandle<T>(JoinHandle<T>);

/// The set of values the spawned thread may return: the closure's postcondition, as for
/// `vstd::thread::JoinHandle::predicate`.
pub uninterp spec fn join_handle_predicate<T>(h: JoinHandle<T>, ret: T) -> bool;

/// `spawn(f)` runs `f` on a new thread. The closure's precondition must hold (it is called
/// with no arguments); its postcondition constrains the value `join` returns.
pub assume_specification<F, T>[ std::thread::spawn::<F, T> ](f: F) -> (h: JoinHandle<T>)
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    requires
        f.requires(()),
    ensures
        forall|ret: T| #[trigger] join_handle_predicate(h, ret) ==> f.ensures((), ret),
;

/// `join` waits for the thread. `Ok(v)`: the closure returned `v`, so its postcondition
/// holds. `Err(payload)`: the thread panicked; nothing is known about the payload.
pub assume_specification<T>[ JoinHandle::<T>::join ](h: JoinHandle<T>) -> (r: std::thread::Result<T>)
    ensures
        r matches Ok(v) ==> join_handle_predicate(h, v),
;

} // verus!
