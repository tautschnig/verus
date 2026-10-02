//! `std::sync::OnceLock`: content-free. Which value a `OnceLock` holds depends on which thread
//! initialised it first, so nothing is said about it; `get_or_init` may run `f`, so `f`'s
//! precondition must hold.
use super::super::prelude::*;
use std::sync::OnceLock;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExOnceLock<T>(OnceLock<T>);

pub assume_specification<T>[ OnceLock::<T>::new ]() -> OnceLock<T>;

pub assume_specification<T>[ OnceLock::<T>::get ](l: &OnceLock<T>) -> Option<&T>;

pub assume_specification<T, F: FnOnce() -> T>[ OnceLock::<T>::get_or_init::<F> ](l: &OnceLock<T>, f: F) -> &T
    requires
        f.requires(()),
;

} // verus!
