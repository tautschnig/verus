//! Acceptance-only specifications for `Cell`, `RefCell` and `Mutex`.
//!
//! These types mutate through a shared reference. Verus models `&T` as the value `T` and
//! assumes it does not change while the reference is live, so any specification that ties
//! the contents of a cell to what a later `get`/`borrow`/`lock` returns would be unsound
//! (two reads through the same `&Cell` could be proved equal across an intervening `set`).
//! The specifications here therefore say nothing about contents: the types are opaque,
//! every read returns an unconstrained value, writes are accepted, and a `RefCell` borrow
//! or a `Mutex` lock may fail (panic or `Err`) as far as verification knows. Code using them
//! is accepted and verified for everything else; properties that depend on a cell's
//! contents need `vstd::cell::PCell` / `vstd::rwlock` instead, which carry permissions.
use super::super::prelude::*;
use core::cell::{Cell, Ref, RefCell, RefMut};

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExCell<T: ?Sized>(Cell<T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExRefCell<T: ?Sized>(RefCell<T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExRef<'b, T: ?Sized + 'b>(Ref<'b, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExRefMut<'b, T: ?Sized + 'b>(RefMut<'b, T>);

pub assume_specification<T>[ Cell::<T>::new ](v: T) -> Cell<T>;

pub assume_specification<T: Copy>[ Cell::<T>::get ](c: &Cell<T>) -> T;

pub assume_specification<T>[ Cell::<T>::set ](c: &Cell<T>, v: T);

pub assume_specification<T>[ Cell::<T>::replace ](c: &Cell<T>, v: T) -> T;

pub assume_specification<T>[ Cell::<T>::into_inner ](c: Cell<T>) -> T;

pub assume_specification<T>[ RefCell::<T>::new ](v: T) -> RefCell<T>;

/// May panic (if mutably borrowed): no `no_unwind`.
pub assume_specification<T: ?Sized>[ RefCell::<T>::borrow ](c: &RefCell<T>) -> Ref<'_, T>;

/// May panic (if borrowed): no `no_unwind`.
pub assume_specification<T: ?Sized>[ RefCell::<T>::borrow_mut ](c: &RefCell<T>) -> RefMut<'_, T>;

pub assume_specification<T>[ RefCell::<T>::replace ](c: &RefCell<T>, v: T) -> T;

pub assume_specification<T>[ RefCell::<T>::into_inner ](c: RefCell<T>) -> T;

pub assume_specification<'a, 'b, T: ?Sized + 'b>[ <Ref<'b, T> as core::ops::Deref>::deref ](r: &'a Ref<'b, T>) -> &'a T;

pub assume_specification<'a, 'b, T: ?Sized + 'b>[ <RefMut<'b, T> as core::ops::Deref>::deref ](r: &'a RefMut<'b, T>) -> &'a T;

pub assume_specification<'a, 'b, T: ?Sized + 'b>[ <RefMut<'b, T> as core::ops::DerefMut>::deref_mut ](r: &'a mut RefMut<'b, T>) -> &'a mut T;

} // verus!

#[cfg(feature = "std")]
pub mod sync {
    use super::super::super::prelude::*;
    use std::sync::{LockResult, Mutex, MutexGuard, PoisonError};

    verus! {

    #[verifier::external_type_specification]
    #[verifier::external_body]
    #[verifier::reject_recursive_types(T)]
    pub struct ExMutex<T: ?Sized>(Mutex<T>);

    #[verifier::external_type_specification]
    #[verifier::external_body]
    #[verifier::reject_recursive_types(T)]
    pub struct ExMutexGuard<'a, T: ?Sized>(MutexGuard<'a, T>);

    #[verifier::external_type_specification]
    #[verifier::external_body]
    #[verifier::accept_recursive_types(T)]
    pub struct ExPoisonError<T>(PoisonError<T>);

    pub assume_specification<T>[ Mutex::<T>::new ](v: T) -> Mutex<T>;

    /// `Err` if poisoned; blocks otherwise. Nothing is known about the protected value.
    pub assume_specification<T: ?Sized>[ Mutex::<T>::lock ](m: &Mutex<T>) -> LockResult<MutexGuard<'_, T>>;


    pub assume_specification<'b, 'a, T: ?Sized + 'a>[ <MutexGuard<'a, T> as core::ops::Deref>::deref ](g: &'b MutexGuard<'a, T>) -> &'b T;

    pub assume_specification<'b, 'a, T: ?Sized + 'a>[ <MutexGuard<'a, T> as core::ops::DerefMut>::deref_mut ](g: &'b mut MutexGuard<'a, T>) -> &'b mut T;

    pub assume_specification<T>[ PoisonError::<T>::into_inner ](e: PoisonError<T>) -> T;

    } // verus!
}
