#![allow(unused_imports)]

use super::super::prelude::*;
use core::ops::{Deref, DerefMut};
use core::pin::Pin;

verus! {

/*
 * `Pin<P>` is a wrapper around a pointer `P` whose only guarantee (that the pointee is not
 * moved) is an *aliasing* discipline, not a functional one. For `P::Target: Unpin` the wrapper
 * is fully transparent: `Pin::new`, `get_mut`, `as_mut`, `into_inner` and the `Deref` impls
 * are identities on the pointer. That is the fragment modelled here. The pin projections and
 * the `!Unpin` methods (`new_unchecked`, `get_unchecked_mut`, `map_unchecked_mut`) are not
 * specified: they are exactly the operations whose correctness depends on the aliasing
 * discipline, which this model does not capture.
 */

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types_in_ground_variants(P)]
pub struct ExPin<P>(Pin<P>);

pub trait PinAdditionalFns<P> {
    /// The wrapped pointer.
    spec fn pointer(&self) -> P;
}

impl<P> PinAdditionalFns<P> for Pin<P> {
    uninterp spec fn pointer(&self) -> P;
}

impl<P> View for Pin<P> {
    type V = P;

    open spec fn view(&self) -> Self::V {
        self.pointer()
    }
}

pub assume_specification<P: Deref>[ Pin::<P>::new ](pointer: P) -> (res: Pin<P>)
    where
        P::Target: Unpin,
    ensures
        res.pointer() == pointer,
;

pub assume_specification<P: Deref>[ Pin::<P>::into_inner ](pin: Pin<P>) -> (res: P)
    where
        P::Target: Unpin,
    ensures
        res == pin.pointer(),
;

pub assume_specification<'a, T: ?Sized>[ Pin::<&'a mut T>::get_mut ](pin: Pin<&'a mut T>) -> (res: &'a mut T)
    where
        T: Unpin,
    ensures
        res == pin.pointer(),
;

pub assume_specification<'a, T: ?Sized>[ Pin::<&'a T>::get_ref ](pin: Pin<&'a T>) -> (res: &'a T)
    ensures
        res == pin.pointer(),
;

// `<Pin<P> as Deref>::deref`, `DerefMut::deref_mut` and `Pin::as_mut` are not specified:
// `assume_specification` must match their generic signatures over `Ptr: Deref(Mut)` and
// return `Ptr::Target`, and vstd has no spec-level `Deref` to state the result for an
// arbitrary `Ptr`. Use `get_ref`/`get_mut`/`into_inner`, which are specified above; the
// compiler-inserted pin adjustments are rejected by the front end.

} // verus!
