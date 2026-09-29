use super::super::prelude::*;

verus! {

// array == array
pub assume_specification<T: PartialEq<U>, U, const N: usize>[ <[T; N] as PartialEq<[U; N]>>::eq ](
    left: &[T; N],
    right: &[U; N],
) -> bool
;

impl<T, U, const N: usize> super::cmp::PartialEqSpecImpl<[U; N]> for [T; N] where
    T: PartialEq<U> + super::cmp::PartialEqSpec<U>,
 {
    open spec fn obeys_eq_spec() -> bool {
        <T as super::cmp::PartialEqSpec<U>>::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &[U; N]) -> bool {
        forall|i: int|
            #![auto]
            0 <= i < N ==> <T as super::cmp::PartialEqSpec<U>>::eq_spec(&self@[i], &other@[i])
    }
}

// slice ref == array
pub assume_specification<'a, T: PartialEq<U>, U, const N: usize>[ <&'a [T] as PartialEq<
    [U; N],
>>::eq ](left: &&'a [T], right: &[U; N]) -> bool
;

impl<'a, T, U, const N: usize> super::cmp::PartialEqSpecImpl<[U; N]> for &'a [T] where
    T: PartialEq<U> + super::cmp::PartialEqSpec<U>,
 {
    open spec fn obeys_eq_spec() -> bool {
        <T as super::cmp::PartialEqSpec<U>>::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &[U; N]) -> bool {
        &&& (*self)@.len() == other@.len()
        &&& forall|i: int|
            #![auto]
            0 <= i < (*self)@.len() ==> <T as super::cmp::PartialEqSpec<U>>::eq_spec(
                &(*self)@[i],
                &other@[i],
            )
    }
}

// array == slice ref
pub assume_specification<'a, T: PartialEq<U>, U, const N: usize>[ <[T; N] as PartialEq<&[U]>>::eq ](
    left: &[T; N],
    right: &&[U],
) -> bool
;

impl<'a, T, U, const N: usize> super::cmp::PartialEqSpecImpl<&'a [U]> for [T; N] where
    T: PartialEq<U> + super::cmp::PartialEqSpec<U>,
 {
    open spec fn obeys_eq_spec() -> bool {
        <T as super::cmp::PartialEqSpec<U>>::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &&'a [U]) -> bool {
        &&& self@.len() == (*other)@.len()
        &&& forall|i: int|
            #![auto]
            0 <= i < self@.len() ==> <T as super::cmp::PartialEqSpec<U>>::eq_spec(
                &self@[i],
                &(*other)@[i],
            )
    }
}

// slice == array
pub assume_specification<T: PartialEq<U>, U, const N: usize>[ <[T] as PartialEq<[U; N]>>::eq ](
    left: &[T],
    right: &[U; N],
) -> bool
;

impl<T, U, const N: usize> super::cmp::PartialEqSpecImpl<[U; N]> for [T] where
    T: PartialEq<U> + super::cmp::PartialEqSpec<U>,
 {
    open spec fn obeys_eq_spec() -> bool {
        <T as super::cmp::PartialEqSpec<U>>::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &[U; N]) -> bool {
        &&& self@.len() == other@.len()
        &&& forall|i: int|
            #![auto]
            0 <= i < self@.len() ==> <T as super::cmp::PartialEqSpec<U>>::eq_spec(
                &self@[i],
                &other@[i],
            )
    }
}

// array == slice
pub assume_specification<T: PartialEq<U>, U, const N: usize>[ <[T; N] as PartialEq<[U]>>::eq ](
    left: &[T; N],
    right: &[U],
) -> bool
;

impl<T, U, const N: usize> super::cmp::PartialEqSpecImpl<[U]> for [T; N] where
    T: PartialEq<U> + super::cmp::PartialEqSpec<U>,
 {
    open spec fn obeys_eq_spec() -> bool {
        <T as super::cmp::PartialEqSpec<U>>::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &[U]) -> bool {
        &&& self@.len() == other@.len()
        &&& forall|i: int|
            #![auto]
            0 <= i < self@.len() ==> <T as super::cmp::PartialEqSpec<U>>::eq_spec(
                &self@[i],
                &other@[i],
            )
    }
}


// `for x in [a, b, c]` (by value): `core::array::IntoIter`, specified like `vec::IntoIter`.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExArrayIntoIter<T, const N: usize>(core::array::IntoIter<T, N>);

/// The elements of an array iteration, fixed at construction (like `vec::into_iter_elts`).
pub uninterp spec fn array_into_iter_elts<T, const N: usize>(i: core::array::IntoIter<T, N>) -> Seq<T>;

impl<T, const N: usize> super::iter::IteratorSpecImpl for core::array::IntoIter<T, N> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    uninterp spec fn remaining(&self) -> Seq<Self::Item>;

    uninterp spec fn will_return_none(&self) -> bool;

    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < array_into_iter_elts(*self).len() {
            Some(array_into_iter_elts(*self)[index])
        } else {
            None
        }
    }
}

impl<T, const N: usize> super::iter::DoubleEndedIteratorSpecImpl for core::array::IntoIter<T, N> {
    open spec fn peek_back(&self, index: int) -> Option<Self::Item> {
        let len = array_into_iter_elts(*self).len();
        if 0 <= index < len {
            Some(array_into_iter_elts(*self)[len - index - 1])
        } else {
            None
        }
    }
}

pub assume_specification<T, const N: usize>[ <[T; N] as core::iter::IntoIterator>::into_iter ](
    a: [T; N],
) -> (iter: <[T; N] as core::iter::IntoIterator>::IntoIter)
    ensures
        super::iter::IteratorSpec::remaining(&iter) == a@,
        array_into_iter_elts(iter) == super::iter::IteratorSpec::remaining(&iter),
        super::iter::IteratorSpec::decrease(&iter) is Some,
;

} // verus!
