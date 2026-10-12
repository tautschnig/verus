use super::super::prelude::*;
use core::marker::PointeeSized;

use verus as verus_skip_verusfmt;
verus_skip_verusfmt! {

#[verifier::external_trait_specification]
pub trait ExTuple {
    type ExternalTraitSpecificationFor: core::marker::Tuple;
}

#[verifier::external_trait_specification]
pub trait ExFnOnce<Args: core::marker::Tuple> {
    type ExternalTraitSpecificationFor: core::ops::FnOnce<Args>;

    type Output;
}

#[verifier::external_trait_specification]
pub trait ExFnMut<Args: core::marker::Tuple>: FnOnce<Args> {
    type ExternalTraitSpecificationFor: core::ops::FnMut<Args>;
}

#[verifier::external_trait_specification]
pub trait ExFn<Args: core::marker::Tuple>: FnMut<Args> {
    type ExternalTraitSpecificationFor: core::ops::Fn<Args>;
}

#[verifier::external_trait_specification]
pub trait ExDeref: PointeeSized {
    type ExternalTraitSpecificationFor: core::ops::Deref;

    type Target: ?Sized;

    fn deref(&self) -> &Self::Target;
}

#[verifier::external_trait_specification]
pub trait ExDerefMut: core::ops::Deref + PointeeSized {
    type ExternalTraitSpecificationFor: core::ops::DerefMut;

    fn deref_mut(&mut self) -> &mut Self::Target;
}

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(IndexSpec via IndexSpecImpl)]
pub trait ExIndex<Idx> where Idx: ?Sized {
    type ExternalTraitSpecificationFor: core::ops::Index<Idx>;

    type Output: ?Sized;

    // NOTE: this used as a precondition for both `Index` and `IndexMut`,
    // since both share the same `s[i]` syntax.
    spec fn index_req(&self, index: &Idx) -> bool;

    fn index(&self, index: Idx) -> (output: &Self::Output) where Idx: Sized
        requires
            self.index_req(&index),
    ;
}

#[verifier::external_trait_specification]
pub trait ExIndexMut<Idx>: core::ops::Index<Idx> where Idx: ?Sized {
    type ExternalTraitSpecificationFor: core::ops::IndexMut<Idx>;

    fn index_mut(&mut self, index: Idx) -> (output: &mut Self::Output) where Idx: Sized
        requires
            self.index_req(&index),
    ;
}

#[verifier::external_trait_specification]
pub trait ExInteger: Copy {
    type ExternalTraitSpecificationFor: Integer;
}

#[verifier::external_trait_specification]
pub trait ExSpecOrd<Rhs> {
    type ExternalTraitSpecificationFor: SpecOrd<Rhs>;
}

#[cfg(not(verus_verify_core))]
#[verifier::external_trait_specification]
pub trait ExAllocator {
    type ExternalTraitSpecificationFor: core::alloc::Allocator;
}

#[verifier::external_trait_specification]
pub trait ExFreeze: PointeeSized {
    type ExternalTraitSpecificationFor: core::marker::Freeze;
}

#[verifier::external_trait_specification]
pub trait ExHasher {
    type ExternalTraitSpecificationFor: core::hash::Hasher;
}

#[verifier::external_trait_specification]
pub trait ExHash: PointeeSized {
    type ExternalTraitSpecificationFor: core::hash::Hash;

    /// Feeds `self` into the hasher. No precondition: the impls of `std` and derived impls
    /// call the `Hasher`'s `write*` methods on the fields, which do not panic for `std`'s
    /// hashers. Nothing is said about the hasher's resulting state (see `hash.rs` for the
    /// model of `DefaultHasher`).
    fn hash<H: core::hash::Hasher>(&self, state: &mut H);
}

#[verifier::external_trait_specification]
pub trait ExPtrPointee: PointeeSized {
    type ExternalTraitSpecificationFor: core::ptr::Pointee;

    type Metadata:
        Copy + Send + Sync + Ord + core::hash::Hash + Unpin + core::fmt::Debug + Sized + core::marker::Freeze;
}

#[verifier::external_trait_specification]
pub trait ExBorrow<Borrowed> where Borrowed: ?Sized {
    type ExternalTraitSpecificationFor: core::borrow::Borrow<Borrowed>;
}

#[verifier::external_trait_specification]
pub trait ExStructural {
    type ExternalTraitSpecificationFor: Structural;
}

/// `AsRef`: `spec_as_ref` is the value `as_ref` returns, for impls that specify it
/// (`obeys_as_ref_spec()`); a call through a bound on an unspecified impl has an unknown
/// result, as for `Deref`. `AsMut` is accepted generically; `[T; N]` and `[T]` are specified.
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(AsRefSpec via AsRefSpecImpl)]
pub trait ExAsRef<T: PointeeSized>: PointeeSized {
    type ExternalTraitSpecificationFor: core::convert::AsRef<T>;

    spec fn obeys_as_ref_spec() -> bool;

    spec fn spec_as_ref(&self) -> &T;

    fn as_ref(&self) -> (r: &T)
        ensures
            Self::obeys_as_ref_spec() ==> r == self.spec_as_ref(),
    ;
}

#[verifier::external_trait_specification]
pub trait ExAsMut<T: PointeeSized>: PointeeSized {
    type ExternalTraitSpecificationFor: core::convert::AsMut<T>;

    fn as_mut(&mut self) -> &mut T;
}

impl<T, const N: usize> AsRefSpecImpl<[T]> for [T; N] {
    open spec fn obeys_as_ref_spec() -> bool {
        true
    }

    open spec fn spec_as_ref(&self) -> &[T] {
        super::super::array::spec_array_as_slice(self)
    }
}

impl<T> AsRefSpecImpl<[T]> for [T] {
    open spec fn obeys_as_ref_spec() -> bool {
        true
    }

    open spec fn spec_as_ref(&self) -> &[T] {
        self
    }
}

// core's blanket impls `AsRef<U> for &T` and `AsRef<U> for &mut T` forward to `T`
impl<'a, T: ?Sized + core::convert::AsRef<U>, U: ?Sized> AsRefSpecImpl<U> for &'a T {
    open spec fn obeys_as_ref_spec() -> bool {
        <T as AsRefSpec<U>>::obeys_as_ref_spec()
    }

    open spec fn spec_as_ref(&self) -> &U {
        <T as AsRefSpec<U>>::spec_as_ref(*self)
    }
}

impl<'a, T: ?Sized + core::convert::AsRef<U>, U: ?Sized> AsRefSpecImpl<U> for &'a mut T {
    open spec fn obeys_as_ref_spec() -> bool {
        <T as AsRefSpec<U>>::obeys_as_ref_spec()
    }

    open spec fn spec_as_ref(&self) -> &U {
        <T as AsRefSpec<U>>::spec_as_ref(&**self)
    }
}

pub assume_specification<T, const N: usize>[ <[T; N] as core::convert::AsMut<[T]>>::as_mut ](
    a: &mut [T; N],
) -> (r: &mut [T])
    ensures
        r@ == old(a)@,
        final(r)@ == final(a)@,
;

pub assume_specification<T>[ <[T] as core::convert::AsMut<[T]>>::as_mut ](s: &mut [T]) -> (r: &mut [T])
    ensures
        r@ == old(s)@,
        final(r)@ == final(s)@,
;

// Since this trait involves the unstable library feature `const_destruct`,
// we only enable it when verifying core
#[cfg(verus_verify_core)]
#[verifier::external_trait_specification]
trait ExDestruct: PointeeSized {
    type ExternalTraitSpecificationFor: core::marker::Destruct;
}

#[verifier::external_trait_specification]
pub trait ExMetaSized {
    type ExternalTraitSpecificationFor: core::marker::MetaSized;
}

/// `char::from_u32(i)` is `Some` exactly for Unicode scalar values (not a surrogate, at most
/// U+10FFFF).
pub assume_specification[ char::from_u32 ](i: u32) -> (c: Option<char>)
    ensures
        c is Some <==> (i <= 0xD7FF || (0xE000 <= i && i <= 0x10FFFF)),
        c is Some ==> c.unwrap() as u32 == i,
;

// `core::error::Error`: declared so it can be used in bounds and as `dyn Error`.
// `source` returns `dyn Error`, so its signature depends on the trait itself; the
// `impls_cannot_extend_spec` mode drops the trait --> method edge (sound for exec methods
// whose impls cannot add ensures), which removes the cycle. `source` has no specification;
// `description` and `cause` (deprecated) are not declared.
#[verifier::external_trait_specification]
pub trait ExError: core::fmt::Debug + core::fmt::Display {
    type ExternalTraitSpecificationFor: core::error::Error;

    #[verifier::impls_cannot_extend_spec]
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)>;
}

pub assume_specification<T>[ bool::then_some::<T> ](b: bool, t: T) -> (r: Option<T>)
    ensures
        r == if b { Some(t) } else { None },
;

pub assume_specification<T>[ core::mem::swap::<T> ](a: &mut T, b: &mut T)
    ensures
        *final(a) == *old(b),
        *final(b) == *old(a),
    opens_invariants none
    no_unwind
;

pub assume_specification<T>[ core::mem::replace::<T> ](dest: &mut T, src: T) -> (res: T)
    ensures
        res == *old(dest),
        *final(dest) == src,
    opens_invariants none
    no_unwind
;

pub assume_specification<T: core::default::Default>[ core::mem::take::<T> ](dest: &mut T) -> (res: T)
    ensures
        res == *old(dest),
        T::default.ensures((), *final(dest)),
;

pub assume_specification<T>[ core::mem::drop::<T> ](x: T)
;

pub assume_specification<T>[ core::mem::forget::<T> ](t: T)
    opens_invariants none
    no_unwind
;

#[verifier::external_type_specification]
pub struct ExOrdering(core::cmp::Ordering);

#[verifier::external_type_specification]
#[verifier::accept_recursive_types(V)]
#[verifier::ext_equal]
pub struct ExOption<V>(core::option::Option<V>);

#[verifier::external_type_specification]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types_in_ground_variants(E)]
pub struct ExResult<T, E>(core::result::Result<T, E>);

// I don't really expect this to be particularly useful;
// this is mostly here because I wanted an easy way to test
// the combination of external_type_specification & external_body
// in a cross-crate context.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDuration(core::time::Duration);

#[verifier::external_type_specification]
#[verifier::accept_recursive_types(V)]
pub struct ExPhantomData<V: PointeeSized>(core::marker::PhantomData<V>);

pub assume_specification[ core::intrinsics::likely ](b: bool) -> (c: bool)
    ensures
        c == b,
;

pub assume_specification[ core::intrinsics::unlikely ](b: bool) -> (c: bool)
    ensures
        c == b,
;

pub assume_specification<T, F: FnOnce() -> T>[ bool::then ](b: bool, f: F) -> (ret: Option<T>)
    requires
        b ==> f.requires(()),
    ensures
        if b {
            ret.is_some() && f.ensures((), ret.unwrap())
        } else {
            ret.is_none()
        },
;

pub assume_specification<T> [core::hint::must_use] (value: T) -> (ret: T)
    ensures
        ret == value,
;

pub assume_specification [core::panicking::panic] (s: &'static str) -> !
    requires
        false,
;

pub assume_specification [core::panicking::panic_fmt] (s: core::fmt::Arguments<'_>) -> !
    requires
        false,
;

/// `panic!` with a single non-literal-format argument in editions before 2021 (and
/// `std::panic!(msg)`) calls `std::rt::begin_panic(msg)`; like `panic!`, it must be
/// unreachable in verified code.
#[cfg(feature = "std")]
pub assume_specification<M: core::any::Any + Send>[ std::rt::begin_panic::<M> ](msg: M) -> !
    requires
        false,
;

/// The failure path of `assert_eq!` / `assert_ne!` / `assert_matches!`: like `panic!`, it
/// must be unreachable in verified code. This makes those macros usable as assertions on
/// exec values (the comparison itself is `PartialEq::eq` on references, so it is only as
/// informative as the type's `obeys_eq_spec`).
pub assume_specification<T: core::fmt::Debug + ?Sized, U: core::fmt::Debug + ?Sized>[
    core::panicking::assert_failed::<T, U>
](
    kind: core::panicking::AssertKind,
    left: &T,
    right: &U,
    args: Option<core::fmt::Arguments<'_>>,
) -> !
    requires
        false,
;

} // verus!

#[verifier::external_type_specification]
pub struct ExAssertKind(core::panicking::AssertKind);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExAssertParamIsClone<T: Clone + PointeeSized>(core::clone::AssertParamIsClone<T>);
