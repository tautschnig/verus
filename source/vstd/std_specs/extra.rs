//! Further `core`/`alloc`/`std` specifications (kraken-cli ingestion, S26).
//! Content-carrying ones have Kani harnesses in `tools/vstd-kani` (`extra_specs_hold`,
//! `slice_sort_specs_hold`) and Lean statements (verus-work `Internal/StdSpecs.lean`).
#![allow(unused_imports)]
use super::super::prelude::*;
use super::super::arithmetic::power::pow;
use super::cmp::{OrdSpec, PartialEqSpec};
use core::cmp::Ordering;

verus! {

// ------------------------------------------------------------------ Option

pub assume_specification<T>[ Option::<Option<T>>::flatten ](o: Option<Option<T>>) -> (r: Option<T>)
    ensures
        r == match o { Some(Some(x)) => Some(x), _ => None },
;

pub assume_specification<T, U>[ Option::<T>::zip::<U> ](a: Option<T>, b: Option<U>) -> (r: Option<(T, U)>)
    ensures
        r == match (a, b) { (Some(x), Some(y)) => Some((x, y)), _ => None },
;

// ------------------------------------------------------------------ arrays

/// `f` is called on every element, in order.
pub assume_specification<T, const N: usize, F: FnMut(T) -> U, U>[ <[T; N]>::map::<F, U> ](a: [T; N], f: F) -> (r: [U; N])
    requires
        forall |i: int| 0 <= i < N ==> #[trigger] call_requires(f, (a@[i],)),
    ensures
        forall |i: int| 0 <= i < N ==> call_ensures(f, (a@[i],), #[trigger] r@[i]),
;

// ------------------------------------------------------------------ integers

macro_rules! pow_specs {
    ($($t:ty),*) => {
        $crate::vstd::prelude::verus! {
            $(
            /// `pow` panics on overflow with overflow checks and wraps without them; the
            /// precondition excludes both (Kani: `pow_in_range_exact`).
            pub assume_specification[ <$t>::pow ](x: $t, exp: u32) -> (r: $t)
                requires
                    <$t>::MIN <= pow(x as int, exp as nat) <= <$t>::MAX,
                ensures
                    r as int == pow(x as int, exp as nat),
            ;
            )*
        }
    };
}

pow_specs!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

pub assume_specification[ u8::is_ascii_hexdigit ](c: &u8) -> (r: bool)
    ensures
        r == ((0x30 <= *c <= 0x39) || (0x41 <= *c <= 0x46) || (0x61 <= *c <= 0x66)),
;

// ------------------------------------------------------------------ slices: sorting

/// Sorting permutes the slice; with a lawful `Ord`, the result is sorted by `cmp_spec`.
pub open spec fn sorted_by_cmp<T: Ord>(s: Seq<T>) -> bool {
    forall |i: int, j: int| #![trigger s[i], s[j]] 0 <= i < j < s.len() ==>
        OrdSpec::cmp_spec(&s[i], &s[j]) != Ordering::Greater
}

pub assume_specification<T: Ord>[ <[T]>::sort ](s: &mut [T])
    ensures
        final(s)@.len() == old(s)@.len(),
        final(s)@.to_multiset() == old(s)@.to_multiset(),
        <T as OrdSpec>::obeys_cmp_spec() ==> sorted_by_cmp(final(s)@),
;

pub assume_specification<T: Ord>[ <[T]>::sort_unstable ](s: &mut [T])
    ensures
        final(s)@.len() == old(s)@.len(),
        final(s)@.to_multiset() == old(s)@.to_multiset(),
        <T as OrdSpec>::obeys_cmp_spec() ==> sorted_by_cmp(final(s)@),
;

/// The comparator may be called on any two elements.
pub assume_specification<T, F: FnMut(&T, &T) -> Ordering>[ <[T]>::sort_by::<F> ](s: &mut [T], compare: F)
    requires
        forall |i: int, j: int| 0 <= i < old(s)@.len() && 0 <= j < old(s)@.len() ==>
            call_requires(compare, (#[trigger] &old(s)@[i], #[trigger] &old(s)@[j])),
    ensures
        final(s)@.len() == old(s)@.len(),
        final(s)@.to_multiset() == old(s)@.to_multiset(),
;

pub assume_specification<T, F: FnMut(&T, &T) -> Ordering>[ <[T]>::sort_unstable_by::<F> ](s: &mut [T], compare: F)
    requires
        forall |i: int, j: int| 0 <= i < old(s)@.len() && 0 <= j < old(s)@.len() ==>
            call_requires(compare, (#[trigger] &old(s)@[i], #[trigger] &old(s)@[j])),
    ensures
        final(s)@.len() == old(s)@.len(),
        final(s)@.to_multiset() == old(s)@.to_multiset(),
;

pub assume_specification<T, K: Ord, F: FnMut(&T) -> K>[ <[T]>::sort_by_key::<K, F> ](s: &mut [T], f: F)
    requires
        forall |i: int| 0 <= i < old(s)@.len() ==> call_requires(f, (#[trigger] &old(s)@[i],)),
    ensures
        final(s)@.len() == old(s)@.len(),
        final(s)@.to_multiset() == old(s)@.to_multiset(),
;

pub assume_specification<T, K: Ord, F: FnMut(&T) -> K>[ <[T]>::sort_unstable_by_key::<K, F> ](s: &mut [T], f: F)
    requires
        forall |i: int| 0 <= i < old(s)@.len() ==> call_requires(f, (#[trigger] &old(s)@[i],)),
    ensures
        final(s)@.len() == old(s)@.len(),
        final(s)@.to_multiset() == old(s)@.to_multiset(),
;

/// `Ok(i)`: an element equal to `x`; `Err(i)`: an insertion point (meaningful when sorted).
pub assume_specification<T: Ord>[ <[T]>::binary_search ](s: &[T], x: &T) -> (r: Result<usize, usize>)
    ensures
        match r {
            Ok(i) => i < s@.len() && (<T as OrdSpec>::obeys_cmp_spec() ==> OrdSpec::cmp_spec(&s@[i as int], x) == Ordering::Equal),
            Err(i) => i <= s@.len(),
        },
;

// ------------------------------------------------------------------ slices: join

/// `[S]::join(sep)` (`Vec<String>`/`[&str]` with a `&str` separator in kraken-cli): content-free.
#[verifier::external_trait_specification]
pub trait ExJoin<Separator> {
    type ExternalTraitSpecificationFor: alloc::slice::Join<Separator>;

    type Output;
}

pub assume_specification<T, Separator>[ <[T]>::join::<Separator> ](s: &[T], sep: Separator) -> <[T] as alloc::slice::Join<Separator>>::Output
    where [T]: alloc::slice::Join<Separator>;

// ------------------------------------------------------------------ VecDeque

pub assume_specification<T, A: core::alloc::Allocator>[ alloc::collections::VecDeque::<T, A>::front ](d: &alloc::collections::VecDeque<T, A>) -> (r: Option<&T>)
    ensures
        r == if d@.len() > 0 { Some(&d@[0]) } else { None },
;

pub assume_specification<T, A: core::alloc::Allocator>[ alloc::collections::VecDeque::<T, A>::front_mut ](d: &mut alloc::collections::VecDeque<T, A>) -> (r: Option<&mut T>)
    ensures
        if old(d)@.len() > 0 {
            r is Some && *r.unwrap() == old(d)@[0] && final(d)@ == old(d)@.update(0, *final(r.unwrap()))
        } else {
            r is None && final(d)@ == old(d)@
        },
;

// ------------------------------------------------------------------ str and String

/// The UTF-8 encoding of the characters (as `str::len` and `str::as_bytes`).
pub assume_specification[ alloc::string::String::len ](s: &alloc::string::String) -> (r: usize)
    ensures
        r == super::super::utf8::encode_utf8(s@).len(),
;

pub assume_specification<'a>[ alloc::string::String::as_bytes ](s: &'a alloc::string::String) -> (r: &'a [u8])
    ensures
        r@ == super::super::utf8::encode_utf8(s@),
;

/// Searches and trimming with arbitrary patterns: content-free.
pub assume_specification<'a, P: core::str::pattern::Pattern>[ str::split_once::<P> ](s: &'a str, pat: P) -> Option<(&'a str, &'a str)>;

pub assume_specification<'a, P: core::str::pattern::Pattern>[ str::trim_start_matches::<P> ](s: &'a str, pat: P) -> &'a str;

pub assume_specification<'a, P: core::str::pattern::Pattern>[ str::replace::<P> ](s: &'a str, from: P, to: &str) -> alloc::string::String;


#[verifier::external_trait_specification]
pub trait ExToString {
    type ExternalTraitSpecificationFor: alloc::string::ToString;

    fn to_string(&self) -> alloc::string::String;
}


// ------------------------------------------------------------------ iterators

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExOnce<T>(core::iter::Once<T>);

/// The element of an `iter::once`, fixed at construction.
pub uninterp spec fn once_elts<T>(i: core::iter::Once<T>) -> Seq<T>;

impl<T> super::iter::IteratorSpecImpl for core::iter::Once<T> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    uninterp spec fn remaining(&self) -> Seq<Self::Item>;

    uninterp spec fn will_return_none(&self) -> bool;

    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < once_elts(*self).len() {
            Some(once_elts(*self)[index])
        } else {
            None
        }
    }
}

pub assume_specification<T>[ core::iter::once::<T> ](v: T) -> (iter: core::iter::Once<T>)
    ensures
        super::iter::IteratorSpec::remaining(&iter) == seq![v],
        once_elts(iter) == super::iter::IteratorSpec::remaining(&iter),
        super::iter::IteratorSpec::decrease(&iter) is Some,
;

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExBTreeSetIntoIter<T, A: core::alloc::Allocator + Clone>(alloc::collections::btree_set::IntoIter<T, A>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExPending<T>(core::future::Pending<T>);

pub assume_specification<T>[ core::future::pending::<T> ]() -> core::future::Pending<T>;

// ------------------------------------------------------------------ S27

/// `String::from(&str)` copies the characters.
pub assume_specification<'a, 'b>[ <alloc::string::String as From<&'a str>>::from ](s: &'b str) -> (r: alloc::string::String)
    ensures
        r@ == s@,
;

/// `slice::from_ref(x)` is the one-element slice `[*x]`.
pub assume_specification<T>[ core::slice::from_ref::<T> ](x: &T) -> (r: &[T])
    ensures
        r@ == seq![*x],
;

/// `RangeInclusive::start` is the start bound.
pub assume_specification<Idx>[ core::ops::RangeInclusive::<Idx>::start ](r: &core::ops::RangeInclusive<Idx>) -> (s: &Idx);

/// `Vec::dedup` removes consecutive duplicates: the length does not grow (contents not
/// modelled).
pub assume_specification<T: PartialEq, A: core::alloc::Allocator>[ alloc::vec::Vec::<T, A>::dedup ](v: &mut alloc::vec::Vec<T, A>)
    ensures
        final(v)@.len() <= old(v)@.len(),
        old(v)@.len() > 0 ==> final(v)@.len() > 0,
;

/// `cmp::Reverse` is a transparent newtype.
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(T)]
pub struct ExReverse<T>(core::cmp::Reverse<T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExOptionIntoIter<T>(core::option::IntoIter<T>);

impl<A> super::iter::IteratorSpecImpl for core::option::IntoIter<A> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool { false }
    uninterp spec fn remaining(&self) -> Seq<A>;
    uninterp spec fn will_return_none(&self) -> bool;
    uninterp spec fn decrease(&self) -> Option<nat>;
    open spec fn peek(&self, index: int) -> Option<A> { None }
}

/// Float to `Duration`: content-free, like float arithmetic.
pub assume_specification[ core::time::Duration::try_from_secs_f64 ](secs: f64) -> Result<core::time::Duration, core::time::TryFromFloatSecsError>;

// ------------------------------------------------------------------ str::Pattern (W7)

#[verifier::external_trait_specification]
pub trait ExPattern: Sized {
    type ExternalTraitSpecificationFor: core::str::pattern::Pattern;

    type Searcher<'a>: core::str::pattern::Searcher<'a>;
}

#[verifier::external_trait_specification]
pub trait ExSearcher<'a> {
    type ExternalTraitSpecificationFor: core::str::pattern::Searcher<'a>;
}

#[verifier::external_trait_specification]
pub trait ExReverseSearcher<'a>: core::str::pattern::Searcher<'a> {
    type ExternalTraitSpecificationFor: core::str::pattern::ReverseSearcher<'a>;
}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExStrSearcher<'a, 'b>(core::str::pattern::StrSearcher<'a, 'b>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCharSearcher<'a>(core::str::pattern::CharSearcher<'a>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCharSliceSearcher<'a, 'b>(core::str::pattern::CharSliceSearcher<'a, 'b>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCharArraySearcher<'a, const N: usize>(core::str::pattern::CharArraySearcher<'a, N>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCharArrayRefSearcher<'a, 'b, const N: usize>(core::str::pattern::CharArrayRefSearcher<'a, 'b, N>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(F)]
pub struct ExCharPredicateSearcher<'a, F: FnMut(char) -> bool>(core::str::pattern::CharPredicateSearcher<'a, F>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(P)]
pub struct ExSplit<'a, P: core::str::pattern::Pattern>(core::str::Split<'a, P>);

pub assume_specification<'a, P: core::str::pattern::Pattern>[ str::split::<P> ](s: &'a str, pat: P) -> core::str::Split<'a, P>;

/// `Split` and `SplitWhitespace` do not obey the prophetic laws here (their items are not
/// modelled).
impl<'a, P: core::str::pattern::Pattern> super::iter::IteratorSpecImpl for core::str::Split<'a, P> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool { false }
    uninterp spec fn remaining(&self) -> Seq<&'a str>;
    uninterp spec fn will_return_none(&self) -> bool;
    uninterp spec fn decrease(&self) -> Option<nat>;
    open spec fn peek(&self, index: int) -> Option<&'a str> { None }
}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExSplitWhitespace<'a>(core::str::SplitWhitespace<'a>);

impl<'a> super::iter::IteratorSpecImpl for core::str::SplitWhitespace<'a> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool { false }
    uninterp spec fn remaining(&self) -> Seq<&'a str>;
    uninterp spec fn will_return_none(&self) -> bool;
    uninterp spec fn decrease(&self) -> Option<nat>;
    open spec fn peek(&self, index: int) -> Option<&'a str> { None }
}

pub assume_specification<'a>[ str::split_whitespace ](s: &'a str) -> core::str::SplitWhitespace<'a>;

/// Searches from the end: content-free.
pub assume_specification<'a, P: core::str::pattern::Pattern>[ str::rfind::<P> ](s: &'a str, pat: P) -> Option<usize>
    where for<'b> P::Searcher<'b>: core::str::pattern::ReverseSearcher<'b>;

pub assume_specification<'a, P: core::str::pattern::Pattern>[ str::trim_end_matches::<P> ](s: &'a str, pat: P) -> &'a str
    where for<'b> P::Searcher<'b>: core::str::pattern::ReverseSearcher<'b>;

pub assume_specification<'a, P: core::str::pattern::Pattern>[ str::ends_with::<P> ](s: &'a str, pat: P) -> bool
    where for<'b> P::Searcher<'b>: core::str::pattern::ReverseSearcher<'b>;

} // verus!
