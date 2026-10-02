#![allow(unused_imports)]
use super::super::prelude::*;

use core::option::Option;

use core::result::Result;

verus! {

////// Add is_variant-style spec functions
pub trait ResultAdditionalSpecFns<T, E> {
    #[cfg_attr(not(verus_verify_core), deprecated = "is_Variant is deprecated - use `->` or `matches` instead: https://verus-lang.github.io/verus/guide/datatypes_enum.html")]
    #[allow(non_snake_case)]
    spec fn is_Ok(&self) -> bool;

    #[cfg_attr(not(verus_verify_core), deprecated = "get_Variant is deprecated - use `->` or `matches` instead: https://verus-lang.github.io/verus/guide/datatypes_enum.html")]
    #[allow(non_snake_case)]
    spec fn get_Ok_0(&self) -> T;

    #[allow(non_snake_case)]
    spec fn arrow_Ok_0(&self) -> T;

    #[cfg_attr(not(verus_verify_core), deprecated = "is_Variant is deprecated - use `->` or `matches` instead: https://verus-lang.github.io/verus/guide/datatypes_enum.html")]
    #[allow(non_snake_case)]
    spec fn is_Err(&self) -> bool;

    #[cfg_attr(not(verus_verify_core), deprecated = "get_Variant is deprecated - use `->` or `matches` instead: https://verus-lang.github.io/verus/guide/datatypes_enum.html")]
    #[allow(non_snake_case)]
    spec fn get_Err_0(&self) -> E;

    #[allow(non_snake_case)]
    spec fn arrow_Err_0(&self) -> E;

    #[allow(deprecated)]
    proof fn tracked_unwrap(tracked self) -> (tracked t: T)
        requires
            self.is_Ok(),
        ensures
            t == self->Ok_0,
    ;

    #[allow(deprecated)]
    proof fn tracked_unwrap_err(tracked self) -> (tracked t: E)
        requires
            self.is_Err(),
        ensures
            t == self->Err_0,
    ;

    #[allow(deprecated)]
    proof fn tracked_expect(tracked self, msg: &str) -> (tracked t: T)
        requires
            self.is_Ok(),
        ensures
            t == self->Ok_0,
    ;

    #[allow(deprecated)]
    proof fn tracked_expect_err(tracked self, msg: &str) -> (tracked t: E)
        requires
            self.is_Err(),
        ensures
            t == self->Err_0,
    ;
}

impl<T, E> ResultAdditionalSpecFns<T, E> for Result<T, E> {
    #[verifier::inline]
    open spec fn is_Ok(&self) -> bool {
        is_variant(self, "Ok")
    }

    #[verifier::inline]
    open spec fn get_Ok_0(&self) -> T {
        get_variant_field(self, "Ok", "0")
    }

    #[verifier::inline]
    open spec fn arrow_Ok_0(&self) -> T {
        get_variant_field(self, "Ok", "0")
    }

    #[verifier::inline]
    open spec fn is_Err(&self) -> bool {
        is_variant(self, "Err")
    }

    #[verifier::inline]
    open spec fn get_Err_0(&self) -> E {
        get_variant_field(self, "Err", "0")
    }

    #[verifier::inline]
    open spec fn arrow_Err_0(&self) -> E {
        get_variant_field(self, "Err", "0")
    }

    proof fn tracked_unwrap(tracked self) -> (tracked t: T) {
        match self {
            Result::Ok(t) => t,
            Result::Err(_) => proof_from_false(),
        }
    }

    proof fn tracked_unwrap_err(tracked self) -> (tracked t: E) {
        match self {
            Result::Ok(_) => proof_from_false(),
            Result::Err(e) => e,
        }
    }

    proof fn tracked_expect(tracked self, msg: &str) -> (tracked t: T) {
        match self {
            Result::Ok(t) => t,
            Result::Err(_) => proof_from_false(),
        }
    }

    proof fn tracked_expect_err(tracked self, msg: &str) -> (tracked t: E) {
        match self {
            Result::Ok(_) => proof_from_false(),
            Result::Err(e) => e,
        }
    }
}

////// Specs for std methods
// is_ok
#[verifier::inline]
pub open spec fn is_ok<T, E>(result: &Result<T, E>) -> bool {
    is_variant(result, "Ok")
}

#[verifier::when_used_as_spec(is_ok)]
pub assume_specification<T, E>[ Result::<T, E>::is_ok ](r: &Result<T, E>) -> (b: bool)
    ensures
        b == is_ok(r),
    no_unwind
;

// is_err
#[verifier::inline]
pub open spec fn is_err<T, E>(result: &Result<T, E>) -> bool {
    is_variant(result, "Err")
}

#[verifier::when_used_as_spec(is_err)]
pub assume_specification<T, E>[ Result::<T, E>::is_err ](r: &Result<T, E>) -> (b: bool)
    ensures
        b == is_err(r),
    no_unwind
;

// as_ref
pub assume_specification<T, E>[ Result::<T, E>::as_ref ](result: &Result<T, E>) -> (r: Result<
    &T,
    &E,
>)
    ensures
        r is Ok <==> result is Ok,
        r is Ok ==> result->Ok_0 == r->Ok_0,
        r is Err <==> result is Err,
        r is Err ==> result->Err_0 == r->Err_0,
    no_unwind
;

// unwrap
#[verifier::inline]
pub open spec fn spec_unwrap<T, E: core::fmt::Debug>(result: Result<T, E>) -> T
    recommends
        result is Ok,
{
    result->Ok_0
}

#[verifier::when_used_as_spec(spec_unwrap)]
pub assume_specification<T, E: core::fmt::Debug>[ Result::<T, E>::unwrap ](
    result: Result<T, E>,
) -> (t: T)
    requires
        result is Ok,
    ensures
        t == result->Ok_0,
;

// unwrap_err
#[verifier::inline]
pub open spec fn spec_unwrap_err<T: core::fmt::Debug, E>(result: Result<T, E>) -> E
    recommends
        result is Err,
{
    result->Err_0
}

#[verifier::when_used_as_spec(spec_unwrap_err)]
pub assume_specification<T: core::fmt::Debug, E>[ Result::<T, E>::unwrap_err ](
    result: Result<T, E>,
) -> (e: E)
    requires
        result is Err,
    ensures
        e == result->Err_0,
;

// expect
#[verifier::inline]
pub open spec fn spec_expect<T, E: core::fmt::Debug>(result: Result<T, E>, msg: &str) -> T
    recommends
        result is Ok,
{
    result->Ok_0
}

#[verifier::when_used_as_spec(spec_expect)]
pub assume_specification<T, E: core::fmt::Debug>[ Result::<T, E>::expect ](
    result: Result<T, E>,
    msg: &str,
) -> (t: T)
    requires
        result is Ok,
    ensures
        t == result->Ok_0,
;

// map
pub assume_specification<T, E, U, F: FnOnce(T) -> U>[ Result::<T, E>::map ](
    result: Result<T, E>,
    op: F,
) -> (mapped_result: Result<U, E>)
    requires
        result.is_ok() ==> op.requires((result->Ok_0,)),
    ensures
        result.is_ok() ==> mapped_result.is_ok() && op.ensures(
            (result->Ok_0,),
            mapped_result->Ok_0,
        ),
        result.is_err() ==> mapped_result == Result::<U, E>::Err(result->Err_0),
;

// map_err
#[verusfmt::skip]
pub assume_specification<T, E, F, O: FnOnce(E) -> F>[Result::<T, E>::map_err](result: Result<T, E>, op: O) -> (mapped_result: Result<T, F>)
    requires
        result.is_err() ==> op.requires((result->Err_0,)),
    ensures
        result.is_err() ==> mapped_result.is_err() && op.ensures(
            (result->Err_0,),
            mapped_result->Err_0,
        ),
        result.is_ok() ==> mapped_result == Result::<T, F>::Ok(result->Ok_0);

// ok
#[verifier::inline]
pub open spec fn ok<T, E>(result: Result<T, E>) -> Option<T> {
    match result {
        Ok(t) => Some(t),
        Err(_) => None,
    }
}

#[verifier::when_used_as_spec(ok)]
pub assume_specification<T, E>[ Result::<T, E>::ok ](result: Result<T, E>) -> (opt: Option<T>)
    ensures
        opt == ok(result),
    no_unwind
;

// err
#[verifier::inline]
pub open spec fn err<T, E>(result: Result<T, E>) -> Option<E> {
    match result {
        Ok(_) => None,
        Err(e) => Some(e),
    }
}

#[verifier::when_used_as_spec(err)]
pub assume_specification<T, E>[ Result::<T, E>::err ](result: Result<T, E>) -> (opt: Option<E>)
    ensures
        opt == err(result),
    no_unwind
;


pub assume_specification<T, E, U, F: FnOnce(T) -> Result<U, E>>[ Result::<T, E>::and_then ](
    result: Result<T, E>,
    op: F,
) -> (res: Result<U, E>)
    requires
        result.is_ok() ==> op.requires((result->Ok_0,)),
    ensures
        result.is_err() ==> res == Err::<U, E>(result->Err_0),
        result.is_ok() ==> op.ensures((result->Ok_0,), res),
;

pub assume_specification<T, E, F, O: FnOnce(E) -> Result<T, F>>[ Result::<T, E>::or_else ](
    result: Result<T, E>,
    op: O,
) -> (res: Result<T, F>)
    requires
        result.is_err() ==> op.requires((result->Err_0,)),
    ensures
        result.is_ok() ==> res == Ok::<T, F>(result->Ok_0),
        result.is_err() ==> op.ensures((result->Err_0,), res),
;

pub assume_specification<T, E>[ Result::<T, E>::unwrap_or ](result: Result<T, E>, default: T) -> (res: T)
    ensures
        result.is_ok() ==> res == result->Ok_0,
        result.is_err() ==> res == default,
;

pub assume_specification<T, E, F: FnOnce(E) -> T>[ Result::<T, E>::unwrap_or_else ](
    result: Result<T, E>,
    op: F,
) -> (res: T)
    requires
        result.is_err() ==> op.requires((result->Err_0,)),
    ensures
        result.is_ok() ==> res == result->Ok_0,
        result.is_err() ==> op.ensures((result->Err_0,), res),
;

pub assume_specification<T: core::default::Default, E>[ Result::<T, E>::unwrap_or_default ](
    result: Result<T, E>,
) -> (res: T)
    ensures
        result.is_ok() ==> res == result->Ok_0,
        result.is_err() ==> T::default.ensures((), res),
;

pub assume_specification<T, E, U, F: FnOnce(T) -> U>[ Result::<T, E>::map_or ](
    result: Result<T, E>,
    default: U,
    f: F,
) -> (res: U)
    requires
        result.is_ok() ==> f.requires((result->Ok_0,)),
    ensures
        result.is_err() ==> res == default,
        result.is_ok() ==> f.ensures((result->Ok_0,), res),
;

pub assume_specification<T, E>[ Result::<T, E>::unwrap_unchecked ](result: Result<T, E>) -> (res: T)
    requires
        result.is_ok(),
    ensures
        res == result->Ok_0,
;

pub assume_specification<T, E, U>[ Result::<T, E>::and::<U> ](r: Result<T, E>, res: Result<U, E>) -> (out: Result<U, E>)
    ensures
        out == match r {
            Ok(_) => res,
            Err(e) => Err(e),
        },
;

} // verus!
