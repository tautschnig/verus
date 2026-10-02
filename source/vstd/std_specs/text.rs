//! Case conversion and related string functions: content-free (nothing is said about the
//! resulting string), except where stated.
use super::super::prelude::*;
use alloc::string::String;

verus! {

pub assume_specification[ str::to_uppercase ](s: &str) -> String;

pub assume_specification[ str::to_lowercase ](s: &str) -> String;

pub assume_specification[ str::to_ascii_uppercase ](s: &str) -> String;

pub assume_specification[ str::to_ascii_lowercase ](s: &str) -> String;

pub assume_specification[ str::eq_ignore_ascii_case ](s: &str, other: &str) -> bool;

pub assume_specification[ str::trim ](s: &str) -> &str;

pub assume_specification[ String::with_capacity ](n: usize) -> (r: String)
    ensures
        r@ == Seq::<char>::empty(),
;

} // verus!
