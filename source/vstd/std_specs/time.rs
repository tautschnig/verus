//! `core::time::Duration`, modelled by its length in nanoseconds.
use super::super::prelude::*;
use core::time::Duration;

verus! {

/// The length of `d` in nanoseconds: `secs * 10^9 + subsec_nanos`.
pub uninterp spec fn duration_nanos(d: Duration) -> nat;

pub open spec fn duration_max_nanos() -> nat {
    (u64::MAX as nat) * 1_000_000_000 + 999_999_999
}

/// A `Duration` is `secs: u64` plus `nanos < 10^9`, so its length is at most `duration_max_nanos`.
pub broadcast axiom fn axiom_duration_nanos_bound(d: Duration)
    ensures
        #[trigger] duration_nanos(d) <= duration_max_nanos(),
;

pub assume_specification[ Duration::from_secs ](secs: u64) -> (r: Duration)
    ensures
        duration_nanos(r) == secs as nat * 1_000_000_000,
;

pub assume_specification[ Duration::from_millis ](millis: u64) -> (r: Duration)
    ensures
        duration_nanos(r) == millis as nat * 1_000_000,
;

pub assume_specification[ Duration::as_secs ](d: &Duration) -> (r: u64)
    ensures
        r as nat == duration_nanos(*d) / 1_000_000_000,
;

pub assume_specification[ Duration::as_millis ](d: &Duration) -> (r: u128)
    ensures
        r as nat == duration_nanos(*d) / 1_000_000,
;

pub assume_specification[ Duration::as_nanos ](d: &Duration) -> (r: u128)
    ensures
        r as nat == duration_nanos(*d),
;

pub assume_specification[ Duration::is_zero ](d: &Duration) -> (r: bool)
    ensures
        r == (duration_nanos(*d) == 0),
;

pub assume_specification[ Duration::saturating_add ](a: Duration, b: Duration) -> (r: Duration)
    ensures
        duration_nanos(r) == if duration_nanos(a) + duration_nanos(b) <= duration_max_nanos() {
            duration_nanos(a) + duration_nanos(b)
        } else {
            duration_max_nanos()
        },
;

pub assume_specification[ Duration::ZERO ] -> (r: Duration)
    ensures
        duration_nanos(r) == 0,
;

pub assume_specification[ Duration::saturating_sub ](a: Duration, b: Duration) -> (r: Duration)
    ensures
        duration_nanos(r) == if duration_nanos(a) >= duration_nanos(b) {
            (duration_nanos(a) - duration_nanos(b)) as nat
        } else {
            0
        },
;

/// The nanosecond part.
pub assume_specification[ Duration::subsec_nanos ](d: &Duration) -> (r: u32)
    ensures
        r as nat == duration_nanos(*d) % 1_000_000_000,
;

/// The largest duration.
pub assume_specification[ Duration::MAX ] -> (r: Duration)
    ensures
        duration_nanos(r) == duration_max_nanos(),
;

pub assume_specification[ Duration::saturating_mul ](d: Duration, n: u32) -> (r: Duration)
    ensures
        duration_nanos(r) == if duration_nanos(d) * (n as nat) <= duration_max_nanos() {
            duration_nanos(d) * (n as nat)
        } else {
            duration_max_nanos()
        },
;

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExTryFromFloatSecsError(core::time::TryFromFloatSecsError);

/// Float conversion: content-free, like float arithmetic.
pub assume_specification[ Duration::as_secs_f64 ](d: &Duration) -> f64;

pub broadcast group group_time_axioms {
    axiom_duration_nanos_bound,
}

} // verus!
