//! Kani falsification harnesses for Verus `vstd` `assume_specification` contracts.
//!
//! Each harness re-implements the *executable projection* of a vstd spec
//! postcondition as plain Rust, then checks it against the behaviour of the
//! REAL `std` API that the spec claims to describe. If Kani finds an input for
//! which the spec projection and real `std` disagree, the spec is FALSIFIED.
//!
//! Two historical vstd spec bugs are replayed as regressions:
//!   * #2674  `RangeInclusive::end_bound`      (fixed by PRs #2687 / #2801)
//!   * #2603  signed `checked_rem` / `checked_rem_euclid` (fixed by PR #2606)
//! For each we encode BOTH the OLD (buggy) claimed postcondition — which must
//! be FALSIFIABLE against real std — and the NEW (fixed) postcondition — which
//! must HOLD.
//!
//! The remaining harnesses mirror translatable first-order scalar specs from
//! `num.rs`, `option.rs` and `result.rs`; each cites the vstd spec it mirrors
//! (file:line at verus.git rev 7325eee).
//!
//! The `spec_*` model functions are plain Rust so the crate also type-checks
//! and unit-tests under stock `rustc` (see the `#[cfg(test)]` module) — that
//! gives a concrete-replay signal even where Kani is unavailable.

#![allow(clippy::all)]

/// Auto-generated harnesses (see `generate.py`). Kept in a submodule so the
/// hand-written regression harnesses above and the generated scalar sweep are
/// discovered by the same `cargo kani` run.
pub mod generated;

/// Harnesses for the vstd specifications added on `internal/c3f0aa9`
/// (windows, chunks, step_by, chain, flat_map, Pin, io printing).
pub mod adaptors;

use std::ops::{Bound, RangeBounds, RangeInclusive};

// ===========================================================================
// Helpers
// ===========================================================================

/// Structural equality for `Bound<&T>` values (std's `Bound` is not `PartialEq`
/// across reference lifetimes in a way that's ergonomic here).
fn bound_eq<T: PartialEq>(a: &Bound<&T>, b: &Bound<&T>) -> bool {
    match (a, b) {
        (Bound::Included(x), Bound::Included(y)) => x == y,
        (Bound::Excluded(x), Bound::Excluded(y)) => x == y,
        (Bound::Unbounded, Bound::Unbounded) => true,
        _ => false,
    }
}

// ===========================================================================
// Regression #2674 — RangeInclusive::<T>::end_bound
// ---------------------------------------------------------------------------
// OLD spec (verus.git 6e73050 source/vstd/std_specs/range.rs, the
// `<RangeInclusive<T> as RangeBounds<T>>::end_bound` assume_specification):
//     ensures  spec_bound(result) == SpecBound::Included(&range@.end)
//   i.e. end_bound() is claimed to ALWAYS be Included(end), unconditionally.
//
// NEW spec (verus.git 7325eee source/vstd/std_specs/range.rs:
//   `spec_range_inclusive_end_bound` + its assume_specification):
//     result == if range@.exhausted { Excluded(&end) } else { Included(&end) }
//
// Real std: RangeInclusive::end_bound() returns Included(end) while the range
// is live, but Excluded(end) once the iterator has been exhausted. Hence the
// OLD spec is wrong exactly in the exhausted case.
// ===========================================================================

/// OLD claimed postcondition, as an executable predicate over the observed
/// `end_bound()` result and the (self-tracked) exhaustion flag.
/// OLD: Included(end) regardless of `exhausted`.
fn spec_2674_old_holds(got: &Bound<&u8>, end: u8, _exhausted: bool) -> bool {
    bound_eq(got, &Bound::Included(&end))
}

/// NEW claimed postcondition: Excluded(end) iff exhausted, else Included(end).
fn spec_2674_new_holds(got: &Bound<&u8>, end: u8, exhausted: bool) -> bool {
    let expected = if exhausted {
        Bound::Excluded(&end)
    } else {
        Bound::Included(&end)
    };
    bound_eq(got, &expected)
}

/// Drive `1u8..=1u8` to exhaustion by iteration, then observe `end_bound()`.
/// Returns (observed end_bound cloned into owned Bound<u8>, exhausted flag).
fn exhaust_and_end_bound(lo: u8, hi: u8) -> (Bound<u8>, u8) {
    let mut r: RangeInclusive<u8> = lo..=hi;
    // Exhaust the iterator: after the last `Some`, `next()` yields `None`
    // and std flips the internal `exhausted` flag.
    while r.next().is_some() {}
    let owned = match r.end_bound() {
        Bound::Included(&x) => Bound::Included(x),
        Bound::Excluded(&x) => Bound::Excluded(x),
        Bound::Unbounded => Bound::Unbounded,
    };
    (owned, hi)
}

#[cfg(kani)]
#[kani::proof]
#[kani::should_panic] // the pre-fix spec is wrong; this assertion must fail
#[kani::unwind(4)]
fn r2674_old_spec_is_falsifiable() {
    // Brief: exhaust `1u8..=1u8` then call end_bound.
    let (owned, end) = exhaust_and_end_bound(1u8, 1u8);
    let got: Bound<&u8> = match &owned {
        Bound::Included(x) => Bound::Included(x),
        Bound::Excluded(x) => Bound::Excluded(x),
        Bound::Unbounded => Bound::Unbounded,
    };
    // The OLD vstd spec claimed Included(end) even after exhaustion.
    // Real std returns Excluded(end). This assertion MUST FAIL under Kani,
    // demonstrating the OLD spec is unsound.
    assert!(
        spec_2674_old_holds(&got, end, /*exhausted=*/ true),
        "#2674: OLD vstd spec claims end_bound()==Included(end) after \
         exhaustion, but real std returns Excluded(end)"
    );
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(4)]
fn r2674_new_spec_holds() {
    let (owned, end) = exhaust_and_end_bound(1u8, 1u8);
    let got: Bound<&u8> = match &owned {
        Bound::Included(x) => Bound::Included(x),
        Bound::Excluded(x) => Bound::Excluded(x),
        Bound::Unbounded => Bound::Unbounded,
    };
    // NEW spec, exhausted case: Excluded(end). MUST HOLD.
    assert!(
        spec_2674_new_holds(&got, end, /*exhausted=*/ true),
        "#2674: NEW vstd spec must match real std after exhaustion"
    );
}

#[cfg(kani)]
#[kani::proof]
fn r2674_new_spec_holds_fresh() {
    // A fresh (non-exhausted) RangeInclusive: end_bound()==Included(end).
    let hi: u8 = kani::any();
    let lo: u8 = kani::any();
    kani::assume(lo <= hi);
    let r: RangeInclusive<u8> = lo..=hi;
    let owned = match r.end_bound() {
        Bound::Included(&x) => Bound::Included(x),
        Bound::Excluded(&x) => Bound::Excluded(x),
        Bound::Unbounded => Bound::Unbounded,
    };
    let got: Bound<&u8> = match &owned {
        Bound::Included(x) => Bound::Included(x),
        Bound::Excluded(x) => Bound::Excluded(x),
        Bound::Unbounded => Bound::Unbounded,
    };
    assert!(
        spec_2674_new_holds(&got, hi, /*exhausted=*/ false),
        "#2674: NEW vstd spec must match real std when not exhausted"
    );
    // And the OLD spec happens to agree in the non-exhausted case.
    assert!(spec_2674_old_holds(&got, hi, false));
}

// ===========================================================================
// Regression #2603 — signed checked_rem / checked_rem_euclid
// ---------------------------------------------------------------------------
// OLD buggy spec (parent of verus.git c00d4d45d, PR #2606, source/vstd/
// std_specs/num.rs signed `checked_rem` / `checked_rem_euclid`):
//     checked_rem:        if rhs == 0 { None } else { Some(<sign-cased rem>) }
//     checked_rem_euclid: if rhs == 0 { None }
//                         else if MIN <= lhs%rhs <= MAX { Some(lhs%rhs) }
//                         else { None }
//   Both MISS the `lhs == MIN && rhs == -1` overflow case.
//
// NEW fixed spec (verus.git 7325eee source/vstd/std_specs/num.rs:488, :500):
//     if rhs == 0 || (lhs == <$iN>::MIN && rhs == -1) { None } else { Some(..) }
//
// Real std: i8::MIN.checked_rem(-1) == None and
//           i8::MIN.checked_rem_euclid(-1) == None (the division overflows).
// ===========================================================================

/// OLD (buggy) `checked_rem` spec projection for i8, faithful to the pre-#2606
/// sign-cased body, computed over i128 to avoid intermediate overflow.
fn spec_2603_checked_rem_old_i8(lhs: i8, rhs: i8) -> Option<i8> {
    if rhs == 0 {
        return None;
    }
    let x = lhs as i128;
    let d = rhs as i128;
    let output = if x == 0 {
        0
    } else if x > 0 && d > 0 {
        x % d
    } else if x < 0 && d < 0 {
        ((x * -1) % (d * -1)) * -1
    } else if x < 0 {
        ((x * -1) % d) * -1
    } else {
        x % (d * -1)
    };
    if output < i8::MIN as i128 || output > i8::MAX as i128 {
        None
    } else {
        Some(output as i8)
    }
}

/// NEW (fixed) `checked_rem` spec projection: truncated remainder, guarded.
fn spec_2603_checked_rem_new_i8(lhs: i8, rhs: i8) -> Option<i8> {
    if rhs == 0 || (lhs == i8::MIN && rhs == -1) {
        None
    } else {
        Some(((lhs as i128) % (rhs as i128)) as i8)
    }
}

/// OLD (buggy) `checked_rem_euclid` spec projection for i8.
fn spec_2603_checked_rem_euclid_old_i8(lhs: i8, rhs: i8) -> Option<i8> {
    if rhs == 0 {
        return None;
    }
    // Verus spec `%` on `int` is Euclidean modulo.
    let m = (lhs as i128).rem_euclid(rhs as i128);
    if m >= i8::MIN as i128 && m <= i8::MAX as i128 {
        Some(m as i8)
    } else {
        None
    }
}

/// NEW (fixed) `checked_rem_euclid` spec projection: Euclidean rem, guarded.
fn spec_2603_checked_rem_euclid_new_i8(lhs: i8, rhs: i8) -> Option<i8> {
    if rhs == 0 || (lhs == i8::MIN && rhs == -1) {
        None
    } else {
        Some((lhs as i128).rem_euclid(rhs as i128) as i8)
    }
}

#[cfg(kani)]
#[kani::proof]
#[kani::should_panic] // the pre-fix spec is wrong; this assertion must fail
fn r2603_checked_rem_old_spec_is_falsifiable() {
    let lhs: i8 = kani::any();
    let rhs: i8 = kani::any();
    // MUST FAIL: at (MIN, -1) the OLD spec yields Some(0) but std yields None.
    assert_eq!(
        spec_2603_checked_rem_old_i8(lhs, rhs),
        lhs.checked_rem(rhs),
        "#2603: OLD checked_rem spec disagrees with real std"
    );
}

#[cfg(kani)]
#[kani::proof]
fn r2603_checked_rem_new_spec_holds() {
    let lhs: i8 = kani::any();
    let rhs: i8 = kani::any();
    assert_eq!(
        spec_2603_checked_rem_new_i8(lhs, rhs),
        lhs.checked_rem(rhs),
        "#2603: NEW checked_rem spec must match real std"
    );
}

#[cfg(kani)]
#[kani::proof]
#[kani::should_panic] // the pre-fix spec is wrong; this assertion must fail
fn r2603_checked_rem_euclid_old_spec_is_falsifiable() {
    let lhs: i8 = kani::any();
    let rhs: i8 = kani::any();
    // MUST FAIL at (MIN, -1): OLD spec Some(0), std None.
    assert_eq!(
        spec_2603_checked_rem_euclid_old_i8(lhs, rhs),
        lhs.checked_rem_euclid(rhs),
        "#2603: OLD checked_rem_euclid spec disagrees with real std"
    );
}

#[cfg(kani)]
#[kani::proof]
fn r2603_checked_rem_euclid_new_spec_holds() {
    let lhs: i8 = kani::any();
    let rhs: i8 = kani::any();
    assert_eq!(
        spec_2603_checked_rem_euclid_new_i8(lhs, rhs),
        lhs.checked_rem_euclid(rhs),
        "#2603: NEW checked_rem_euclid spec must match real std"
    );
}

// ===========================================================================
// Translatable scalar specs (>=10). Each mirrors a current vstd spec and MUST
// HOLD against real std. Citations are file:line at verus.git rev 7325eee.
// ===========================================================================

// --- num.rs: unsigned checked_* (u8) -------------------------------------

/// mirrors num.rs:140  <u8>::checked_add
#[cfg(kani)]
#[kani::proof]
fn s_u8_checked_add() {
    let x: u8 = kani::any();
    let y: u8 = kani::any();
    let spec = if (x as u16) + (y as u16) > u8::MAX as u16 {
        None
    } else {
        Some((x as u16 + y as u16) as u8)
    };
    assert_eq!(spec, x.checked_add(y));
}

/// mirrors num.rs:164  <u8>::checked_sub
#[cfg(kani)]
#[kani::proof]
fn s_u8_checked_sub() {
    let x: u8 = kani::any();
    let y: u8 = kani::any();
    let spec = if (x as i16) - (y as i16) < 0 {
        None
    } else {
        Some((x - y) as u8)
    };
    assert_eq!(spec, x.checked_sub(y));
}

/// mirrors num.rs:176  <u8>::checked_mul
#[cfg(kani)]
#[kani::proof]
fn s_u8_checked_mul() {
    let x: u8 = kani::any();
    let y: u8 = kani::any();
    let spec = if (x as u16) * (y as u16) > u8::MAX as u16 {
        None
    } else {
        Some((x as u16 * y as u16) as u8)
    };
    assert_eq!(spec, x.checked_mul(y));
}

// --- num.rs: signed checked_* (i8) ---------------------------------------

/// mirrors num.rs:404  <i8>::checked_add
#[cfg(kani)]
#[kani::proof]
fn s_i8_checked_add() {
    let x: i8 = kani::any();
    let y: i8 = kani::any();
    let s = (x as i32) + (y as i32);
    let spec = if s < i8::MIN as i32 || s > i8::MAX as i32 {
        None
    } else {
        Some(s as i8)
    };
    assert_eq!(spec, x.checked_add(y));
}

/// mirrors num.rs:428  <i8>::checked_sub
#[cfg(kani)]
#[kani::proof]
fn s_i8_checked_sub() {
    let x: i8 = kani::any();
    let y: i8 = kani::any();
    let s = (x as i32) - (y as i32);
    let spec = if s < i8::MIN as i32 || s > i8::MAX as i32 {
        None
    } else {
        Some(s as i8)
    };
    assert_eq!(spec, x.checked_sub(y));
}

/// mirrors num.rs:452  <i8>::checked_mul
#[cfg(kani)]
#[kani::proof]
fn s_i8_checked_mul() {
    let x: i8 = kani::any();
    let y: i8 = kani::any();
    let s = (x as i32) * (y as i32);
    let spec = if s < i8::MIN as i32 || s > i8::MAX as i32 {
        None
    } else {
        Some(s as i8)
    };
    assert_eq!(spec, x.checked_mul(y));
}

/// mirrors num.rs:416  <i8>::checked_add_unsigned
#[cfg(kani)]
#[kani::proof]
fn s_i8_checked_add_unsigned() {
    let x: i8 = kani::any();
    let y: u8 = kani::any();
    let s = (x as i32) + (y as i32);
    let spec = if s > i8::MAX as i32 { None } else { Some(s as i8) };
    assert_eq!(spec, x.checked_add_unsigned(y));
}

// --- num.rs: wrapping_* (u8) ---------------------------------------------

/// mirrors num.rs:98  <u8>::wrapping_add  (mod 256 arithmetic)
#[cfg(kani)]
#[kani::proof]
fn s_u8_wrapping_add() {
    let x: u8 = kani::any();
    let y: u8 = kani::any();
    let spec = ((x as u16 + y as u16) % 256) as u8;
    assert_eq!(spec, x.wrapping_add(y));
}

/// mirrors num.rs:112  <u8>::wrapping_sub  (mod 256 arithmetic)
#[cfg(kani)]
#[kani::proof]
fn s_u8_wrapping_sub() {
    let x: u8 = kani::any();
    let y: u8 = kani::any();
    let spec = (((x as i16 - y as i16) & 0xff) as u16) as u8;
    assert_eq!(spec, x.wrapping_sub(y));
}

// --- option.rs -----------------------------------------------------------

/// mirrors option.rs:123 / :136  Option::is_some / is_none
#[cfg(kani)]
#[kani::proof]
fn s_option_is_some_none() {
    let some: bool = kani::any();
    let v: u8 = kani::any();
    let o: Option<u8> = if some { Some(v) } else { None };
    assert_eq!(o.is_some(), matches!(o, Some(_)));
    assert_eq!(o.is_none(), matches!(o, None));
    // is_some and is_none are exact complements (option.rs models).
    assert_eq!(o.is_some(), !o.is_none());
}

/// mirrors option.rs:177  Option::unwrap_or
#[cfg(kani)]
#[kani::proof]
fn s_option_unwrap_or() {
    let some: bool = kani::any();
    let v: u8 = kani::any();
    let d: u8 = kani::any();
    let o: Option<u8> = if some { Some(v) } else { None };
    let spec = match o {
        Some(x) => x,
        None => d,
    };
    assert_eq!(spec, o.unwrap_or(d));
}

// --- result.rs -----------------------------------------------------------

/// mirrors result.rs:135 / :148  Result::is_ok / is_err
#[cfg(kani)]
#[kani::proof]
fn s_result_is_ok_err() {
    let ok: bool = kani::any();
    let v: u8 = kani::any();
    let r: Result<u8, u8> = if ok { Ok(v) } else { Err(v) };
    assert_eq!(r.is_ok(), matches!(r, Ok(_)));
    assert_eq!(r.is_err(), matches!(r, Err(_)));
    assert_eq!(r.is_ok(), !r.is_err());
}

// ===========================================================================
// Concrete-replay unit tests (run under stock `rustc` via `cargo test`).
// These pin the historical counterexamples so the regression signal survives
// even when Kani is not installed.
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replay_2674_old_spec_wrong_new_right() {
        let (owned, end) = exhaust_and_end_bound(1u8, 1u8);
        let got: Bound<&u8> = match &owned {
            Bound::Included(x) => Bound::Included(x),
            Bound::Excluded(x) => Bound::Excluded(x),
            Bound::Unbounded => Bound::Unbounded,
        };
        // Real std returns Excluded(1) after exhaustion.
        assert!(matches!(owned, Bound::Excluded(1)));
        // OLD spec (Included) is FALSE here; NEW spec (Excluded) is TRUE.
        assert!(!spec_2674_old_holds(&got, end, true));
        assert!(spec_2674_new_holds(&got, end, true));
    }

    #[test]
    fn replay_2603_checked_rem_min_neg1() {
        // Real std: i8::MIN.checked_rem(-1) == None.
        assert_eq!(i8::MIN.checked_rem(-1), None);
        // OLD spec disagrees (Some(0)); NEW spec agrees (None).
        assert_eq!(spec_2603_checked_rem_old_i8(i8::MIN, -1), Some(0));
        assert_eq!(spec_2603_checked_rem_new_i8(i8::MIN, -1), None);
    }

    #[test]
    fn replay_2603_checked_rem_euclid_min_neg1() {
        assert_eq!(i8::MIN.checked_rem_euclid(-1), None);
        assert_eq!(spec_2603_checked_rem_euclid_old_i8(i8::MIN, -1), Some(0));
        assert_eq!(spec_2603_checked_rem_euclid_new_i8(i8::MIN, -1), None);
    }

    #[test]
    fn exhaustive_i8_new_specs_match_std() {
        // Exhaustive 256*256 concrete check that the NEW specs match std.
        for lhs in i8::MIN..=i8::MAX {
            for rhs in i8::MIN..=i8::MAX {
                assert_eq!(spec_2603_checked_rem_new_i8(lhs, rhs), lhs.checked_rem(rhs));
                assert_eq!(
                    spec_2603_checked_rem_euclid_new_i8(lhs, rhs),
                    lhs.checked_rem_euclid(rhs)
                );
            }
        }
    }

    #[test]
    fn exhaustive_i8_old_specs_have_a_counterexample() {
        // The OLD specs must disagree with std for at least one input.
        let mut rem_bad = false;
        let mut euclid_bad = false;
        for lhs in i8::MIN..=i8::MAX {
            for rhs in i8::MIN..=i8::MAX {
                if spec_2603_checked_rem_old_i8(lhs, rhs) != lhs.checked_rem(rhs) {
                    rem_bad = true;
                }
                if spec_2603_checked_rem_euclid_old_i8(lhs, rhs) != lhs.checked_rem_euclid(rhs) {
                    euclid_bad = true;
                }
            }
        }
        assert!(rem_bad, "OLD checked_rem spec should be falsifiable");
        assert!(euclid_bad, "OLD checked_rem_euclid spec should be falsifiable");
    }
}
