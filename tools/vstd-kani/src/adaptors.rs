//! Harnesses for the vstd specifications added on the `internal/c3f0aa9` branch
//! (soundness-review programme, C rows): `<[T]>::windows`, `<[T]>::chunks`,
//! `Iterator::step_by`, `Iterator::chain`, `Iterator::flat_map`, `Pin` for
//! `Unpin` targets, and `std::io::_print`/`_eprint`.
//!
//! Each harness re-implements the executable projection of the spec's
//! postcondition (`vstd/std_specs/{slice,iter,pin,io}.rs` on that branch) and
//! checks it against the REAL std API on symbolic inputs. The iterator specs
//! also speak about `will_return_none`/`decrease` (the prophetic model); those
//! are not observable from the outside and are not checked here. What is
//! checked is the observable content: the sequence of items the adaptor yields.
//!
//! Every spec projection is written as plain Rust so the module also runs under
//! stock `rustc` (`cargo test`), exhaustively over small domains, giving a
//! concrete-replay signal where Kani is unavailable.

#![allow(clippy::all)]

#[cfg(any(kani, test))]
use std::pin::Pin;

// ---------------------------------------------------------------------------
// Spec projections (plain Rust)
// ---------------------------------------------------------------------------

/// `spec_windows(s, k)` (slice.rs): empty if `k == 0 || s.len() < k`, else
/// `s.len() - k + 1` windows, window `i` = `s[i..i+k]`.
fn spec_windows(s: &[u8], k: usize) -> Vec<Vec<u8>> {
    if k == 0 || s.len() < k {
        Vec::new()
    } else {
        (0..=s.len() - k).map(|i| s[i..i + k].to_vec()).collect()
    }
}

/// `spec_chunks(s, k)` (slice.rs): empty if `k == 0`, else `ceil(len / k)`
/// chunks, chunk `i` = `s[i*k .. min((i+1)*k, len)]`.
fn spec_chunks(s: &[u8], k: usize) -> Vec<Vec<u8>> {
    if k == 0 {
        Vec::new()
    } else {
        let n = (s.len() + k - 1) / k;
        (0..n).map(|i| s[i * k..std::cmp::min((i + 1) * k, s.len())].to_vec()).collect()
    }
}

/// `spec_seq_step_by(s, step)` (iter.rs): `ceil(len / step)` items, item `i` = `s[i*step]`.
fn spec_step_by(s: &[u8], step: usize) -> Vec<u8> {
    let n = (s.len() + step - 1) / step;
    (0..n).map(|i| s[i * step]).collect()
}

/// `chain_postcondition` (iter.rs): `remaining(r) == a.remaining() + b.remaining()`.
fn spec_chain(a: &[u8], b: &[u8]) -> Vec<u8> {
    let mut v = a.to_vec();
    v.extend_from_slice(b);
    v
}

/// `flat_map_postcondition` (iter.rs): `remaining(r) == parts.flatten()` where
/// `parts[k]` is what `f(items[k]).into_iter()` yields. Written without std's
/// own `flat_map`, so the comparison is against an independent model.
fn spec_flat_map_parts<F: Fn(u8) -> Vec<u8>>(s: &[u8], f: F) -> Vec<u8> {
    let mut out = Vec::new();
    for x in s {
        out.extend(f(*x)); // parts[k] = f(items[k]).into_iter(), flattened
    }
    out
}

/// Symbolic slice of length ≤ N.
#[cfg(kani)]
fn any_slice<const N: usize>() -> ([u8; N], usize) {
    let arr: [u8; N] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= N);
    (arr, len)
}

// ---------------------------------------------------------------------------
// <[T]>::windows   (slice.rs: requires size > 0; ensures remaining == spec_windows)
// ---------------------------------------------------------------------------

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(6)]
fn windows_remaining_matches_spec() {
    // Element-wise form of `remaining == spec_windows(s, size)`: the number of
    // windows is `len - size + 1` (or 0), and window i is `s[i..i+size]`.
    let (arr, len) = any_slice::<4>();
    let size: usize = kani::any();
    kani::assume(size >= 1 && size <= 5);
    let s = &arr[..len];
    let expected_count = if s.len() < size { 0 } else { s.len() - size + 1 };
    let mut i = 0usize;
    for w in s.windows(size) {
        assert!(i < expected_count, "windows: more windows than spec_windows");
        assert!(w.len() == size, "windows: window length");
        let mut j = 0usize;
        while j < size {
            assert!(w[j] == s[i + j], "windows: window i must equal s[i..i+size]");
            j += 1;
        }
        i += 1;
    }
    assert!(i == expected_count, "windows: fewer windows than spec_windows");
}

// ---------------------------------------------------------------------------
// <[T]>::chunks   (slice.rs: requires chunk_size > 0; ensures remaining == spec_chunks)
// ---------------------------------------------------------------------------

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(6)]
fn chunks_remaining_matches_spec() {
    // Element-wise form of `remaining == spec_chunks(s, k)`: ceil(len/k) chunks,
    // chunk i is `s[i*k .. min((i+1)*k, len)]`.
    let (arr, len) = any_slice::<4>();
    let k: usize = kani::any();
    kani::assume(k >= 1 && k <= 5);
    let s = &arr[..len];
    let expected_count = (s.len() + k - 1) / k;
    let mut i = 0usize;
    for c in s.chunks(k) {
        assert!(i < expected_count, "chunks: more chunks than spec_chunks");
        let lo = i * k;
        let hi = if (i + 1) * k <= s.len() { (i + 1) * k } else { s.len() };
        assert!(c.len() == hi - lo, "chunks: chunk length");
        let mut j = 0usize;
        while j < c.len() {
            assert!(c[j] == s[lo + j], "chunks: chunk i must equal s[i*k..hi]");
            j += 1;
        }
        i += 1;
    }
    assert!(i == expected_count, "chunks: fewer chunks than spec_chunks");
}

// ---------------------------------------------------------------------------
// Iterator::step_by   (iter.rs: requires step > 0; remaining == spec_seq_step_by)
// ---------------------------------------------------------------------------

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(8)]
fn step_by_remaining_matches_spec() {
    let (arr, len) = any_slice::<5>();
    let step: usize = kani::any();
    kani::assume(step >= 1 && step <= 6);
    let s = &arr[..len];
    let got: Vec<u8> = s.iter().copied().step_by(step).collect();
    assert!(got == spec_step_by(s, step), "step_by: real std disagrees with spec_seq_step_by");
}

// ---------------------------------------------------------------------------
// Iterator::chain   (iter.rs: remaining == a.remaining() + b.remaining())
// ---------------------------------------------------------------------------

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(8)]
fn chain_remaining_matches_spec() {
    let (a, la) = any_slice::<3>();
    let (b, lb) = any_slice::<3>();
    let (a, b) = (&a[..la], &b[..lb]);
    let got: Vec<u8> = a.iter().copied().chain(b.iter().copied()).collect();
    assert!(got == spec_chain(a, b), "chain: real std disagrees with chain_postcondition");
}

// ---------------------------------------------------------------------------
// Iterator::flat_map   (iter.rs: remaining == flatten(parts), parts[k] = f(item_k))
// ---------------------------------------------------------------------------

/// The inner producer used by the harness: `x` yields `x` copies of `x`
/// (bounded to keep the unwinding small).
fn inner(x: u8) -> Vec<u8> {
    vec![x; (x % 3) as usize]
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(8)]
fn flat_map_remaining_matches_spec() {
    // Element-wise form of `remaining == flatten(parts)` with parts[k] = inner(items[k]):
    // the k-th part contributes `items[k] % 3` copies of `items[k]`, in order.
    let (arr, len) = any_slice::<3>();
    let s = &arr[..len];
    let mut expected: [u8; 6] = [0; 6];
    let mut n = 0usize;
    let mut k = 0usize;
    while k < s.len() {
        let mut c = 0u8;
        while c < s[k] % 3 {
            expected[n] = s[k];
            n += 1;
            c += 1;
        }
        k += 1;
    }
    let mut i = 0usize;
    for x in s.iter().copied().flat_map(inner) {
        assert!(i < n, "flat_map: more items than flatten(parts)");
        assert!(x == expected[i], "flat_map: item i must be flatten(parts)[i]");
        i += 1;
    }
    assert!(i == n, "flat_map: fewer items than flatten(parts)");
}

// ---------------------------------------------------------------------------
// Pin<P> for P::Target: Unpin   (pin.rs)
//   new(p).pointer() == p ; into_inner(pin) == pin.pointer() ;
//   get_mut(pin) == pin.pointer() ; get_ref(pin) == pin.pointer()
// The `pointer()` ghost accessor is the wrapped pointer, so the observable
// content is: the pointee reached through the pin is the original pointee,
// and into_inner returns the same pointer (same address).
// ---------------------------------------------------------------------------

#[cfg(kani)]
#[kani::proof]
fn pin_new_get_ref_into_inner() {
    let x: u32 = kani::any();
    let p: Pin<&u32> = Pin::new(&x);
    assert!(*p.get_ref() == x, "Pin::get_ref must return the pinned pointer");
    let inner: &u32 = Pin::into_inner(Pin::new(&x));
    assert!(inner as *const u32 == &x as *const u32, "Pin::into_inner must return the pointer");
}

#[cfg(kani)]
#[kani::proof]
fn pin_new_get_mut_writes_through() {
    let mut x: u32 = kani::any();
    let v: u32 = kani::any();
    let addr = &x as *const u32;
    {
        let p: Pin<&mut u32> = Pin::new(&mut x);
        let r: &mut u32 = p.get_mut();
        assert!(r as *const u32 == addr, "Pin::get_mut must return the pinned pointer");
        *r = v;
    }
    assert!(x == v, "a write through Pin::get_mut reaches the pinned value");
}

// ---------------------------------------------------------------------------
// Vec::retain   (vec.rs: final(vec)@ == old(vec)@.filter_index(|j| keep[j]),
//                keep[j] == f(&old(vec)@[j]))
// ---------------------------------------------------------------------------

fn spec_retain(s: &[u8], f: fn(&u8) -> bool) -> Vec<u8> {
    let mut out = Vec::new();
    for x in s {
        if f(x) {
            out.push(*x);
        }
    }
    out
}

fn is_even(x: &u8) -> bool {
    *x % 2 == 0
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(6)]
fn retain_matches_spec() {
    let (arr, len) = any_slice::<4>();
    let mut v: Vec<u8> = arr[..len].to_vec();
    v.retain(is_even);
    let expected = spec_retain(&arr[..len], is_even);
    assert!(v.len() == expected.len(), "retain: length differs from filter_index");
    let mut i = 0usize;
    while i < v.len() {
        assert!(v[i] == expected[i], "retain: element differs from filter_index");
        i += 1;
    }
}

// ---------------------------------------------------------------------------
// Vec::drain   (vec.rs: requires slice_range_valid; drained items == old[start..end];
//               final(vec)@ == old[..start] + old[end..])
// ---------------------------------------------------------------------------

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(6)]
fn drain_matches_spec() {
    // Symbolic contents and range over a fixed-length vector (a symbolic length
    // makes CBMC's model of Drain's tail move too large for the available memory).
    let arr: [u8; 3] = kani::any();
    let len = 3usize;
    let start: usize = kani::any();
    let end: usize = kani::any();
    kani::assume(start <= end && end <= len);
    let mut v: Vec<u8> = vec![arr[0], arr[1], arr[2]];
    // drained items == old[start..end], read one by one (no collect: keeps CBMC small)
    let mut i = 0usize;
    {
        let mut d = v.drain(start..end);
        while let Some(x) = d.next() {
            assert!(i < end - start, "drain: more items than the range");
            assert!(x == arr[start + i], "drain: drained item");
            i += 1;
        }
    }
    assert!(i == end - start, "drain: fewer items than the range");
    // remaining == old[..start] + old[end..]
    assert!(v.len() == len - (end - start), "drain: remaining length");
    let mut j = 0usize;
    while j < v.len() {
        let src = if j < start { j } else { j + (end - start) };
        assert!(v[j] == arr[src], "drain: remaining item");
        j += 1;
    }
}

// ---------------------------------------------------------------------------
// std::io::_print / _eprint   (io.rs): no postcondition; the spec only claims
// the call returns (it may panic on a failed write, which the spec does not
// exclude: assume_specification without `no_unwind`). Nothing to falsify; a
// smoke harness documents the coverage decision.
// ---------------------------------------------------------------------------

#[cfg(kani)]
#[kani::proof]
fn print_has_no_postcondition_to_check() {
    // `print!` expands to `std::io::_print(format_args!(..))`; the spec states
    // nothing about the result, so any behaviour is consistent with it.
    let _ = format_args!("{}", 1u8);
}

// ---------------------------------------------------------------------------
// Stock-rustc exhaustive replays over small domains
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn all_slices(max_len: usize) -> Vec<Vec<u8>> {
        // all slices of length ≤ max_len over the alphabet {0, 1, 2}
        let mut out = vec![Vec::new()];
        let mut layer = vec![Vec::new()];
        for _ in 0..max_len {
            let mut next = Vec::new();
            for s in &layer {
                for x in 0..3u8 {
                    let mut t = s.clone();
                    t.push(x);
                    next.push(t);
                }
            }
            out.extend(next.iter().cloned());
            layer = next;
        }
        out
    }

    #[test]
    fn windows_chunks_step_by_exhaustive() {
        for s in all_slices(5) {
            for k in 1..=6usize {
                let w: Vec<Vec<u8>> = s.windows(k).map(|w| w.to_vec()).collect();
                assert_eq!(w, spec_windows(&s, k), "windows {s:?} {k}");
                let c: Vec<Vec<u8>> = s.chunks(k).map(|c| c.to_vec()).collect();
                assert_eq!(c, spec_chunks(&s, k), "chunks {s:?} {k}");
                let st: Vec<u8> = s.iter().copied().step_by(k).collect();
                assert_eq!(st, spec_step_by(&s, k), "step_by {s:?} {k}");
            }
        }
    }

    #[test]
    fn chain_flat_map_exhaustive() {
        for a in all_slices(3) {
            for b in all_slices(3) {
                let got: Vec<u8> = a.iter().copied().chain(b.iter().copied()).collect();
                assert_eq!(got, spec_chain(&a, &b));
            }
            let got: Vec<u8> = a.iter().copied().flat_map(inner).collect();
            assert_eq!(got, spec_flat_map_parts(&a, inner));
        }
    }

    #[test]
    fn retain_drain_exhaustive() {
        for s in all_slices(4) {
            let mut v = s.clone();
            v.retain(is_even);
            assert_eq!(v, spec_retain(&s, is_even));
            for start in 0..=s.len() {
                for end in start..=s.len() {
                    let mut v = s.clone();
                    let d: Vec<u8> = v.drain(start..end).collect();
                    assert_eq!(d, s[start..end].to_vec());
                    let mut rest = s[..start].to_vec();
                    rest.extend_from_slice(&s[end..]);
                    assert_eq!(v, rest);
                }
            }
        }
    }

    #[test]
    fn pin_unpin_accessors() {
        let mut x = 5u32;
        assert_eq!(*Pin::new(&x).get_ref(), 5);
        let inner: &u32 = Pin::into_inner(Pin::new(&x));
        assert!(inner as *const u32 == &x as *const u32);
        {
            let p = Pin::new(&mut x);
            *p.get_mut() = 9;
        }
        assert_eq!(x, 9);
    }
}
