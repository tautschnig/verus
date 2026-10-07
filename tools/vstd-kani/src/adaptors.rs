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
// char / u8 ASCII predicates (char.rs) and core::cmp::{max,min} (cmp.rs)
// ---------------------------------------------------------------------------

#[cfg(kani)]
#[kani::proof]
fn ascii_predicates_match_spec() {
    let c: char = kani::any();
    assert!(c.is_ascii() == ((c as u32) < 128), "char::is_ascii");
    assert!(c.is_ascii_digit() == ('0' <= c && c <= '9'), "char::is_ascii_digit");
    assert!(c.is_ascii_alphabetic() == (('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')), "char::is_ascii_alphabetic");
    assert!(c.is_ascii_alphanumeric() == (('0' <= c && c <= '9') || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')), "char::is_ascii_alphanumeric");
    assert!(c.is_ascii_uppercase() == ('A' <= c && c <= 'Z'), "char::is_ascii_uppercase");
    assert!(c.is_ascii_lowercase() == ('a' <= c && c <= 'z'), "char::is_ascii_lowercase");
    assert!(c.is_ascii_whitespace() == (c == ' ' || c == '\t' || c == '\n' || c == '\u{C}' || c == '\r'), "char::is_ascii_whitespace");
    assert!(c.is_ascii_hexdigit() == (('0' <= c && c <= '9') || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F')), "char::is_ascii_hexdigit");
    let b: u8 = kani::any();
    assert!(b.is_ascii() == (b < 128), "u8::is_ascii");
    assert!(b.is_ascii_digit() == (b'0' <= b && b <= b'9'), "u8::is_ascii_digit");
    assert!(b.is_ascii_alphabetic() == ((b'a' <= b && b <= b'z') || (b'A' <= b && b <= b'Z')), "u8::is_ascii_alphabetic");
    assert!(b.is_ascii_alphanumeric() == ((b'0' <= b && b <= b'9') || (b'a' <= b && b <= b'z') || (b'A' <= b && b <= b'Z')), "u8::is_ascii_alphanumeric");
    assert!(b.is_ascii_whitespace() == (b == b' ' || b == b'\t' || b == b'\n' || b == 0x0C || b == b'\r'), "u8::is_ascii_whitespace");
}

#[cfg(kani)]
#[kani::proof]
fn cmp_max_min_match_ord() {
    let a: u64 = kani::any();
    let b: u64 = kani::any();
    assert!(core::cmp::max(a, b) == a.max(b), "core::cmp::max is Ord::max");
    assert!(core::cmp::min(a, b) == a.min(b), "core::cmp::min is Ord::min");
}

// ---------------------------------------------------------------------------
// rotate_left/right (wrapping.rs model), to/from_{le,be}_bytes (bytes.rs byte_of),
// NonZero::trailing_zeros, chunks_exact / chunks_exact_mut
// ---------------------------------------------------------------------------

/// `byte_of(x, i)` = `(x >> 8i) & 0xff`.
fn byte_of(x: u128, i: u32) -> u8 {
    ((x >> (8 * i)) & 0xff) as u8
}

#[cfg(kani)]
#[kani::proof]
fn rotate_matches_spec() {
    let x: u32 = kani::any();
    let n: u32 = kani::any();
    let r = n % 32;
    let left = if r == 0 { x } else { (x << r) | (x >> (32 - r)) };
    let right = if r == 0 { x } else { (x >> r) | (x << (32 - r)) };
    assert!(x.rotate_left(n) == left, "u32::rotate_left");
    assert!(x.rotate_right(n) == right, "u32::rotate_right");
}

#[cfg(kani)]
#[kani::proof]
fn bytes_match_spec() {
    let x: u32 = kani::any();
    let le = x.to_le_bytes();
    let be = x.to_be_bytes();
    let mut i = 0u32;
    while i < 4 {
        assert!(le[i as usize] == byte_of(x as u128, i), "to_le_bytes");
        assert!(be[i as usize] == byte_of(x as u128, 3 - i), "to_be_bytes");
        i += 1;
    }
    let b: [u8; 4] = kani::any();
    let f = u32::from_le_bytes(b);
    let g = u32::from_be_bytes(b);
    let mut i = 0u32;
    while i < 4 {
        assert!(byte_of(f as u128, i) == b[i as usize], "from_le_bytes");
        assert!(byte_of(g as u128, 3 - i) == b[i as usize], "from_be_bytes");
        i += 1;
    }
}

#[cfg(kani)]
#[kani::proof]
fn nonzero_trailing_zeros_matches_primitive() {
    let x: u64 = kani::any();
    kani::assume(x != 0);
    let nz = core::num::NonZeroU64::new(x).unwrap();
    assert!(nz.trailing_zeros() == x.trailing_zeros(), "NonZero::trailing_zeros");
    assert!(nz.leading_zeros() == x.leading_zeros(), "NonZero::leading_zeros");
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(6)]
fn chunks_exact_matches_spec() {
    let (arr, len) = any_slice::<4>();
    let k: usize = kani::any();
    kani::assume(k >= 1 && k <= 5);
    let s = &arr[..len];
    let expected_count = s.len() / k;
    let mut i = 0usize;
    for c in s.chunks_exact(k) {
        assert!(i < expected_count, "chunks_exact: more chunks than len / k");
        assert!(c.len() == k, "chunks_exact: chunk length");
        let mut j = 0usize;
        while j < k {
            assert!(c[j] == s[i * k + j], "chunks_exact: chunk i must equal s[i*k..(i+1)*k]");
            j += 1;
        }
        i += 1;
    }
    assert!(i == expected_count, "chunks_exact: fewer chunks than len / k");
    // chunks_exact_mut: writes reach exactly the full chunks; the remainder is untouched
    let mut v: [u8; 4] = arr;
    let orig = arr;
    for c in v[..len].chunks_exact_mut(k) {
        c[0] = 0xAA;
    }
    let mut j = 0usize;
    while j < len {
        let i = j / k;
        if i < expected_count && j % k == 0 {
            assert!(v[j] == 0xAA, "chunks_exact_mut: first byte of each full chunk written");
        } else {
            assert!(v[j] == orig[j], "chunks_exact_mut: other bytes untouched");
        }
        j += 1;
    }
}

// ---------------------------------------------------------------------------
// <&mut I as Iterator>::next   (iter.rs: the stored reference is unchanged, only the
// referent advances; the call is I::next on a reborrow of the referent)
// ---------------------------------------------------------------------------
//
// Observable content of the spec: (a) `n` calls of `next` through `&mut it` leave `it` in
// the same state as `n` direct calls (the referent is advanced by `I::next`, nothing
// else); (b) the `&mut I` inside a `for x in &mut it` loop is the same borrow throughout,
// so after the loop `it` is the advanced iterator (the "future" of the reference).
// Checked on the concrete iterators the survey used (slice::Iter, ChunksExactMut).

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(7)]
fn by_mut_ref_next_matches_direct_next() {
    let (arr, len) = any_slice::<5>();
    let n: usize = kani::any();
    kani::assume(n <= 6);
    let s = &arr[..len];
    let mut direct = s.iter();
    let mut via_ref = s.iter();
    let mut i = 0usize;
    while i < n {
        let d = direct.next();
        let r = {
            let r: &mut core::slice::Iter<u8> = &mut via_ref;
            // this is `<&mut Iter as Iterator>::next`, not `Iter::next` on the referent
            Iterator::next(&mut { r })
        };
        assert!(d == r, "&mut I: next yields the same element as the referent's next");
        i += 1;
    }
    assert!(direct.len() == via_ref.len(), "&mut I: referent advanced identically");
    // (b) a for-loop through `&mut it` exhausts `it`, and `it` is usable afterwards
    let mut it = s.iter();
    let mut count = 0usize;
    for _x in &mut it {
        count += 1;
    }
    assert!(count == len, "for x in &mut it: visits every element");
    assert!(it.next().is_none(), "for x in &mut it: it is exhausted afterwards");
    // partial: break after one element, `it` continues from the second
    let mut it2 = s.iter();
    for _x in &mut it2 {
        break;
    }
    let rest = it2.len();
    assert!(rest == if len == 0 { 0 } else { len - 1 }, "break leaves it at the next element");
}

// ---------------------------------------------------------------------------
// ChunksExactMut::next keeps the iteration's accessors   (slice.rs:
// chunks_exact_mut_len/size/remainder unchanged by next) — observable as: after any number
// of `next` calls, `into_remainder()` is the same slice (len % k, the original tail)
// ---------------------------------------------------------------------------

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(7)]
fn chunks_exact_mut_remainder_stable_under_next() {
    let (arr, len) = any_slice::<5>();
    let k: usize = kani::any();
    kani::assume(k >= 1 && k <= 5);
    let n: usize = kani::any();
    kani::assume(n <= 6);
    let orig = arr;
    let mut v: [u8; 5] = arr;
    let mut it = v[..len].chunks_exact_mut(k);
    let mut i = 0usize;
    while i < n {
        let _ = it.next();
        i += 1;
    }
    let rem = it.into_remainder();
    assert!(rem.len() == len % k, "into_remainder after n nexts: length is len % k");
    let base = len - len % k;
    let mut j = 0usize;
    while j < rem.len() {
        assert!(rem[j] == orig[base + j], "into_remainder after n nexts: the original tail");
        j += 1;
    }
}

// ---------------------------------------------------------------------------
// Zip::next / Take::next over `&mut` components   (iter.rs: the first iterator is advanced
// by one `next` per call; the second only if the first produced an element; when the second
// runs out the element taken from the first is dropped. Take advances the inner iterator
// while its count is positive and leaves it untouched afterwards.)
// ---------------------------------------------------------------------------

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(8)]
fn zip_next_advances_components_as_spec() {
    let (arr_a, la) = any_slice::<5>();
    let (arr_b, lb) = any_slice::<5>();
    let n: usize = kani::any();
    kani::assume(n <= 7);
    let a_s = &arr_a[..la];
    let b_s = &arr_b[..lb];
    let mut a = a_s.iter();
    let mut b = b_s.iter();
    // model: positions of the two component iterators
    let mut pa = 0usize;
    let mut pb = 0usize;
    {
        let mut z = a.by_ref().zip(b.by_ref());
        let mut i = 0usize;
        while i < n {
            let r = z.next();
            // spec: a.next() first
            let x = if pa < la { pa += 1; Some(a_s[pa - 1]) } else { None };
            let expected = match x {
                None => None,
                Some(xv) => {
                    let y = if pb < lb { pb += 1; Some(b_s[pb - 1]) } else { None };
                    match y { None => None, Some(yv) => Some((xv, yv)) }
                }
            };
            assert!(r.map(|(p, q)| (*p, *q)) == expected, "Zip::next: yielded pair");
            i += 1;
        }
    }
    assert!(a.len() == la - pa, "Zip::next: first component advanced as modelled");
    assert!(b.len() == lb - pb, "Zip::next: second component advanced as modelled");
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(8)]
fn take_next_advances_inner_as_spec() {
    let (arr, len) = any_slice::<5>();
    let k: usize = kani::any();
    kani::assume(k <= 6);
    let n: usize = kani::any();
    kani::assume(n <= 7);
    let s = &arr[..len];
    let mut it = s.iter();
    let mut pos = 0usize;
    let mut count = k;
    {
        let mut t = it.by_ref().take(k);
        let mut i = 0usize;
        while i < n {
            let r = t.next();
            let expected = if count > 0 {
                count -= 1;
                if pos < len { pos += 1; Some(s[pos - 1]) } else { None }
            } else {
                None
            };
            assert!(r.copied() == expected, "Take::next: yielded element");
            i += 1;
        }
    }
    assert!(it.len() == len - pos, "Take::next: inner advanced only while count > 0");
}

// ---------------------------------------------------------------------------
// Iterator::for_each   (iter.rs: f is applied to every remaining element; per-element
// postconditions hold for all elements) — checked as: each element visited exactly once, in
// order, and a mutation through `&mut` items reaches every element
// ---------------------------------------------------------------------------

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(7)]
fn for_each_visits_every_element_once_in_order() {
    let (arr, len) = any_slice::<5>();
    let s = &arr[..len];
    let mut seen: [u8; 5] = [0; 5];
    let mut count = 0usize;
    // closure without captured mutation is what Verus can express; here the harness itself
    // records the visit order through a mutable capture (allowed in plain Rust)
    s.iter().for_each(|x| {
        seen[count] = *x;
        count += 1;
    });
    assert!(count == len, "for_each: exactly len calls");
    let mut i = 0usize;
    while i < len {
        assert!(seen[i] == s[i], "for_each: elements in order");
        i += 1;
    }
    let mut v: [u8; 5] = arr;
    v[..len].iter_mut().for_each(|x| *x = 0);
    let mut j = 0usize;
    while j < 5 {
        assert!(v[j] == if j < len { 0 } else { arr[j] }, "for_each over iter_mut: every element written");
        j += 1;
    }
}

// ---------------------------------------------------------------------------
// <[T; N] as IntoIterator>::into_iter   (array.rs: remaining == a@, yielded in order;
// peek_back reverses)
// ---------------------------------------------------------------------------

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(6)]
fn array_into_iter_yields_elements_in_order() {
    let a: [u8; 4] = kani::any();
    let mut it = a.into_iter();
    let mut i = 0usize;
    while i < 4 {
        assert!(it.next() == Some(a[i]), "array IntoIter: i-th element");
        i += 1;
    }
    assert!(it.next().is_none(), "array IntoIter: exhausted after N");
    let mut back = a.into_iter();
    assert!(back.next_back() == Some(a[3]), "array IntoIter: next_back is the last");
}

// ---------------------------------------------------------------------------
// Iterator::copied   (iter.rs: remaining == inner.remaining().map_values(|p| *p))
// ---------------------------------------------------------------------------

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(7)]
fn copied_matches_spec() {
    let (arr, len) = any_slice::<5>();
    let s = &arr[..len];
    let mut i = 0usize;
    for x in s.iter().copied() {
        assert!(i < s.len(), "copied: more items than the slice");
        assert!(x == s[i], "copied: item i equals s[i]");
        i += 1;
    }
    assert!(i == s.len(), "copied: fewer items than the slice");
    // memchr shapes: copied().skip(1) and rev().copied().skip(1)
    let mut j = 1usize;
    for x in s.iter().copied().skip(1) {
        assert!(x == s[j], "copied.skip(1)");
        j += 1;
    }
    let mut k = s.len();
    for x in s.iter().rev().copied().skip(1) {
        k -= 1;
        assert!(x == s[k - 1], "rev.copied.skip(1)");
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
    fn ascii_exhaustive_u8_and_char_bmp() {
        for b in 0u8..=255 {
            assert_eq!(b.is_ascii(), b < 128);
            assert_eq!(b.is_ascii_digit(), b'0' <= b && b <= b'9');
            assert_eq!(b.is_ascii_alphanumeric(), (b'0' <= b && b <= b'9') || (b'a' <= b && b <= b'z') || (b'A' <= b && b <= b'Z'));
            assert_eq!(b.is_ascii_whitespace(), b == b' ' || b == b'\t' || b == b'\n' || b == 0x0C || b == b'\r');
        }
        for u in 0u32..0x1_0000 {
            let Some(c) = char::from_u32(u) else { continue };
            assert_eq!(c.is_ascii(), u < 128);
            assert_eq!(c.is_ascii_digit(), '0' <= c && c <= '9');
            assert_eq!(c.is_ascii_hexdigit(), ('0' <= c && c <= '9') || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F'));
            assert_eq!(c.is_ascii_whitespace(), c == ' ' || c == '\t' || c == '\n' || c == '\u{C}' || c == '\r');
        }
    }

    #[test]
    fn rotate_bytes_chunks_exhaustive() {
        for x in [0u32, 1, 0x8000_0000, 0xdead_beef, u32::MAX] {
            for n in 0..70u32 {
                let r = n % 32;
                let left = if r == 0 { x } else { (x << r) | (x >> (32 - r)) };
                assert_eq!(x.rotate_left(n), left);
                let right = if r == 0 { x } else { (x >> r) | (x << (32 - r)) };
                assert_eq!(x.rotate_right(n), right);
            }
            let le = x.to_le_bytes();
            for i in 0..4u32 {
                assert_eq!(le[i as usize], byte_of(x as u128, i));
                assert_eq!(x.to_be_bytes()[i as usize], byte_of(x as u128, 3 - i));
            }
            assert_eq!(u32::from_le_bytes(le), x);
        }
        for s in all_slices(5) {
            for k in 1..=6usize {
                let got: Vec<Vec<u8>> = s.chunks_exact(k).map(|c| c.to_vec()).collect();
                let exp: Vec<Vec<u8>> = (0..s.len() / k).map(|i| s[i * k..(i + 1) * k].to_vec()).collect();
                assert_eq!(got, exp);
            }
        }
    }

    #[test]
    fn copied_exhaustive() {
        for s in all_slices(5) {
            let got: Vec<u8> = s.iter().copied().collect();
            assert_eq!(got, s);
            let tail: Vec<u8> = s.iter().copied().skip(1).collect();
            assert_eq!(tail, s.iter().skip(1).cloned().collect::<Vec<u8>>());
        }
    }

    #[test]
    fn by_mut_ref_next_exhaustive() {
        for s in all_slices(5) {
            for n in 0..=6usize {
                let mut direct = s.iter();
                let mut via_ref = s.iter();
                for _ in 0..n {
                    let d = direct.next();
                    let r = Iterator::next(&mut &mut via_ref);
                    assert_eq!(d, r);
                }
                assert_eq!(direct.len(), via_ref.len());
            }
            let mut it = s.iter();
            let mut count = 0;
            for _x in &mut it {
                count += 1;
            }
            assert_eq!(count, s.len());
            assert!(it.next().is_none());
            let mut it2 = s.iter();
            for _x in &mut it2 {
                break;
            }
            assert_eq!(it2.len(), s.len().saturating_sub(1));
        }
    }

    #[test]
    fn chunks_exact_mut_remainder_exhaustive() {
        for s in all_slices(5) {
            for k in 1..=5usize {
                for n in 0..=6usize {
                    let mut v = s.clone();
                    let mut it = v.chunks_exact_mut(k);
                    for _ in 0..n {
                        let _ = it.next();
                    }
                    let rem = it.into_remainder();
                    assert_eq!(rem.len(), s.len() % k);
                    assert_eq!(rem, &s[s.len() - s.len() % k..]);
                }
            }
        }
    }

    #[test]
    fn zip_take_next_exhaustive() {
        for a_s in all_slices(4) {
            for b_s in all_slices(4) {
                for n in 0..=6usize {
                    let mut a = a_s.iter();
                    let mut b = b_s.iter();
                    let (mut pa, mut pb) = (0usize, 0usize);
                    {
                        let mut z = a.by_ref().zip(b.by_ref());
                        for _ in 0..n {
                            let r = z.next();
                            let x = if pa < a_s.len() { pa += 1; Some(a_s[pa - 1]) } else { None };
                            let expected = match x {
                                None => None,
                                Some(xv) => {
                                    let y = if pb < b_s.len() { pb += 1; Some(b_s[pb - 1]) } else { None };
                                    y.map(|yv| (xv, yv))
                                }
                            };
                            assert_eq!(r.map(|(p, q)| (*p, *q)), expected);
                        }
                    }
                    assert_eq!(a.len(), a_s.len() - pa);
                    assert_eq!(b.len(), b_s.len() - pb);
                }
            }
            for k in 0..=5usize {
                for n in 0..=6usize {
                    let mut it = a_s.iter();
                    let (mut pos, mut count) = (0usize, k);
                    {
                        let mut t = it.by_ref().take(k);
                        for _ in 0..n {
                            let r = t.next();
                            let expected = if count > 0 {
                                count -= 1;
                                if pos < a_s.len() { pos += 1; Some(a_s[pos - 1]) } else { None }
                            } else {
                                None
                            };
                            assert_eq!(r.copied(), expected);
                        }
                    }
                    assert_eq!(it.len(), a_s.len() - pos);
                }
            }
        }
    }

    #[test]
    fn for_each_exhaustive() {
        for s in all_slices(5) {
            let mut seen = Vec::new();
            s.iter().for_each(|x| seen.push(*x));
            assert_eq!(seen, s);
            let mut v = s.clone();
            v.iter_mut().for_each(|x| *x = 0);
            assert!(v.iter().all(|x| *x == 0));
        }
    }

    #[test]
    fn array_into_iter_exhaustive() {
        for a in [[0u8, 1, 2, 3], [9, 9, 9, 9], [3, 1, 4, 1]] {
            let got: Vec<u8> = a.into_iter().collect();
            assert_eq!(got, a.to_vec());
            let back: Vec<u8> = a.into_iter().rev().collect();
            assert_eq!(back, a.iter().rev().cloned().collect::<Vec<u8>>());
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

/// vstd `std_specs/slice.rs`: `<[T]>::fill(value)` keeps the length, clones `value` into
/// all but the last element and moves it into the last (for `u8`, clone is the identity).
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(4)]
fn slice_fill_spec_holds() {
    let mut a: [u8; 3] = kani::any();
    let v: u8 = kani::any();
    let s: &mut [u8] = &mut a;
    s.fill(v);
    assert!(s.len() == 3);
    assert!(s[0] == v && s[1] == v && s[2] == v);
}

/// vstd `std_specs/option.rs` / `result.rs`: combinator specifications. The closure
/// stands for an arbitrary `f`: its ensures (`f.ensures(args, r)`) is `r == f(args)`, and
/// each assertion restates the vstd ensures under that reading.
#[cfg(kani)]
#[kani::proof]
fn option_result_combinator_specs_hold() {
    let o: Option<u8> = kani::any();
    let d: u8 = kani::any();
    let k: u8 = kani::any();
    let f = |x: u8| x.wrapping_mul(3) ^ k;
    // map_or
    let r = o.map_or(d, f);
    if o.is_none() { assert!(r == d) } else { assert!(r == f(o.unwrap())) }
    // map_or_else
    let r = o.map_or_else(|| d, f);
    if o.is_none() { assert!(r == d) } else { assert!(r == f(o.unwrap())) }
    // or_else
    let alt: Option<u8> = kani::any();
    let r = o.or_else(|| alt);
    if o.is_some() { assert!(r == o) } else { assert!(r == alt) }
    // filter
    let p = |x: &u8| (*x ^ k) & 1 == 0;
    let r = o.filter(p);
    if o.is_none() { assert!(r.is_none()) } else {
        assert!(r == o || r.is_none());
        assert!(r.is_some() == p(&o.unwrap()));
    }
    // is_some_and / is_none_or
    let q = |x: u8| x > k;
    let r = o.is_some_and(q);
    if o.is_none() { assert!(!r) } else { assert!(r == q(o.unwrap())) }
    let r = o.is_none_or(q);
    if o.is_none() { assert!(r) } else { assert!(r == q(o.unwrap())) }
    // copied
    let b: u8 = kani::any();
    let ro: Option<&u8> = if kani::any() { Some(&b) } else { None };
    let r = ro.copied();
    if ro.is_none() { assert!(r.is_none()) } else { assert!(r == Some(*ro.unwrap())) }
    // get_or_insert_with
    let mut m = o;
    let v = *m.get_or_insert_with(|| d);
    if o.is_some() { assert!(v == o.unwrap()) } else { assert!(v == d) }
    assert!(m == Some(v));
    // Result
    let res: Result<u8, u16> = if kani::any() { Ok(kani::any()) } else { Err(kani::any()) };
    let g = |x: u8| -> Result<u32, u16> { if x > k { Ok(x as u32 + 1) } else { Err(x as u16) } };
    let r = res.and_then(g);
    match res { Err(e) => assert!(r == Err(e)), Ok(x) => assert!(r == g(x)) }
    let h = |e: u16| -> Result<u8, u32> { if e > 5 { Ok(e as u8) } else { Err(e as u32) } };
    let r = res.or_else(h);
    match res { Ok(x) => assert!(r == Ok(x)), Err(e) => assert!(r == h(e)) }
    let r = res.unwrap_or(d);
    match res { Ok(x) => assert!(r == x), Err(_) => assert!(r == d) }
    let u = |e: u16| e as u8;
    let r = res.unwrap_or_else(u);
    match res { Ok(x) => assert!(r == x), Err(e) => assert!(r == u(e)) }
    let r = res.unwrap_or_default();
    match res { Ok(x) => assert!(r == x), Err(_) => assert!(r == 0) }
    let r = res.map_or(d, f);
    match res { Err(_) => assert!(r == d), Ok(x) => assert!(r == f(x)) }
}

/// vstd `std_specs/iter.rs`: `enumerate()`'s `remaining` is the inner iterator's with each
/// item paired with its position: `i.remaining().map(|k, x| (k as usize, x))`.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn enumerate_spec_holds() {
    let a: [u8; 3] = kani::any();
    let mut n = 0usize;
    for (k, x) in a.iter().enumerate() {
        assert!(k == n);
        assert!(*x == a[n]);
        n += 1;
    }
    assert!(n == 3);
}

/// vstd `core.rs`, `slice.rs`, `raw_ptr.rs`: `mem::replace`/`take`, `<[T]>::swap`/`reverse`/
/// `contains`/`to_vec`, `<*mut T>::cast`/`is_null`.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn mem_slice_ptr_specs_hold() {
    let x0: u8 = kani::any();
    let src: u8 = kani::any();
    let mut x = x0;
    let r = core::mem::replace(&mut x, src);
    assert!(r == x0 && x == src);
    let mut y = x0;
    let r = core::mem::take(&mut y);
    assert!(r == x0 && y == 0);
    let a0: [u8; 3] = kani::any();
    let i: usize = kani::any();
    let j: usize = kani::any();
    kani::assume(i < 3 && j < 3);
    let mut a = a0;
    a.swap(i, j);
    for k in 0..3 {
        let expected = if k == j { a0[i] } else if k == i { a0[j] } else { a0[k] };
        assert!(a[k] == expected);
    }
    let mut b = a0;
    b.reverse();
    assert!(b[0] == a0[2] && b[1] == a0[1] && b[2] == a0[0]);
    let q: u8 = kani::any();
    assert!(a0.contains(&q) == (a0[0] == q || a0[1] == q || a0[2] == q));
    let v = a0[..].to_vec();
    assert!(v.len() == 3 && v[0] == a0[0] && v[1] == a0[1] && v[2] == a0[2]);
    let addr: usize = kani::any();
    let p = core::ptr::without_provenance_mut::<u32>(addr);
    assert!(p.cast::<u8>().addr() == p.addr());
    assert!(p.is_null() == (p.addr() == 0));
}

/// vstd `iter.rs`: `cloned()` yields a clone of each referenced item, in order; a fresh
/// `peekable()` yields the inner sequence, and `peek` returns the next item without
/// consuming it.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn cloned_peekable_specs_hold() {
    let a: [u8; 3] = kani::any();
    let mut n = 0usize;
    for x in a.iter().cloned() {
        assert!(x == a[n]);
        n += 1;
    }
    assert!(n == 3);
    let mut p = a.iter().peekable();
    for k in 0..3 {
        let q = p.peek().map(|r| **r);
        assert!(q == Some(a[k]));
        let q2 = p.peek().map(|r| **r);
        assert!(q2 == Some(a[k]));
        assert!(p.next() == Some(&a[k]));
    }
    assert!(p.peek().is_none());
    assert!(p.next().is_none());
}

/// vstd `vec.rs`: `Vec::extend` appends the items of the iterator (owned) or copies of them
/// (by reference, `T: Copy`).
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn vec_extend_spec_holds() {
    let a: [u8; 2] = kani::any();
    let b: [u8; 2] = kani::any();
    let mut v: Vec<u8> = a.to_vec();
    v.extend(b.iter());
    assert!(v.len() == 4 && v[0] == a[0] && v[1] == a[1] && v[2] == b[0] && v[3] == b[1]);
    let mut w: Vec<u8> = a.to_vec();
    w.extend(b.to_vec().into_iter());
    assert!(w == v);
}

/// vstd: `char::from_u32` is Some exactly for Unicode scalar values; `str::bytes` yields the
/// UTF-8 encoding; `Vec::capacity >= len`; `into_boxed_slice` keeps the elements.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn char_bytes_vec_misc_specs_hold() {
    let i: u32 = kani::any();
    let c = char::from_u32(i);
    assert!(c.is_some() == (i <= 0xD7FF || (0xE000 <= i && i <= 0x10FFFF)));
    if let Some(ch) = c { assert!(ch as u32 == i); }
    let a: [u8; 2] = kani::any();
    kani::assume(a[0].is_ascii() && a[1].is_ascii());
    let s = core::str::from_utf8(&a).unwrap();
    let mut n = 0;
    for b in s.bytes() { assert!(b == a[n]); n += 1; }
    assert!(n == 2);
    let v: Vec<u8> = a.to_vec();
    assert!(v.capacity() >= v.len());
    let bx = v.clone().into_boxed_slice();
    assert!(bx.len() == 2 && bx[0] == a[0] && bx[1] == a[1]);
}


/// vstd `std_specs/time.rs`: `Duration` modelled by `duration_nanos`; here
/// `duration_nanos(d) = d.as_nanos()`, and each assertion restates a vstd ensures clause.
#[cfg(kani)]
#[kani::proof]
fn duration_specs_hold() {
    use core::time::Duration;
    // duration_nanos(d) = secs * 10^9 + nanos (nanos < 10^9), so each clause is checked on the
    // (secs, nanos) pair, which keeps 128-bit products out of the solver's problem.
    let s: u64 = kani::any();
    let m: u64 = kani::any();
    let d = Duration::from_secs(s);
    assert!(d.as_secs() == s && d.subsec_nanos() == 0);
    let e = Duration::from_millis(m);
    assert!(e.as_secs() == m / 1000 && e.subsec_nanos() as u64 == (m % 1000) * 1_000_000);
    let secs: u64 = kani::any();
    let sub: u32 = kani::any();
    kani::assume(sub < 1_000_000_000);
    let x = Duration::new(secs, sub);
    assert!(x.as_secs() == secs && x.subsec_nanos() == sub);
    assert!(x.as_millis() == secs as u128 * 1000 + (sub / 1_000_000) as u128);
    assert!(x.is_zero() == (secs == 0 && sub == 0));
    let secs2: u64 = kani::any();
    let sub2: u32 = kani::any();
    kani::assume(sub2 < 1_000_000_000);
    let y = Duration::new(secs2, sub2);
    let r = x.saturating_add(y);
    let carry = (sub + sub2 >= 1_000_000_000) as u64;
    let ns = if carry == 1 { sub + sub2 - 1_000_000_000 } else { sub + sub2 };
    match secs.checked_add(secs2).and_then(|t| t.checked_add(carry)) {
        Some(t) => assert!(r.as_secs() == t && r.subsec_nanos() == ns),
        None => assert!(r.as_secs() == u64::MAX && r.subsec_nanos() == 999_999_999),
    }
}

/// vstd `std_specs/core.rs` `bool::then_some`, `std_specs/option.rs` `Option::transpose`,
/// `string`'s `String::with_capacity`.
#[cfg(kani)]
#[kani::proof]
fn then_some_transpose_with_capacity_hold() {
    let b: bool = kani::any();
    let x: u8 = kani::any();
    let r = b.then_some(x);
    assert!(r == if b { Some(x) } else { None });
    let o: Option<Result<u8, u16>> = match kani::any::<u8>() % 3 {
        0 => None,
        1 => Some(Ok(kani::any())),
        _ => Some(Err(kani::any())),
    };
    let t = o.transpose();
    match o {
        None => assert!(t == Ok(None)),
        Some(Ok(v)) => assert!(t == Ok(Some(v))),
        Some(Err(e)) => assert!(t == Err(e)),
    }
    let n: usize = kani::any();
    kani::assume(n <= 8);
    let s = String::with_capacity(n);
    assert!(s.is_empty());
}

/// vstd `std_specs/result.rs` `Result::and`.
#[cfg(kani)]
#[kani::proof]
fn result_and_holds() {
    let r: Result<u8, u16> = if kani::any() { Ok(kani::any()) } else { Err(kani::any()) };
    let s: Result<u32, u16> = if kani::any() { Ok(kani::any()) } else { Err(kani::any()) };
    let a = r.and(s);
    match r { Ok(_) => assert!(a == s), Err(e) => assert!(a == Err(e)) }
}

/// vstd `std_specs/time.rs` `Duration::ZERO`, `saturating_sub`. (`Entry::or_default` is tested
/// by `entry_or_default_exec` below: map search does not unwind under Kani.)
#[cfg(kani)]
#[kani::proof]
fn duration_zero_saturating_sub_hold() {
    use core::time::Duration;
    assert!(Duration::ZERO.as_nanos() == 0);
    let (s1, n1, s2, n2): (u64, u32, u64, u32) = (kani::any(), kani::any(), kani::any(), kani::any());
    kani::assume(n1 < 1_000_000_000 && n2 < 1_000_000_000);
    let (a, b) = (Duration::new(s1, n1), Duration::new(s2, n2));
    let r = a.saturating_sub(b);
    // duration_nanos(d) = secs * 10^9 + nanos with nanos < 10^9, so the nanosecond statement is
    // the lexicographic one on (secs, nanos); stated that way to keep 128-bit products out of
    // the solver's problem.
    let ge = (s1, n1) >= (s2, n2);
    let (es, en) = if !ge { (0, 0) } else if n1 >= n2 { (s1 - s2, n1 - n2) } else { (s1 - s2 - 1, n1 + 1_000_000_000 - n2) };
    assert!(r.as_secs() == es && r.subsec_nanos() == en);
}

/// `Entry::or_default`, executed exhaustively over small maps (ordinary `cargo test`).
#[cfg(test)]
#[test]
fn entry_or_default_exec() {
    use std::collections::HashMap;
    for had in [None, Some(0u64), Some(7)] {
        for k in 0u8..4 {
            let mut m: HashMap<u8, u64> = HashMap::new();
            m.insert(9, 1);
            if let Some(x) = had { m.insert(k, x); }
            let before = m.clone();
            let v = m.entry(k).or_default();
            let got = *v;
            *v = got + 1;
            if let Some(x) = had { assert_eq!(got, x); }
            let mut e = before.clone(); e.insert(k, got + 1);
            assert_eq!(m, e);
        }
    }
}

/// vstd `std_specs/iter.rs`: `count`, `position`, `find_map`, `max`, `min` on a slice iterator
/// of length 3 (`remaining` = the slice), and `sum` of `u8`/`&u8`: no panic when every prefix
/// sum fits, and then the exact sum; a panic otherwise (the precondition is necessary).
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn iterator_consumers_hold() {
    let a: [u8; 3] = kani::any();
    let x: u8 = kani::any();
    assert!(a.iter().count() == 3);
    // position: the first index whose item satisfies the predicate; the iterator then holds
    // the items after it
    let mut it = a.iter();
    let p = it.position(|y| *y == x);
    match p {
        None => assert!(a[0] != x && a[1] != x && a[2] != x && it.len() == 0),
        Some(i) => {
            assert!(i < 3 && a[i] == x && (0..i).all(|j| a[j] != x));
            assert!(it.len() == 3 - i - 1);
        }
    }
    // find_map
    let mut it = a.iter();
    let f = |y: &u8| if *y > x { Some(*y - x) } else { None };
    let r = it.find_map(f);
    match r {
        None => assert!(a.iter().all(|y| f(y).is_none()) && it.len() == 0),
        Some(v) => { let idx = 3 - it.len() - 1; assert!(f(&a[idx]) == Some(v) && (0..idx).all(|j| f(&a[j]).is_none())); }
    }
    // max / min: one of the items, and no item compares greater / less
    let m = *a.iter().max().unwrap();
    assert!(a.contains(&m) && a.iter().all(|y| *y <= m));
    let n = *a.iter().min().unwrap();
    assert!(a.contains(&n) && a.iter().all(|y| *y >= n));
    let e: [u8; 0] = [];
    assert!(e.iter().max().is_none() && e.iter().min().is_none() && e.iter().count() == 0);
    // sum: prefix sums in range => exact
    let s0 = a[0] as u32; let s1 = s0 + a[1] as u32; let s2 = s1 + a[2] as u32;
    if s1 <= 255 && s2 <= 255 {
        let r: u8 = a.iter().sum();
        assert!(r as u32 == s2);
        let r2: u8 = a.into_iter().sum();
        assert!(r2 as u32 == s2);
    }
}

/// `sum` overflowing a prefix panics (debug build): the `sum_req` precondition is not
/// vacuous. Kani reports the overflow as a failed check, so this harness is expected to fail.
#[cfg(kani)]
#[kani::proof]
#[kani::should_panic]
fn iterator_sum_overflow_panics() {
    let a: [u8; 2] = [200, 100];
    let r: u8 = a.iter().sum();
    let _ = r;
}

/// vstd `std_specs/extra.rs`: `Option::flatten`/`zip`, `array::map`, `pow` (u8, inside the
/// precondition), `u8::is_ascii_hexdigit`, `Duration::saturating_mul`.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(9)]
fn extra_specs_hold() {
    let o: Option<Option<u8>> = match kani::any::<u8>() % 3 { 0 => None, 1 => Some(None), _ => Some(Some(kani::any())) };
    assert!(o.flatten() == match o { Some(Some(x)) => Some(x), _ => None });
    let a: Option<u8> = if kani::any() { Some(kani::any()) } else { None };
    let b: Option<u16> = if kani::any() { Some(kani::any()) } else { None };
    assert!(a.zip(b) == match (a, b) { (Some(x), Some(y)) => Some((x, y)), _ => None });
    let arr: [u8; 3] = kani::any();
    let k: u8 = kani::any();
    let m = arr.map(|x: u8| x ^ k);
    assert!(m[0] == arr[0] ^ k && m[1] == arr[1] ^ k && m[2] == arr[2] ^ k);
    let c: u8 = kani::any();
    assert!(c.is_ascii_hexdigit() == ((0x30 <= c && c <= 0x39) || (0x41 <= c && c <= 0x46) || (0x61 <= c && c <= 0x66)));
}

/// `u8::pow` inside the precondition is the exact power.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(9)]
fn pow_in_range_exact() {
    let x: u8 = kani::any(); let e: u32 = kani::any(); kani::assume(e < 9);
    let mut exact: u16 = 1; let mut i = 0;
    while i < e && exact <= 255 { exact = exact * x as u16; i += 1; }
    if i == e && exact <= 255 { assert!(x.pow(e) as u16 == exact); }
}

/// `Duration::saturating_mul` without saturation: the exact product, stated on (secs, nanos)
/// (no 128-bit products). Saturation is the `checked_mul` fallback (`Duration::MAX`).
#[cfg(kani)]
#[kani::proof]
fn duration_saturating_mul_exact() {
    let (secs, nanos, k): (u64, u32, u32) = (kani::any(), kani::any(), kani::any());
    kani::assume(nanos < 1_000_000_000 && secs < 1 << 8 && k < 1 << 4);
    let d = core::time::Duration::new(secs, nanos).saturating_mul(k);
    let total_n = nanos as u64 * k as u64;
    assert!(d.subsec_nanos() as u64 == total_n % 1_000_000_000);
    assert!(d.as_secs() == secs * k as u64 + total_n / 1_000_000_000);
    let m = core::time::Duration::MAX.saturating_mul(2 + k);
    assert!(m == core::time::Duration::MAX);
}

/// `VecDeque::front`/`front_mut`; `String::len`/`as_bytes` are the UTF-8 encoding.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn extra_container_specs_hold() {
    let mut d: std::collections::VecDeque<u8> = std::collections::VecDeque::with_capacity(4);
    let n: u8 = kani::any(); kani::assume(n < 3);
    let mut i = 0; while i < n { d.push_back(i + 10); i += 1; }
    assert!(d.front() == if n > 0 { Some(&10u8) } else { None });
    let w: u8 = kani::any();
    if let Some(y) = d.front_mut() { *y = w; }
    if n > 0 { assert!(d.len() == n as usize && d[0] == w && (1..d.len()).all(|j| d[j] == 10 + j as u8)); } else { assert!(d.is_empty()); }
    let ch: char = kani::any();
    let mut s = String::with_capacity(4);
    s.push(ch);
    let mut buf = [0u8; 4];
    let enc: &[u8] = ch.encode_utf8(&mut buf).as_bytes();
    assert!(s.len() == ch.len_utf8() && s.as_bytes().len() == enc.len());
    assert!(s.as_bytes()[0] == enc[0]);
}

/// `sort`, `sort_unstable`, `sort_by`, `sort_by_key`, `sort_unstable_by(_key)`: a permutation
/// (same length, same multiset), sorted for `sort`/`sort_unstable`; `binary_search`.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn slice_sort_specs_hold() {
    let a: [u8; 3] = kani::any();
    let count = |s: &[u8], v: u8| s.iter().filter(|x| **x == v).count();
    let perm = |s: &[u8]| s.len() == 3 && (0..3).all(|i| count(s, a[i]) == count(&a, a[i]));
    let mut s = a; s.sort();
    assert!(perm(&s) && s[0] <= s[1] && s[1] <= s[2]);
    let mut s = a; s.sort_unstable();
    assert!(perm(&s) && s[0] <= s[1] && s[1] <= s[2]);
    let mut s = a; s.sort_by(|x, y| y.cmp(x));
    assert!(perm(&s));
    let mut s = a; s.sort_unstable_by(|x, y| y.cmp(x));
    assert!(perm(&s));
    let mut s = a; s.sort_by_key(|x| *x / 2);
    assert!(perm(&s));
    let mut s = a; s.sort_unstable_by_key(|x| *x % 3);
    assert!(perm(&s));
    let mut s = a; s.sort();
    let x: u8 = kani::any();
    match s.binary_search(&x) { Ok(i) => assert!(i < 3 && s[i] == x), Err(i) => assert!(i <= 3) }
}

/// `HashMap::get_mut` (HashMap search does not unwind under Kani): for every map over keys
/// {0,1,2} with values in {0,1} and every key, `None` iff absent (map unchanged); `Some(v)`
/// with `*v` the old value, and writing `w` through it is `insert(k, w)`.
#[cfg(test)]
#[test]
fn hashmap_get_mut_exec() {
    use std::collections::HashMap;
    for mask in 0..27u32 {
        let mut base = HashMap::new();
        let mut m2 = mask;
        for k in 0..3u64 { match m2 % 3 { 0 => {}, d => { base.insert(k, d as u64 - 1); } } m2 /= 3; }
        for k in 0..4u64 {
            let mut m = base.clone();
            match m.get_mut(&k) {
                None => { assert!(!base.contains_key(&k)); assert!(m == base); }
                Some(v) => {
                    assert!(base.get(&k) == Some(v));
                    *v = 9;
                    let mut exp = base.clone(); exp.insert(k, 9);
                    assert!(m == exp);
                }
            }
        }
    }
}

/// `iter::once(v)` yields exactly `v`; `max_by_key` returns an element of the iterator.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn once_and_max_by_key_hold() {
    let v: u8 = kani::any();
    let mut it = core::iter::once(v);
    assert!(it.next() == Some(v) && it.next().is_none());
    let a: [u8; 3] = kani::any();
    let k: u8 = kani::any();
    let m = *a.iter().max_by_key(|x| **x ^ k).unwrap();
    assert!(a.contains(&m));
}

/// S27: `String::from(&str)` copies the characters; `slice::from_ref(x)` is `[*x]`;
/// `Vec::dedup` does not grow the vector and keeps a non-empty one non-empty;
/// `NonZero::<u64>::MIN` is 1.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn s27_specs_hold() {
    let c: char = kani::any();
    let mut buf = [0u8; 4];
    let s: &str = c.encode_utf8(&mut buf);
    let t = String::from(s);
    assert!(t.len() == s.len() && t.chars().next() == Some(c));
    let x: u8 = kani::any();
    let r = core::slice::from_ref(&x);
    assert!(r.len() == 1 && r[0] == x);
    let a: [u8; 3] = kani::any();
    let mut v = a.to_vec();
    v.dedup();
    assert!(v.len() <= 3 && v.len() > 0 && v[0] == a[0]);
    assert!(core::num::NonZeroU64::MIN.get() == 1 && core::num::NonZeroU8::MIN.get() == 1);
}

/// S28: `Result::as_mut` keeps the variant and writes through to the payload;
/// `Duration::subsec_nanos` is the total nanoseconds mod 10^9 (stated on (secs, nanos));
/// `Duration::MAX` is (u64::MAX, 10^9 - 1).
#[cfg(kani)]
#[kani::proof]
fn s28_specs_hold() {
    let ok: bool = kani::any();
    let v: u8 = kani::any();
    let w: u8 = kani::any();
    let mut r: Result<u8, u8> = if ok { Ok(v) } else { Err(v) };
    match r.as_mut() {
        Ok(x) => { assert!(ok && *x == v); *x = w; }
        Err(e) => { assert!(!ok && *e == v); *e = w; }
    }
    assert!(r == if ok { Ok(w) } else { Err(w) });
    let (secs, nanos): (u64, u32) = (kani::any(), kani::any());
    kani::assume(nanos < 1_000_000_000);
    let d = core::time::Duration::new(secs, nanos);
    assert!(d.subsec_nanos() == nanos);
    assert!(core::time::Duration::MAX.as_secs() == u64::MAX && core::time::Duration::MAX.subsec_nanos() == 999_999_999);
}

/// S28: `Box::pin(x)` holds `x` (vstd: `*r.pointer() == x`).
#[cfg(kani)]
#[kani::proof]
fn box_pin_holds() {
    let x: u64 = kani::any();
    let p: core::pin::Pin<Box<u64>> = Box::pin(x);
    assert!(*p == x);
    let p2: core::pin::Pin<Box<u64>> = Box::pin(x);
    assert!(*core::pin::Pin::into_inner(p2) == x);
}

/// `From<bool>` for the integer types: 1 for true, 0 for false (vstd `from_spec`).
#[cfg(kani)]
#[kani::proof]
fn from_bool_holds() {
    let b: bool = kani::any();
    let e: u8 = if b { 1 } else { 0 };
    assert!(u8::from(b) == e && u16::from(b) == e as u16 && u32::from(b) == e as u32);
    assert!(u64::from(b) == e as u64 && usize::from(b) == e as usize && u128::from(b) == e as u128);
    assert!(i8::from(b) == e as i8 && i16::from(b) == e as i16 && i32::from(b) == e as i32);
    assert!(i64::from(b) == e as i64 && isize::from(b) == e as isize && i128::from(b) == e as i128);
}

/// `<[T; N]>::try_from(&[T])` and `<&[T; N]>::try_from(&[T])`: Ok exactly when
/// `len == N`, with the slice's elements (vstd `try_from_spec`, `spec_array_from_seq`).
#[cfg(kani)]
#[kani::proof]
fn array_try_from_slice_holds() {
    let buf: [u8; 4] = kani::any();
    let n: usize = kani::any();
    kani::assume(n <= 4);
    let s = &buf[..n];
    let r: Result<[u8; 2], _> = s.try_into();
    assert!(r.is_ok() == (n == 2));
    if let Ok(a) = r {
        assert!(a[0] == buf[0] && a[1] == buf[1]);
    }
    let q: Result<&[u8; 3], _> = s.try_into();
    assert!(q.is_ok() == (n == 3));
    if let Ok(a) = q {
        assert!(a[0] == buf[0] && a[1] == buf[1] && a[2] == buf[2]);
    }
}

/// `overflowing_add`/`overflowing_sub` on unsigned integers: the wrapping result and
/// whether the exact result is out of range (vstd: `(wrapping_*(x, y), x + y > MAX)`,
/// `(wrapping_sub(x, y), x < y)`).
#[cfg(kani)]
#[kani::proof]
fn overflowing_unsigned_holds() {
    let x: u8 = kani::any();
    let y: u8 = kani::any();
    assert!(x.overflowing_add(y) == (x.wrapping_add(y), (x as u16) + (y as u16) > u8::MAX as u16));
    assert!(x.overflowing_sub(y) == (x.wrapping_sub(y), x < y));
    let a: u64 = kani::any();
    let b: u64 = kani::any();
    assert!(a.overflowing_add(b) == (a.wrapping_add(b), (a as u128) + (b as u128) > u64::MAX as u128));
    assert!(a.overflowing_sub(b) == (a.wrapping_sub(b), a < b));
}
