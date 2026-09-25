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
