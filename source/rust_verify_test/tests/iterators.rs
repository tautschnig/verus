#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] all_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(v: Vec<u32>)
        {
            let mut it = v.into_iter();
            let ghost g = it;
            let v_result = it.all(
                |i: u32| -> (ret: bool)
                    ensures ret == (i < 10)
                {i < 10}
            );
            if v_result {
                // If `all` returned true, every element was below 10.
                assert(forall |i| 0 <= i < v.len() ==> v[i] < 10);
            } else {
                // If `all` returned false, at least one element was >= 10.
                // The witness is the (consumed) element that failed the predicate.
                let ghost idx = g.remaining().len() - it.remaining().len() - 1;
                assert(0 <= idx < v.len() && v[idx] >= 10);
                assert(exists |i| 0 <= i < v.len() && v[i] >= 10);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] any_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(v: Vec<u32>)
        {
            let mut it = v.into_iter();
            let ghost g = it;
            let v_result = it.any(
                |i: u32| -> (ret: bool)
                    ensures ret == (i < 10)
                {i < 10}
            );
            if v_result {
                // If `any` returned true, at least one element was below 10.
                // The witness is the (consumed) element that satisfied the predicate.
                let ghost idx = g.remaining().len() - it.remaining().len() - 1;
                assert(0 <= idx < v.len() && v[idx] < 10);
                assert(exists |i| 0 <= i < v.len() && v[i] < 10);
            } else {
                // If `any` returned false, every element was >= 10.
                assert(forall |i| 0 <= i < v.len() ==> v[i] >= 10);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] chars_next_falls_back_to_iterator_spec verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(s: &str)
            requires
                s@.len() >= 1,
        {
            let mut it = s.chars();
            assert(it.remaining() == s@);
            let r = it.next();
            assert(r == Some(s@[0]));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] collect_works verus_code! {
        use vstd::prelude::*;

        fn test() {
            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = v.into_iter().collect();
            assert(v@ == w@);
            let x: Vec<u32> = w.into_iter().rev().collect();
            assert(x@ == seq![4u32, 3, 2, 1]);

            let y: Vec<u32> = vec![1, 2, 3, 4];
            let z: Vec<u32> = y.into_iter().rev().rev().collect();
            assert(z@ == y@);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] filter_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::*;

        fn test() {
            let p = |x: &u32| -> (b: bool)
                ensures b == (*x % 2 == 0)
            { *x % 2 == 0 };

            let v: Vec<u32> = vec![1, 2, 3, 4];
            let mut w: Vec<u32> = Vec::new();

            for x in it: v.into_iter().filter(p)
                invariant
                    w.len() == it.index(),
                    forall |i| 0 <= i < w.len() ==> w[i] == it.seq()[i],
            {
                w.push(x);
            }
            assert(w.len() <= 4);
            assert(forall |i| 0 <= i < w.len() ==> w[i] % 2 == 0);
            assert(forall |i| #![auto] 0 <= i < w.len() ==> v@.contains(w[i]));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] find_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(v: Vec<u32>)
        {
            let v_result = v.into_iter().find(
                |i| -> (ret: bool)
                ensures ret == (*i < 10)
                {*i < 10}
            );
            if let Some(i) = v_result {
                assert(i < 10);
                assert(v@.contains(i));
            } else {
                assert(forall |i| 0 <= i < v.len() ==> v[i] >= 10);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] map_works verus_code! {
        use vstd::prelude::*;

        fn double_it() {
            let v = vec![1u32, 2, 3, 4];
            let mut w = Vec::new();
            for x in iter: v.iter().map(|x: &u32| -> (y: u32) requires *x < 10, ensures y == x * 2 { *x * 2 })
                invariant
                    w.len() == iter.index(),
                    forall |i| 0 <= i < w.len() ==> w[i] == v[i] * 2,
            {
                w.push(x);
            }
            assert(w@ == seq![2u32, 4, 6, 8]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mut_ref_forwarding verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        pub fn next_test<I: Iterator>(i: &mut I)
            requires
                i.obeys_prophetic_iter_laws(),
                i.will_return_none(),
            ensures
                // TODO: The number of operators needed here is unfortunate
                (&(*final(i))).obeys_prophetic_iter_laws(),
                (&(*final(i))).will_return_none(),
        {
            i.next();

        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] range_works verus_code! {
        use vstd::prelude::*;

        fn test()
        {
            let mut v = vec![];
            for i in iter: 0..4
            invariant
                v.len() == iter.index(),
                iter.index() <= 4,
            {
                assert(i < 4);
                v.push(i);
            }
            assert(v.len() == 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] range_inclusive_works verus_code! {
        use vstd::prelude::*;

        fn test()
        {
            let mut v = vec![];
            for i in iter: 0..=4
            invariant
                v.len() == iter.index(),
                i <= 5,
            {
                assert(i <= 4);
                v.push(i);
            }
            assert(v.len() == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] skip_works verus_code! {
        use vstd::prelude::*;

        fn test() {
            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = v.into_iter().skip(2).collect();
            assert(w@ == seq![3, 4]);


            let v: Vec<u32> = vec![1, 2, 3, 4];
            let mut w: Vec<u32> = Vec::new();

            for x in it: v.into_iter().skip(2)
                invariant
                    w.len() == it.index(),
                    forall |i| 0 <= i < w.len() ==> w[i] == it.seq()[i],
            {
                w.push(x);
            }
            assert(w@ == seq![3, 4]);

            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = v.into_iter().skip(2).rev().collect();
            assert(w@ == seq![4u32, 3]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] take_works verus_code! {
        use vstd::prelude::*;

        fn test() {
            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = v.into_iter().take(2).collect();
            assert(w@ == seq![1, 2]);


            let v: Vec<u32> = vec![1, 2, 3, 4];
            let mut w: Vec<u32> = Vec::new();

            for x in it: v.into_iter().take(3)
                invariant
                    w.len() == it.index(),
                    forall |i| 0 <= i < w.len() ==> w[i] == it.seq()[i],
            {
                w.push(x);
            }
            assert(w@ == seq![1, 2, 3]);

            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = v.into_iter().take(2).rev().collect();
            assert(w@ == seq![2u32, 1]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] take_skip verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test<I: Iterator>(v: Vec<u32>, n: usize)
            requires
                n <= v.len(),
        {
            // Creusot:
            //   assert!(iter.take(n).skip(n).next().is_none())
            // Verus:
            let mut r = v.into_iter().take(n).skip(n);
            assert(r.remaining().len() == 0);
            let out = r.next();
            assert(out is None);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] vec_iter_mut_works verus_code! {
        use vstd::prelude::*;

        fn client_for_loop() {
            let mut v: Vec<u32> = vec![1, 2, 3, 4];
            for x in it: v.iter_mut()
                invariant
                    forall |i: int| #![auto] 0 <= i < it.index() ==> *final(it.seq()[i]) == 0,
            {
                *x = 0;
            }
            assert(forall |i: int| 0 <= i < v.len() ==> v[i] == 0);
            assert(v@ == seq![0, 0, 0, 0]);
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] zip_works verus_code! {
        use vstd::prelude::*;

        fn zip_works() {
            let x1 = vec![1u32, 2, 3];
            let x2 = vec![2u32, 4, 6];
            let y1 = vec![2u32, 4, 6];
            let y2 = vec![1u32, 2];
            let z1 = vec![1u32, 2];
            let z2 = vec![2u32, 4, 6, 8, 10];

            let x: Vec<(u32, u32)> = x1.into_iter().zip(x2).collect();
            assert(x@ == seq![(1u32,2u32), (2, 4), (3, 6)]);

            let y: Vec<(u32, u32)> = y1.into_iter().zip(y2).collect();
            assert(y@ == seq![(2u32,1u32), (4, 2)]);

            let z: Vec<(u32, u32)> = z1.into_iter().zip(z2).collect();
            assert(z@ == seq![(1u32,2u32), (2, 4)]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] slice_windows_spec verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;
        use vstd::std_specs::slice::spec_windows;

        spec fn asc_count(s: Seq<u64>, upto: int) -> int
            decreases upto
        {
            if upto <= 0 { 0int } else { asc_count(s, upto - 1) + (if s[upto - 1] <= s[upto] { 1int } else { 0int }) }
        }

        fn count_ascending_pairs(s: &[u64]) -> (r: usize)
            requires s.len() >= 1,
            ensures r == asc_count(s@, s.len() - 1),
        {
            let mut r: usize = 0;
            for w in it: s.windows(2)
                invariant
                    it.seq().len() == s.len() - 1,
                    forall|i: int| 0 <= i < it.seq().len() ==> (#[trigger] it.seq()[i])@ == s@.subrange(i, i + 2),
                    r == asc_count(s@, it.index()),
                    r <= it.index(),
                    it.index() <= s.len() - 1,
            {
                assert(w@ == s@.subrange(it.index(), it.index() + 2));
                if w[0] <= w[1] { r = r + 1; }
            }
            r
        }

        fn windows_facts(s: &[u64])
            requires s.len() >= 2,
        {
            let w = s.windows(2);
            assert(w.remaining().len() == s.len() - 1);
            assert(w.remaining()[0]@ == s@.subrange(0, 2));
            assert(spec_windows(s@, 2)[0] == s@.subrange(0, 2));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] slice_windows_zero_fails verus_code! {
        use vstd::prelude::*;
        fn windows_zero_size(s: &[u64]) {
            let _w = s.windows(0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] slice_chunks_spec verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;
        use vstd::std_specs::slice::spec_chunks;

        fn chunk_facts(s: &[u64], idx: Ghost<int>)
            requires s.len() == 5, 0 <= idx@ < 3,
        {
            let c = s.chunks(2);
            assert(c.remaining().len() == 3);
            assert(spec_chunks(s@, 2)[idx@] == s@.subrange(idx@ * 2, if (idx@ + 1) * 2 <= 5 { (idx@ + 1) * 2 } else { 5 }));
            assert(c.remaining()[2]@ == s@.subrange(4, 5));
        }

        fn chunks_zero_size(s: &[u64]) {
            let _c = s.chunks(0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] flat_map_spec verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::{IteratorSpec, flat_map_parts};

        fn count_all(vs: &Vec<Vec<u64>>) -> (s: u64)
            requires vs.len() <= 100,
        {
            let mut s: u64 = 0;
            for _x in vs.iter().flat_map(|inner: &Vec<u64>| inner.iter())
                invariant s <= 100,
            {
                s = if s < 100 { s + 1 } else { s };
            }
            s
        }

        fn facts(v: &Vec<u64>)
            requires v.len() == 2,
        {
            let fm = v.iter().flat_map(|x: &u64| vec![*x, *x]);
            assert(flat_map_parts(fm).len() == 2);
            assert(fm.remaining() == flat_map_parts(fm).flatten());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] chain_spec verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn collect_chain() {
            let a = vec![1u32, 2];
            let b = vec![3u32];
            let c: Vec<u32> = a.into_iter().chain(b).collect();
            assert(c@ == seq![1u32, 2, 3]);
        }

        fn order(a: &Vec<u64>, b: &Vec<u64>)
            requires a.len() == 1, b.len() == 1,
        {
            let c = a.iter().chain(b.iter());
            assert(c.remaining().len() == 2);
            assert(*c.remaining()[0] == a[0]);
            assert(*c.remaining()[1] == b[0]);
        }
    } => Ok(())
}

test_verify_one_file! {
    // A for loop over a Chain gets the wrapper's index and element facts
    #[test] chain_for_loop verus_code! {
        use vstd::prelude::*;
        fn concat(a: &Vec<u8>, b: &Vec<u8>) -> (r: Vec<u8>)
            ensures r@ == a@ + b@,
        {
            let mut out: Vec<u8> = Vec::new();
            for x in it: a.iter().chain(b.iter())
                invariant
                    it.seq().len() == a@.len() + b@.len(),
                    forall|i| 0 <= i < it.seq().len() ==> #[trigger] it.seq()[i] == (a@ + b@)[i],
                    out@ == it.seq().subrange(0, it.index()).map_values(|p: &u8| *p),
            {
                out.push(*x);
            }
            assert(out@ =~= a@ + b@);
            out
        }
    } => Ok(())
}

test_verify_one_file! {
    // `copied()` over a slice iterator, including the `skip(1)` and `rev()` shapes memchr uses
    #[test] copied_spec verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;
        fn next_facts(v: &Vec<u8>) requires v@.len() >= 1 {
            let mut c = v.iter().copied();
            let ghost r0 = IteratorSpec::remaining(&c);
            assert(r0.len() == v@.len());
            let x = c.next();
            assert(x == Some(r0[0]));
            assert(IteratorSpec::remaining(&c) == r0.drop_first());
        }
        fn sum_copied(v: &Vec<u8>) -> (s: u64) requires v@.len() < 100, ensures s <= 255 * v@.len() {
            let mut s: u64 = 0;
            for x in it: v.iter().copied()
                invariant v@.len() < 100, it.seq() =~= v@, s <= 255 * it.index(),
            {
                s = s + x as u64;
            }
            s
        }
        fn count_tail(needle: &[u8]) -> (n: usize)
            requires needle@.len() >= 1, needle@.len() < 1000,
            ensures n == needle@.len() - 1,
        {
            let mut n: usize = 0;
            for b in it: needle.iter().copied().skip(1)
                invariant needle@.len() < 1000, it.seq() == needle@.skip(1), n == it.index(),
            {
                n = n + 1;
            }
            n
        }
        fn hash_rev(needle: &[u8]) -> (h: u64) requires needle@.len() >= 1 {
            let mut h: u64 = 0;
            for b in it: needle.iter().rev().copied().skip(1)
                invariant it.seq() == needle@.reverse().skip(1),
            {
                h = h.wrapping_add(b as u64);
            }
            h
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] copied_spec_wrong verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;
        fn wrong(v: &Vec<u8>) requires v@.len() >= 2 {
            let mut c = v.iter().copied();
            let ghost r0 = IteratorSpec::remaining(&c);
            let x = c.next();
            assert(x == Some(r0[1])); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_for_loop_by_mut_ref_leaves_facts_on_iterator verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        // `for x in &mut it` goes through core's blanket `impl Iterator for &mut I`.
        // After the loop, `it` is exhausted and can be used again.
        fn exhaust(v: &Vec<u8>) {
            let mut iter = v.iter();
            for x in &mut iter {
            }
            assert(IteratorSpec::remaining(&iter).len() == 0);
            let n = iter.next();
            assert(n.is_none());
        }

        // Partial consumption: break out early, then continue on the original iterator.
        // (The loop is verified in isolation, so the precondition is restated as an invariant.)
        fn first_then_rest(v: &Vec<u8>) -> (r: Option<&u8>)
            requires v@.len() >= 2,
            ensures r matches Some(x) && *x == v@[1],
        {
            let mut iter = v.iter();
            for x in it: &mut iter
                invariant_except_break it.index() == 0,
                invariant
                    it.seq() == v@.as_ref(),
                    v@.len() >= 2,
                ensures
                    it.index() == 1,
                    IteratorSpec::remaining(it.iter) == it.seq().skip(1),
            {
                proof { it.lemma_wf_remaining(); }
                break;
            }
            iter.next()
        }

        fn wrong(v: &Vec<u8>) {
            let mut iter = v.iter();
            for x in &mut iter {
            }
            assert(IteratorSpec::remaining(&iter).len() == v@.len()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_zip_take_over_by_ref_then_use_components verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::{IteratorSpec, zip_iter_fst, zip_iter_snd, take_iter, take_count};

        // std's Zip::next advances the first iterator first; when the second runs out the
        // element already taken from the first is dropped. Here the first (2 elements) runs
        // out: it is exhausted (2 Some + 1 None) and the second is advanced by exactly 2.
        fn zip_consumed(v: &Vec<u8>, w: &Vec<u8>)
            requires v@.len() == 2, w@.len() == 5,
        {
            let mut a = v.iter();
            let mut b = w.iter();
            for (x, y) in it: a.by_ref().zip(b.by_ref())
                invariant
                    IteratorSpec::remaining(&*zip_iter_fst(it.iter)).len() == 2 - it.index(),
                    IteratorSpec::remaining(&*zip_iter_snd(it.iter)).len() == 5 - it.index(),
                    &*final(zip_iter_fst(it.iter)) == &*final(zip_iter_fst(it.snapshot@)),
                    &*final(zip_iter_snd(it.iter)) == &*final(zip_iter_snd(it.snapshot@)),
            {
            }
            assert(IteratorSpec::remaining(&a).len() == 0);
            assert(IteratorSpec::remaining(&b).len() == 3);
        }

        // the second runs out first: the first has consumed one extra element
        fn zip_extra_consumption(v: &Vec<u8>, w: &Vec<u8>)
            requires v@.len() == 5, w@.len() == 2,
        {
            let mut a = v.iter();
            let mut b = w.iter();
            for (x, y) in it: a.by_ref().zip(b.by_ref())
                invariant_except_break
                    // at the loop head: both advanced by the pairs yielded so far
                    IteratorSpec::remaining(&*zip_iter_fst(it.iter)).len() == 5 - it.index(),
                    IteratorSpec::remaining(&*zip_iter_snd(it.iter)).len() == 2 - it.index(),
                invariant
                    &*final(zip_iter_fst(it.iter)) == &*final(zip_iter_fst(it.snapshot@)),
                    &*final(zip_iter_snd(it.iter)) == &*final(zip_iter_snd(it.snapshot@)),
                ensures
                    // at the exit: the second ran out, the first lost one more element
                    IteratorSpec::remaining(&*zip_iter_snd(it.iter)).len() == 0,
                    IteratorSpec::remaining(&*zip_iter_fst(it.iter)).len() == 2,
            {
            }
            assert(IteratorSpec::remaining(&b).len() == 0);
            assert(IteratorSpec::remaining(&a).len() == 2); // 5 - 2 pairs - 1 dropped element
        }

        fn take_then_rest(v: &Vec<u8>) -> (r: Option<&u8>)
            requires v@.len() == 3,
            ensures r matches Some(x) && *x == v@[2],
        {
            let mut it = v.iter();
            let ghost r0 = IteratorSpec::remaining(&it);
            for x in t: it.by_ref().take(2)
                invariant
                    r0 == v@.as_ref(),
                    IteratorSpec::remaining(&*take_iter(t.iter)).len() == 3 - t.index(),
                    forall|j: int| 0 <= j < 3 - t.index() ==>
                        #[trigger] IteratorSpec::remaining(&*take_iter(t.iter))[j] == r0[t.index() + j],
                    take_count(t.iter) == 2 - t.index(),
                    &*final(take_iter(t.iter)) == &*final(take_iter(t.snapshot@)),
            {
            }
            it.next()
        }

        fn wrong(v: &Vec<u8>, w: &Vec<u8>)
            requires v@.len() == 5, w@.len() == 2,
        {
            let mut a = v.iter();
            let mut b = w.iter();
            for (x, y) in it: a.by_ref().zip(b.by_ref())
                invariant_except_break
                    IteratorSpec::remaining(&*zip_iter_fst(it.iter)).len() == 5 - it.index(),
                    IteratorSpec::remaining(&*zip_iter_snd(it.iter)).len() == 2 - it.index(),
                invariant
                    &*final(zip_iter_fst(it.iter)) == &*final(zip_iter_fst(it.snapshot@)),
                    &*final(zip_iter_snd(it.iter)) == &*final(zip_iter_snd(it.snapshot@)),
                ensures
                    IteratorSpec::remaining(&*zip_iter_fst(it.iter)).len() == 2,
            {
            }
            assert(IteratorSpec::remaining(&a).len() == 3); // FAILS (one element was dropped)
        }
    } => Err(err) => assert_one_fails(err)
}

