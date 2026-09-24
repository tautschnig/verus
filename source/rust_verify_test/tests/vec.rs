#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_vec_into_iter verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::vec::*;

        fn test() {
            let mut v1: Vec<u32> = Vec::new();
            let mut v2: Vec<u32> = Vec::new();
            v1.push(3);
            v1.push(4);
            assert(v1@ == seq![3u32, 4u32]);

            v2.push(5);
            assert(v2.len() == 1);
            v2.push(7);
            assert(v2@.len() == 2);
            v2.insert(1, 6);
            assert(v2@ == seq![5u32, 6u32, 7u32]);

            v1.append(&mut v2);
            assert(v2@.len() == 0);
            assert(v1@.len() == 5);
            assert(v1@ == seq![3u32, 4u32, 5u32, 6u32, 7u32]);
            v1.remove(2);
            assert(v1@ == seq![3u32, 4u32, 6u32, 7u32]);

            v1.push(8u32);
            v1.push(9u32);
            assert(v1@ == seq![3u32, 4u32, 6u32, 7u32, 8u32, 9u32]);

            v1.swap_remove(5);
            assert(v1@ == seq![3u32, 4u32, 6u32, 7u32, 8u32]);

            let mut i: usize = 0;
            for x in it: v1
                invariant
                    i == it.index(),
                    it.seq() == seq![3u32, 4u32, 6u32, 7u32, 8u32],
            {
                assert(x > 2);
                assert(x < 10);
                i = i + 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_vec_dec verus_code! {
        use vstd::prelude::*;
        struct Tree {
            children: Vec<Tree>,
        }

        fn recurse(tree: &Tree)
            decreases *tree
        {
            if tree.children.len() > 0 {
                recurse(&tree.children[0]);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] retain_spec verus_code! {
        use vstd::prelude::*;
        fn keep_even(v: &mut Vec<u64>)
            ensures
                forall|i| 0 <= i < final(v)@.len() ==> #[trigger] final(v)@[i] % 2 == 0,
                final(v)@.len() <= old(v)@.len(),
        {
            let f = |x: &u64| -> (b: bool) ensures b == (*x % 2 == 0) { *x % 2 == 0 };
            v.retain(f);
            proof {
                let keep = choose|keep: Seq<bool>| #[trigger] keep.len() == old(v)@.len()
                    && (forall|j| 0 <= j < keep.len() ==> call_ensures(f, (&old(v)@[j],), #[trigger] keep[j]))
                    && v@ == old(v)@.filter_index(|j: int| keep[j]);
                old(v)@.lemma_filter_index(|j: int| keep[j]);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] retain_spec_wrong verus_code! {
        use vstd::prelude::*;
        fn keep_even(v: &mut Vec<u64>)
            ensures final(v)@.len() == old(v)@.len(), // FAILS
        {
            v.retain(|x: &u64| -> (b: bool) ensures b == (*x % 2 == 0) { *x % 2 == 0 });
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] drain_spec verus_code! {
        use vstd::prelude::*;
        fn drain_front(v: &mut Vec<u64>) -> (r: Vec<u64>)
            requires old(v)@.len() >= 2,
            ensures
                r@ == old(v)@.subrange(0, 2),
                final(v)@ == old(v)@.subrange(2, old(v)@.len() as int),
        {
            let mut out: Vec<u64> = Vec::new();
            for x in it: v.drain(0..2)
                invariant
                    it.seq() == old(v)@.subrange(0, 2),
                    out@ == it.seq().subrange(0, it.index()),
            {
                out.push(x);
            }
            out
        }
        fn drain_all(v: &mut Vec<u64>)
            ensures final(v)@.len() == 0,
        {
            let d = v.drain(..);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] drain_spec_out_of_range verus_code! {
        use vstd::prelude::*;
        fn test(v: &mut Vec<u64>)
            requires old(v)@.len() == 1,
        {
            let d = v.drain(0..2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] drain_spec_wrong verus_code! {
        use vstd::prelude::*;
        fn test(v: &mut Vec<u64>)
            requires old(v)@.len() >= 3,
            ensures final(v)@.len() == old(v)@.len(), // FAILS
        {
            let d = v.drain(1..2);
        }
    } => Err(err) => assert_one_fails(err)
}
