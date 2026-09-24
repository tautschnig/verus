#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Function pointers `fn(A..) -> R` are modelled as `&dyn Fn(A..) -> R`; the coercions from
// fn items are `ToDyn`, so call_requires/call_ensures of a pointer are those of the function.

const FNS: &str = verus_code_str! {
    use vstd::prelude::*;
    fn inc(x: u64) -> (r: u64) requires x < 1000 ensures r == x + 1 { x + 1 }
    fn dec(x: u64) -> (r: u64) requires x > 0 ensures r == x - 1 { x - 1 }
};

test_verify_one_file! {
    #[test] fn_pointer_call FNS.to_string() + verus_code_str! {
        fn apply_ptr(f: fn(u64) -> u64, x: u64) -> (r: u64)
            requires f.requires((x,)),
            ensures f.ensures((x,), r),
        {
            f(x)
        }
        fn test() {
            let p: fn(u64) -> u64 = inc;
            let s = apply_ptr(p, 5);
            assert(s == 6);
            let t = p(7);
            assert(t == 8);
            let q = dec as fn(u64) -> u64;
            let u = q(7);
            assert(u == 6);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] fn_pointer_in_struct_and_generic FNS.to_string() + verus_code_str! {
        struct Ops { f: fn(u64) -> u64, g: fn(u64) -> u64 }
        fn run(ops: &Ops, x: u64) -> (r: u64)
            requires ops.f.requires((x,)),
            ensures ops.f.ensures((x,), r),
        {
            (ops.f)(x)
        }
        fn generic<F: Fn(u64) -> u64>(f: F, x: u64) -> (r: u64)
            requires f.requires((x,)),
            ensures f.ensures((x,), r),
        {
            f(x)
        }
        fn test() {
            let ops = Ops { f: inc, g: dec };
            let r = run(&ops, 5);
            assert(r == 6);
            let p: fn(u64) -> u64 = dec;
            let s = generic(p, 5);
            assert(s == 4);
            let mut v: Vec<fn(u64) -> u64> = Vec::new();
            v.push(inc);
            v.push(dec);
            assert(v.len() == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] fn_pointer_precondition FNS.to_string() + verus_code_str! {
        fn test() {
            let p: fn(u64) -> u64 = inc;
            let s = p(2000); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] fn_pointer_wrong_result FNS.to_string() + verus_code_str! {
        fn test() {
            let p: fn(u64) -> u64 = dec;
            let s = p(7);
            assert(s == 15); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // A fn pointer to `inc` and one to `dec` have the same type but different specifications
    #[test] fn_pointer_distinct_values_sound FNS.to_string() + verus_code_str! {
        proof fn no_false(a: fn(u64) -> u64, b: fn(u64) -> u64) {
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
