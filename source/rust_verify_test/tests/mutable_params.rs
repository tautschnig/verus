#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] mut_param_with_loops [] => verus_code! {
        fn cond() -> bool { true }

        fn test(mut x: u64) -> (y: u64)
            ensures x == y
        {
            let z = x;
            x = 5;
            return z;
        }

        fn test_fails(mut x: u64) -> (y: u64)
            ensures x == y
        {
            x = 5;
            return 5; // FAILS
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                return x;
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails0(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                let z = x;
                x = 5;
                return z; // FAILS (requires invariant relating x to old(x))
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                x = 5;
                return 5; // FAILS
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails2(mut x: u64) -> (y: u64)
            ensures x == y
        {
            x = 1;
            loop {
                let z = x;
                return z; // FAILS
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails3(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                if cond() {
                    let z = x;
                    return z; // FAILS
                } else {
                    x = 1;
                }
            }
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file_with_options! {
    #[test] mut_param_on_closure_with_loops [] => verus_code! {
        fn cond() -> bool { true }

        fn test() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y
            {
                let z = x;
                x = 5;
                return z;
            };
        }

        fn test_fails() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                x = 5;
                return 5;
            };
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y
            {
                loop {
                    return x;
                }
            };
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails0() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS (requires invariant relating x to old(x))
            {
                loop {
                    let z = x;
                    x = 5;
                    return z;
                }
            };
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                loop {
                    x = 5;
                    return 5;
                }
            };
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails2() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                x = 1;
                loop decreases 0int {
                    let z = x;
                    return z;
                }
            };
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails3() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                loop {
                    if cond() {
                        let z = x;
                        return z;
                    } else {
                        x = 1;
                    }
                }
            };
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file_with_options! {
    #[test] no_confusion_invariants_spec [] => verus_code! {
        use vstd::prelude::*;

        struct X { }

        impl vstd::invariant::InvariantPredicate<(), ()> for X {
            open spec fn inv(k: (), v: ()) -> bool { true }
        }

        fn open(mut x: u64, Tracked(t): Tracked<&vstd::invariant::AtomicInvariant<(), (), X>>)
            requires t.namespace() == x + 1, x < 10,
            opens_invariants [x]
        {
            x = x + 1;
            vstd::invariant::open_atomic_invariant!(t => i => {
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot show invariant namespace is in the mask given by the scope")
}

test_verify_one_file_with_options! {
    #[test] no_confusion_unwind_spec [] => verus_code! {
        fn panic() { }

        fn open(mut x: u64)
            no_unwind when x != 1
        {
            x = 1;
            panic(); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] no_confusion_ensures_recommend_check [] => verus_code! {
        spec fn rec(x: int) -> bool
            recommends x == 2
        {
            false
        }

        proof fn test_ens(mut x: int)
            ensures rec(x)
        {
            x = 2;
        }
    } => Err(err) => assert_has_recommends_failure(err)
}

test_verify_one_file_with_options! {
    #[test] no_confusion_ensures_recommend_check_closure [] => verus_code! {
        spec fn rec(x: u64) -> bool
            recommends x == 2
        {
            false
        }

        fn test_ens() {
            let r = |mut x: u64|
                ensures rec(x)
            {
                x = 2;
            };
        }
    } => Err(err) => assert_has_recommends_failure(err)
}

test_verify_one_file_with_options! {
    #[test] no_confusion_decreases_clause [] => verus_code! {
        #[allow(unconditional_recursion)]
        fn test(mut x: u64)
            decreases x
        {
            x = 30;
            test(20); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] mut_param_with_loops_iso_false [] => verus_code! {
        fn cond() -> bool { true }

        fn test(mut x: u64) -> (y: u64)
            ensures x == y
        {
            let z = x;
            x = 5;
            return z;
        }

        fn test_fails(mut x: u64) -> (y: u64)
            ensures x == y
        {
            x = 5;
            return 5; // FAILS
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                return x;
            }
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails0(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                let z = x;
                x = 5;
                return z; // FAILS (requires invariant relating x to old(x))
            }
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                x = 5;
                return 5; // FAILS
            }
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails2(mut x: u64) -> (y: u64)
            ensures x == y
        {
            x = 1;
            loop {
                let z = x;
                return z; // FAILS
            }
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails3(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                if cond() {
                    let z = x;
                    return z; // FAILS
                } else {
                    x = 1;
                }
            }
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file_with_options! {
    #[test] mut_param_on_closure_with_loops_iso_false [] => verus_code! {
        fn cond() -> bool { true }

        fn test() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y
            {
                let z = x;
                x = 5;
                return z;
            };
        }

        fn test_fails() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                x = 5;
                return 5;
            };
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y
            {
                loop {
                    return x;
                }
            };
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails0() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS (requires invariant relating x to old(x))
            {
                loop {
                    let z = x;
                    x = 5;
                    return z;
                }
            };
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                loop {
                    x = 5;
                    return 5;
                }
            };
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails2() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                x = 1;
                loop decreases 0int {
                    let z = x;
                    return z;
                }
            };
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails3() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                loop {
                    if cond() {
                        let z = x;
                        return z;
                    } else {
                        x = 1;
                    }
                }
            };
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file_with_options! {
    #[test] mutation_conditional_cases [] => verus_code! {
        fn cond() -> bool { true }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test1(mut x: u64) -> (y: u64)
            ensures y == x
        {
            if cond() {
                x = 20;
                loop{}
            } else {
                loop {
                    return x; // ok
                }
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test2(mut x: u64) -> (y: u64)
            ensures y == x
        {
            if cond() {
                loop {
                    return x; // ok
                }
            } else {
                x = 20;
                loop{}
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test3(mut x: u64) -> (y: u64)
            ensures y == x
        {
            if cond() {
                loop{}
            } else {
                x = 20;
                loop {
                    return x; // FAILS
                }
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test4(mut x: u64) -> (y: u64)
            ensures y == x
        {
            if cond() {
                x = 20;
                loop {
                    return x; // FAILS
                }
            } else {
                loop{}
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test5(mut x: u64) -> (y: u64)
            ensures y == x
        {
            if cond() {
                x = 20;
            } else {
            }

            loop {
                return x; // FAILS
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test6(mut x: u64) -> (y: u64)
            ensures y == x
        {
            if cond() {
                x = 20;
            }

            loop {
                return x; // FAILS
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test7(mut x: u64) -> (y: u64)
            ensures y == x
        {
            if cond() {
            } else {
                x = 20;
            }

            loop {
                return x; // FAILS
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test8(mut x: u64) -> (y: u64)
            ensures y == x
        {
            x = 20;

            if cond() {
            } else {
            }

            loop {
                return x; // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file_with_options! {
    #[test] mutation_nested_loop [] => verus_code! {
        fn cond() -> bool { true }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test(mut x: u64) -> (y: u64)
            ensures y == x
        {
            loop {
                if cond() {
                    return x; // FAILS
                }

                loop {
                    if cond() {
                        x = 20;
                    }
                    if cond() {
                        break;
                    }
                }
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

// https://github.com/verus-lang/verus/issues/1933
// An ident subpattern (`a @ b: T`) in parameter position used to register only
// the outer name. Non-identifier parameter patterns are now bound from a hidden
// parameter by `let pat = param;` at the start of the body, so every name the
// pattern binds is registered.
test_verify_one_file_with_options! {
    #[test] ident_subpattern_in_param_position [] => verus_code! {
        fn double(a @ b: i32) -> (r: i32)
            requires -1000 < a < 1000,
            ensures r == 2 * a,
        {
            a + b
        }

        fn process(whole @ (a, b): (i32, i32)) -> (r: i32)
            requires 0 <= a < 10, 0 <= b < 10,
            ensures r == a + b + whole.0,
        {
            a + b + whole.0
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] pattern_params [] => verus_code! {
        struct M;
        trait L { fn enabled(&self, m: &M) -> bool; }
        struct Nop;
        impl L for Nop { fn enabled(&self, _: &M) -> bool { false } }

        fn ignore_arg(_: i32) -> (r: i32) ensures r == 0 { 0 }
        fn add_pair((a, b): (i32, i32)) -> (r: i32)
            requires 0 <= a < 10, 0 <= b < 10,
            ensures r == a + b,
        {
            a + b
        }
        fn first(&(a, b): &(u32, u32)) -> (r: u32) requires a < 10 ensures r == a { a }
        fn mut_in_pattern((x, mut y): (u32, u32)) -> (r: u32) ensures r == x { y = x; y }
        struct P { u: u64, v: u64 }
        fn field(P { u, .. }: P) -> (r: u64) ensures r == u { u }
        spec fn sum((a, b): (int, int)) -> int { a + b }
        proof fn sum_lemma((a, b): (int, int)) ensures sum((a, b)) == a + b {}

        fn caller() {
            let r = first(&(3, 4));
            assert(r == 3);
            let s = add_pair((1, 2));
            assert(s == 3);
            assert(sum((1, 2)) == 3);
        }

        fn wrong(&(a, b): &(u32, u32)) -> (r: u32)
            ensures r == b, // FAILS
        {
            a
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] pattern_param_mut_ref_binding_rejected [] => verus_code! {
        fn f((a, ref mut b): (u32, u32)) { *b = a; }
    } => Err(err) => assert_vir_error_msg(err, "mutable-reference bindings in function parameter patterns")
}
