#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_dyn verus_code! {
        use std::rc::Rc;
        use std::sync::Arc;
        use vstd::prelude::*;
        trait T {
            spec fn b(&self) -> u8 { 5 }
            fn f(&self) -> (r: u8) ensures r <= self.b();
        }
        impl T for u8 {
            spec fn b(&self) -> u8 { *self }
            fn f(&self) -> (r: u8) { *self / 2 }
        }
        impl T for u16 {
            spec fn b(&self) -> u8 { (*self / 256) as u8 }
            fn f(&self) -> (r: u8) { (*self / 512) as u8 }
        }
        impl T for u32 {
            fn f(&self) -> (r: u8) { 4 }
        }
        fn test_coerce_ref() {
            let u: u8 = 7;
            let d: &dyn T = &u; // ToDyn coercion
            let r = d.f();
            assert(d.b() == 7);
            assert(r <= 10);
        }

        fn test_coerce_box() {
            let x: u32 = 9;
            let d: Box<dyn T> = Box::new(x); // ToDyn coercion
            let r = d.f();
            assert(d.b() == 5);
            assert(r <= 10);

            let y: u16 = 8;
            let d: Box<dyn T> = Box::new(y); // ToDyn coercion
            let r = d.f();
            assert(d.b() == 5); // FAILS
        }

        fn test_coerce_rc() {
            let x: u32 = 9;
            let d: Rc<dyn T> = Rc::new(x); // ToDyn coercion
            let r = d.f();
            assert(d.b() == 5);
            assert(r <= 10);

            let y: u16 = 8;
            let d: Rc<dyn T> = Rc::new(y); // ToDyn coercion
            let r = d.f();
            assert(d.b() == 5); // FAILS
        }

        fn test_coerce_arc() {
            let x: u32 = 9;
            let d: Arc<dyn T> = Arc::new(x); // ToDyn coercion
            let r = d.f();
            assert(d.b() == 5);
            assert(r <= 10);

            let y: u16 = 8;
            let d: Arc<dyn T> = Arc::new(y); // ToDyn coercion
            let r = d.f();
            assert(d.b() == 5); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_dyn_ext verus_code! {
        #[verifier::external]
        trait T {
            fn f(&self) -> u8;
        }

        #[verifier::external_trait_specification]
        #[verifier::external_trait_extension(TSpec via TSpecImpl)]
        trait ExT {
            type ExternalTraitSpecificationFor: T;

            spec fn b(&self) -> u8;
            fn f(&self) -> (r: u8) ensures r <= self.b();
        }

        impl T for u8 {
            fn f(&self) -> (r: u8) { *self / 2 }
        }

        impl TSpecImpl for u8 {
            spec fn b(&self) -> u8 { *self }
        }

        fn test() {
            let u: u8 = 7;
            let d: &dyn T = &u; // ToDyn coercion
            assert(d.b() == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] explicit_dyn_coercion_lowered_to_identity verus_code! {
        trait T {
            fn f(&self);
        }

        impl T for u8 {
            fn f(&self) {}
        }

        fn test(value: &u8) {
            let value: &dyn T = value as _;
            value.f();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_dyn_generic verus_code! {
        use vstd::prelude::*;

        trait T0 {
        }

        trait T4 {
            fn f(&self);
        }

        fn g0<A: T0 + ?Sized>() {
        }

        fn g1<A: T0 + ?Sized>(a: &A) {
        }

        fn test(x0: &dyn T0, x4: &dyn T4) {
            g0::<dyn T0>();
            g1(x0);
            x4.f();
        }

        fn test2<A0: T0, A4: T4>(a0: &A0, a4: &A4, b4: A4) {
            let x: &dyn T4 = &b4;
            let x: Box<dyn T4> = Box::new(b4);
            test(a0, a4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited1 verus_code! {
        use vstd::prelude::*;
        trait T {
            proof fn bogus(&self)
                ensures
                    false;
        }
        proof fn test() {
            let d: &dyn T = arbitrary();
            d.bogus();
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "not Verus dyn-compatible")
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited1b verus_code! {
        trait T {
            spec fn f(&self) -> nat;
            proof fn about_f(&self) ensures self.f() < 10;
        }

        broadcast proof fn promote_f<A: T>(a: &A)
            ensures
                #[trigger] a.f() < 10,
        {
            a.about_f();
        }

        proof fn test(s: &dyn T) {
            assert(s.f() < 10);
        }
    } => Err(err) => assert_vir_error_msg(err, "not Verus dyn-compatible")
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited2 verus_code! {
        use vstd::prelude::*;
        trait T {
            proof fn bogus(tracked &self)
                ensures
                    false;
        }
        proof fn test() {
            let d: &dyn T = arbitrary();
            d.bogus();
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited2b verus_code! {
        trait T {
            spec fn f(&self) -> nat;
            proof fn about_f(tracked &self) ensures self.f() < 10;
        }

        broadcast proof fn promote_f<A: T>(a: &A)
            ensures
                #[trigger] a.f() < 10,
        {
            a.about_f();
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited3 verus_code! {
        use vstd::prelude::*;
        trait T {
            proof fn bogus(tracked &self)
                ensures
                    false;
        }
        proof fn test() {
            let tracked d: &dyn T = arbitrary();
            d.bogus();
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited3b verus_code! {
        trait T {
            spec fn f(&self) -> nat;
            proof fn about_f(tracked &self) ensures self.f() < 10;
        }

        broadcast proof fn promote_f<A: T>(tracked a: &A)
            ensures
                #[trigger] a.f() < 10,
        {
            a.about_f();
        }
    } => Err(err) => assert_vir_error_msg(err, "broadcast function must have spec parameters")
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited4 verus_code! {
        use vstd::prelude::*;
        trait T {
            spec fn bogus(&self)
                ensures
                    false;
        }
        proof fn test() {
            let d: &dyn T = arbitrary();
            d.bogus();
            assert(false);
        }
        // Note: when we allow spec ensures, this should become a "not Verus dyn-compatible" error
    } => Err(err) => assert_vir_error_msg(err, "spec functions cannot have requires/ensures")
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited_sized verus_code! {
        use vstd::prelude::*;
        enum Opt<A: ?Sized> {
            None,
            Some(Box<A>),
        }

        spec fn f<A: ?Sized>(a: &Opt<A>) -> bool { true }

        trait False {
            proof fn ensure_false() where Self: Sized ensures false;
        }

        broadcast proof fn promote_false<A: False>(a: Opt<A>)
            ensures
                #[trigger] f::<A>(&a),
                false,
        {
            A::ensure_false();
        }

        proof fn incorrect<A: False + ?Sized>()
            ensures
                false,
        {
            broadcast use promote_false;
            assert(f::<A>(&Opt::None));
            assert(false); // FAILS
        }

        proof fn bad()
            ensures
                false,
        {
            incorrect::<dyn False>();
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] dyn_rust_blanket_unsoundness verus_code! {
        // https://github.com/rust-lang/rust/issues/57893
        trait T {}
        impl<A: ?Sized> T for A {}
        fn test(x: &dyn T) {}
    } => Err(err) => assert_vir_error_msg(err, "it has an unsized blanket impl")
}

test_verify_one_file! {
    #[test] dyn_rust_blanket_unsoundness2 verus_code! {
        // https://github.com/rust-lang/rust/issues/57893
        trait TraitA { type Item: ?Sized; }
        trait TraitB<T> { }
        impl<X: TraitA> TraitB<X> for X::Item { }
        impl TraitA for () { type Item = dyn TraitB<()>; }
    } => Err(err) => assert_vir_error_msg(err, "conflicting implementations of trait")
}

test_verify_one_file! {
    #[test] dyn_in_struct verus_code! {
        use vstd::prelude::*;
        trait T { fn f(&self) {} }
        impl T for u8 {}
        struct S(Box<dyn T>);
        fn test() {
            let u: u8 = 3;
            let s = S(Box::new(u));
            s.0.f();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] dyn_cycle1 verus_code! {
        trait T {
            spec fn f(&self, d: &dyn T) -> int;
        }
        impl T for u8 {
            spec fn f(&self, d: &dyn T) -> int {
                d.f(d) + 1
            }
        }
        proof fn test() {
            let u: u8 = 3;
            let d: &dyn T = &u;
            assert(d.f(d) == d.f(d) + 1);
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference")
}

test_verify_one_file! {
    #[test] dyn_cycle2 verus_code! {
        trait T {
            proof fn f(tracked &self, tracked d: &dyn T)
                ensures
                    false;
        }
        impl T for u8 {
            proof fn f(tracked &self, tracked d: &dyn T) {
                d.f(d)
            }
        }
        proof fn test() {
            let tracked u: u8 = 3;
            let tracked d: &dyn T = &u;
            d.f(d);
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference")
}

test_verify_one_file! {
    #[test] dyn_cycle3 verus_code! {
        use vstd::std_specs::alloc::*;
        trait T {
            spec fn f(&self, d: &S) -> int;
        }
        struct S(Box<dyn T>);
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference")
}

test_verify_one_file! {
    #[test] dyn_cycle4 verus_code! {
        use vstd::prelude::*;
        trait T {
            spec fn f(&self) -> S;
        }
        struct S(Box<dyn T>);

        proof fn p(s: &S)
            ensures
                false,
            decreases s
        {
            p(&(s.0).f())
        }

        proof fn test()
            ensures
                false,
        {
            p(&arbitrary());
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference")
}

test_verify_one_file! {
    #[test] dyn_cycle5 verus_code! {
        use vstd::prelude::*;
        trait T<A> {
            spec fn f(&self) -> A;
        }
        struct S(Box<dyn T<S>>);

        proof fn p(s: &S)
            ensures
                false,
            decreases s
        {
            p(&(s.0).f())
        }

        proof fn test()
            ensures
                false,
        {
            p(&arbitrary());
        }
    } => Err(err) => assert_vir_error_msg(err, "non-positive position")
}

test_verify_one_file! {
    #[test] dyn_auto_traits verus_code! {
        use vstd::prelude::*;
        trait Animal {
            spec fn spec_legs(&self) -> u64;
            fn legs(&self) -> (r: u64) ensures r == self.spec_legs();
        }
        struct Dog;
        impl Animal for Dog {
            spec fn spec_legs(&self) -> u64 { 4 }
            fn legs(&self) -> (r: u64) ensures r == self.spec_legs() { 4 }
        }
        // auto-trait bounds carry no verification content and are accepted
        fn count(a: &(dyn Animal + Send + Sync)) -> (r: u64)
            ensures r == a.spec_legs()
        {
            a.legs()
        }
        // dropping the auto trait is an identity coercion: facts survive it
        fn count_plain(a: &(dyn Animal + Send)) -> (r: u64)
            ensures r == a.spec_legs()
        {
            let b: &dyn Animal = a;
            b.legs()
        }
        fn total(zoo: &Vec<Box<dyn Animal + Send + Sync>>) -> (r: u64)
            requires zoo.len() == 2,
            ensures r == zoo[0].spec_legs() + zoo[1].spec_legs(),
        {
            let a = zoo[0].legs();
            let b = zoo[1].legs();
            assume(a + b <= u64::MAX);
            a + b
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] dyn_auto_traits_fails verus_code! {
        use vstd::prelude::*;
        trait Animal {
            spec fn spec_legs(&self) -> u64;
            fn legs(&self) -> (r: u64) ensures r == self.spec_legs();
        }
        fn wrong(a: &(dyn Animal + Send)) -> (r: u64)
            ensures r == a.spec_legs() + 1 // FAILS
        {
            a.legs()
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] dyn_unsupported2 verus_code! {
        trait T {}
        fn test(d: &dyn Fn() -> ()) {
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: dyn with a binding of a supertrait's associated type")
}

test_verify_one_file! {
    #[test] test_dyn2 verus_code! {
        use vstd::prelude::*;
        trait T {
            spec fn f(&self) -> int;
        }
        impl T for u32 {
            spec fn f(&self) -> int { 3 }
        }
        impl T for Box<u32> {
            spec fn f(&self) -> int { 4 }
        }
        fn test_coerce() {
            let x: Box<u32> = Box::new(9);
            let d: Box<dyn T> = Box::new(x); // ToDyn coercion
            assert(d.f() == 4);
            assert(d.f() == 3); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_dyn_owned_precond verus_code! {
        use vstd::prelude::*;
        verus! {
            pub trait T {
                spec fn t(&self) -> int;
            }
            struct Ty {}
            impl T for Ty {
                open spec fn t(&self) -> int { 0 }
            }
            fn borrowed<'a>(x: &'a Box<dyn T>)
                requires
                x.t() == 0,
            {}
            fn owned(x: Box<dyn T>)
                requires
                x.t() == 0,
            {}
            fn repro() {
                let x: Box<dyn T> = Box::new(Ty {});
                assert(x.t() == 0);
                borrowed(&x);
                // Exercises failure case of #2629: rustc emits a no-op unsize
                // adjustment, which must not generate a spurious ToDyn, as that
                // breaks carrying the precondition through:
                owned(x);
            }
        }
    } => Ok(())
}

// dyn Trait<Assoc = T>: the binding is part of the dyn type's identity

const DYN_PROJ_COMMON: &str = verus_code_str! {
    trait Producer {
        type Item;
        spec fn peek(&self) -> Self::Item;
        fn next(&self) -> (r: Self::Item)
            ensures r == self.peek();
    }
    struct Ones;
    impl Producer for Ones {
        type Item = u64;
        spec fn peek(&self) -> u64 { 1 }
        fn next(&self) -> (r: u64) ensures r == self.peek() { 1 }
    }
    struct Twos;
    impl Producer for Twos {
        type Item = u64;
        spec fn peek(&self) -> u64 { 2 }
        fn next(&self) -> (r: u64) ensures r == self.peek() { 2 }
    }
    struct Flags;
    impl Producer for Flags {
        type Item = bool;
        spec fn peek(&self) -> bool { true }
        fn next(&self) -> (r: bool) ensures r == self.peek() { true }
    }
};

test_verify_one_file! {
    #[test] dyn_projection_basic DYN_PROJ_COMMON.to_string() + verus_code_str! {
        fn use_dyn(p: &dyn Producer<Item = u64>) -> (r: u64)
            ensures r == p.peek()
        {
            p.next()
        }
        fn use_dyn_b(p: &dyn Producer<Item = bool>) -> (r: bool)
            ensures r == p.peek()
        {
            p.next()
        }
        fn test() {
            let o = Ones;
            let r = use_dyn(&o);
            assert(r == 1);
            let f = Flags;
            let b = use_dyn_b(&f);
            assert(b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] dyn_projection_heterogeneous DYN_PROJ_COMMON.to_string() + verus_code_str! {
        use vstd::prelude::*;
        fn sum(v: &Vec<Box<dyn Producer<Item = u64>>>) -> (r: u64)
            requires v.len() == 2, v[0].peek() == 1, v[1].peek() == 2,
            ensures r == 3
        {
            let a = v[0].next();
            let b = v[1].next();
            a + b
        }
        fn test() {
            let mut v: Vec<Box<dyn Producer<Item = u64>>> = Vec::new();
            let a: Box<dyn Producer<Item = u64>> = Box::new(Ones);
            let b: Box<dyn Producer<Item = u64>> = Box::new(Twos);
            v.push(a);
            v.push(b);
            let s = sum(&v);
            assert(s == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] dyn_projection_wrong_post DYN_PROJ_COMMON.to_string() + verus_code_str! {
        fn wrong(p: &dyn Producer<Item = u64>) -> (r: u64)
            ensures r == 7 // FAILS
        {
            p.next()
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Two dyn types of one trait with different bindings must remain distinct types:
    // conflating them would make their projection axioms contradict (Item == u64 and
    // Item == bool for the same type id) and prove false.
    #[test] dyn_projection_distinct_bindings_sound DYN_PROJ_COMMON.to_string() + verus_code_str! {
        proof fn no_false(a: &dyn Producer<Item = u64>, b: &dyn Producer<Item = bool>) {
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] dyn_projection_with_trait_args verus_code! {
        trait Conv<A> {
            type Out;
            spec fn spec_conv(&self, a: A) -> Self::Out;
            fn conv(&self, a: A) -> (r: Self::Out) ensures r == self.spec_conv(a);
        }
        struct Widen;
        impl Conv<u8> for Widen {
            type Out = u64;
            spec fn spec_conv(&self, a: u8) -> u64 { a as u64 }
            fn conv(&self, a: u8) -> (r: u64) ensures r == self.spec_conv(a) { a as u64 }
        }
        fn via(c: &dyn Conv<u8, Out = u64>, x: u8) -> (r: u64)
            ensures r == c.spec_conv(x)
        {
            c.conv(x)
        }
        fn test() {
            let w = Widen;
            let r = via(&w, 5);
            assert(r == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    // A dyn value's typing (has_type) is established by the to_dyn coercion, which also
    // makes facts about collections of dyn values available (Vec::push postconditions).
    #[test] dyn_vec_push_len verus_code! {
        use vstd::prelude::*;
        trait Shape { spec fn area(&self) -> int; }
        struct Sq(u64);
        impl Shape for Sq { spec fn area(&self) -> int { self.0 as int } }
        fn test() {
            let s1 = Sq(1);
            let mut v: Vec<&dyn Shape> = Vec::new();
            let a: &dyn Shape = &s1;
            v.push(a);
            assert(v@.len() == 1);
            assert(v@[0] == a);
        }
    } => Ok(())
}
