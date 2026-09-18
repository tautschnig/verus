use vstd::prelude::*;

verus! {

mod alpha {
    use vstd::prelude::*;
    pub fn f(n: u32) -> (r: u32) requires n < 100, ensures r == n + 1 { n + 1 }
    pub fn g(n: u32) -> (r: u32) requires n < 50, ensures r >= n {
        let mut i: u32 = 0;
        while i < n invariant i <= n, n < 50, decreases n - i, { i = i + 1; }
        i
    }
}

mod beta {
    use vstd::prelude::*;
    pub fn h(a: u32, b: u32) -> (r: u64) ensures r == a as u64 + b as u64 {
        (a as u64) + (b as u64)
    }
    proof fn lemma_sq(x: int) ensures x * x >= 0 {
        assert(x * x >= 0) by (nonlinear_arith);
    }
}

mod gamma {
    use vstd::prelude::*;
    pub fn k(n: u32) -> (r: u32) requires n < 30, ensures r <= 2 * n {
        let mut s: u32 = 0;
        let mut i: u32 = 0;
        while i < n invariant i <= n, n < 30, s == 2 * i, decreases n - i,
        { s = s + 2; i = i + 1; }
        s
    }
}

mod delta {
    use vstd::prelude::*;
    pub enum E { A(u32), B }
    pub fn m(e: &E) -> (r: u32) ensures r < 200 {
        match e { E::A(v) => if *v < 100 { *v } else { 0 }, E::B => 7 }
    }
}

fn main() {}

} // verus!
