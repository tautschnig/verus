use vstd::prelude::*;

verus! {

// Identical-shaped modules: only the module name differs.
mod twin_a {
    use vstd::prelude::*;
    pub fn f(n: u32) -> (r: u32) requires n < 10, ensures r == n + 1 { n + 1 }
}
mod twin_b {
    use vstd::prelude::*;
    pub fn f(n: u32) -> (r: u32) requires n < 10, ensures r == n + 1 { n + 1 }
}

// Two textually identical spinoff (nonlinear) queries on ONE source line:
// same fun, same desc, columns differ only.
fn host(n: u32) -> (r: u32)
    requires n < 5,
    ensures r == n,
{
    proof { assert(0int * 0int == 0int) by (nonlinear_arith); assert(0int * 0int == 0int) by (nonlinear_arith); }
    n
}

fn main() {}

} // verus!
