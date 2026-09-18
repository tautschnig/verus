use vstd::prelude::*;

verus! {

fn sum_to(n: u32) -> (s: u64)
    requires
        n <= 1000,
    ensures
        s <= 1000 * 1000,
{
    let mut s: u64 = 0;
    for i in 0..n
        invariant
            s <= 1000 * (i as u64),
            n <= 1000,
    {
        s = s + 1000;
    }
    proof {
        assert(s <= 1000 * (n as u64));
        assert(1000 * (n as u64) <= 1000 * 1000) by (nonlinear_arith)
            requires n <= 1000;
    }
    s
}

fn main() {}

} // verus!
