use vstd::prelude::*;

verus! {

fn count_to(n: u32) -> (r: u32)
    requires
        n <= 10,
    ensures
        r == n,
{
    let mut i: u32 = 0;
    while i < n
        invariant
            i <= n,
        decreases n - i,
    {
        i = i + 1;
    }
    i
}

} // verus!

fn main() {}
