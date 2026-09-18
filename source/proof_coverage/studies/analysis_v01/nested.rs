use vstd::prelude::*;

verus! {

fn nested_count(n: u32) -> (r: u32)
    requires
        n <= 10,
    ensures
        r == n,
{
    let mut i: u32 = 0;
    let mut x: u32 = 0;
    while i < n
        invariant
            i <= n,
            x == i,
        decreases n - i,
    {
        let mut j: u32 = 0;
        while j < 1
            invariant
                j <= 1,
                x == i,
            decreases 1 - j,
        {
            j = j + 1;
        }
        x = x + j;
        i = i + 1;
    }
    x
}

} // verus!

fn main() {}
