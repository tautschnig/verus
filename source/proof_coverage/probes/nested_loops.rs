use vstd::prelude::*;

verus! {

fn sum_grid(n: u32) -> (total: u64)
    requires
        n <= 1000,
    ensures
        total == 1000 * (n as u64),
{
    let mut total: u64 = 0;
    let mut i: u32 = 0;
    while i < n
        invariant
            i <= n,
            n <= 1000,
            total == 1000 * (i as u64),
        decreases n - i,
    {
        let mut j: u32 = 0;
        while j < 1000
            invariant
                j <= 1000,
                i < n,
                n <= 1000,
                total == 1000 * (i as u64) + (j as u64),
            decreases 1000 - j,
        {
            total = total + 1;
            j = j + 1;
        }
        i = i + 1;
    }
    total
}

fn main() {
}

} // verus!
