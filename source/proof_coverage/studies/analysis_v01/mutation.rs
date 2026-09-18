use vstd::prelude::*;

verus! {

// A mutation whose value the postcondition depends on, and one whose value it
// does not. `total` is rebuilt every iteration and read at exit; `scratch` is
// mutated and never read by any obligation.
fn accumulate(n: u32) -> (r: u32)
    requires
        n <= 100,
    ensures
        r == n,
{
    let mut i: u32 = 0;
    let mut total: u32 = 0;
    let mut scratch: u32 = 7;
    while i < n
        invariant
            i <= n,
            total == i,
        decreases n - i,
    {
        scratch = scratch ^ 1;
        total = total + 1;
        i = i + 1;
    }
    total
}

// Reading the old value: `x = -x` must be attributed to the assignment and
// evaluate the right-hand side before the variable changes.
proof fn negate_twice(x: int) -> (r: int)
    ensures
        r == x,
{
    let mut y = x;
    y = -y;
    y = -y;
    y
}

} // verus!

fn main() {}
