use vstd::prelude::*;

verus! {

proof fn compare(a: int, b: int) -> (r: int)
    requires
        a >= 0,
        b >= 0,
    ensures
        r >= a,
        r >= b,
{
    a + b
}

fn main() {}

} // verus!
