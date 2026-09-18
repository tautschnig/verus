use vstd::prelude::*;

verus! {

fn find_first_ge(v: u32, limit: u32) -> (idx: u32)
    requires
        limit <= 1000,
    ensures
        idx <= limit,
{
    let mut i: u32 = 0;
    loop
        invariant_except_break
            i <= limit,
        ensures
            i <= limit,
        decreases limit - i,
    {
        if i >= limit {
            break;
        }
        if i == v {
            break;
        }
        i = i + 1;
    }
    i
}

fn main() {}

} // verus!
