use vstd::prelude::*;

verus! {

pub open spec fn bump(x: int) -> int { x + 1 }

pub fn add_one(x: u32) -> (r: u32)
    requires
        x < 100,
    ensures
        r as int == bump(x as int),
        r > 0,
{
    x + 1
}

} // verus!
