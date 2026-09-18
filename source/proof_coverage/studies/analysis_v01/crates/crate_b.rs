use vstd::prelude::*;
use crate_a::*;

verus! {

fn twice(x: u32) -> (r: u32)
    requires
        x < 50,
    ensures
        r as int == bump(bump(x as int)),
{
    let y = add_one(x);
    add_one(y)
}

} // verus!

fn main() {}
