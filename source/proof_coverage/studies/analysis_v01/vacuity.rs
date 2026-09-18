use vstd::prelude::*;

verus! {

proof fn contradictory(p: bool, unrelated: bool)
    requires
        p,
        !p,
        unrelated,
    ensures
        false,
{
}

} // verus!

fn main() {}
