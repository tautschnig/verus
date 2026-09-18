use vstd::prelude::*;

verus! {

proof fn uncovered_premise(p: bool, q: bool)
    requires
        p,
        q,
    ensures
        p,
{
}

proof fn vacuous_obligation(p: bool, r: int)
    requires
        p,
        !p,
        r > 0,
        r > 15,
    ensures
        false,
{
}

} // verus!

fn main() {}
