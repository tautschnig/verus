use vstd::prelude::*;

verus! {

// Vacuous: contradictory requires make every obligation hold trivially.
proof fn vacuous_lemma(x: int)
    requires x > 0, x < 0,
    ensures x == 42,
{
}

// Vacuous branch: the assert inside the dead branch is never exercised.
fn dead_branch(x: u32) -> (r: u32)
    requires x < 10,
    ensures r >= x,
{
    if x < 10 {
        x + 1
    } else {
        assert(x > 100);
        x
    }
}

// Non-vacuous control.
proof fn honest_lemma(x: int)
    requires x > 0,
    ensures x + 1 > 1,
{
}

} // verus!

fn main() {}
