use vstd::prelude::*;

verus! {

// Baseline: the base-case premise proves the result nonnegative, while the
// recursive call's postcondition proves the recursive case.
proof fn recursive_nonnegative(n: nat, base: int) -> (r: int)
    requires
        base >= 0,
    ensures
        r >= 0,
    decreases n,
{
    if n == 0 {
        base
    } else {
        recursive_nonnegative((n - 1) as nat, base)
    }
}

// `spare >= 0` is irrelevant to the result and is not propagated to the
// recursive call: that call receives the constant 0 instead. The assertion
// merely repeats the entry fact and its established proposition is unused.
proof fn recursive_with_redundancy(n: nat, base: int, spare: int) -> (r: int)
    requires
        base >= 0,
        spare >= 0,
    ensures
        r >= 0,
    decreases n,
{
    if n == 0 {
        base
    } else {
        assert(spare >= 0);
        recursive_with_redundancy((n - 1) as nat, base, 0)
    }
}

} // verus!

fn main() {}
