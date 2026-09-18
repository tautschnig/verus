use vstd::prelude::*;

// Adversarial probe for dependency precision: independent obligations must
// not borrow each other's support. A whole-batch core is a joint witness —
// only focused (per-terminal) evidence plus prefix discipline keeps x-facts
// out of y-obligations. Validated by tools: backward closure of the
// y-assertion must not contain x's defining premises, and ablating one
// branch's support must not break the other branch's obligation.

verus! {

// 1. Two independent assertion chains in straight line: x-facts must not
// appear in the y-assertion's support.
fn independent_straight(a: u32, b: u32) -> (r: u32)
    requires
        a < 100,
        b < 100,
    ensures
        r == a + b,
{
    let x = a + 1;
    let y = b + 2;
    assert(x == a + 1);
    assert(y == b + 2);
    (x - 1) + (y - 2)
}

// 2. Independent obligations in separate branch arms: the then-arm's
// premises must not support the else-arm's obligation.
fn independent_branches(c: bool, n: u32) -> (r: u32)
    requires
        n < 100,
    ensures
        r <= n + 5,
{
    if c {
        let p = n + 3;
        assert(p == n + 3);
        p
    } else {
        let q = n + 5;
        assert(q == n + 5);
        q
    }
}

fn main() {}

} // verus!
