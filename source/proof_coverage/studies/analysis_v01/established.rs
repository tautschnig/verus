use vstd::prelude::*;

verus! {

// An established assertion: the intermediate assert is checked once and then
// assumed. The postcondition witness observes the established fact; the
// requirements that discharged the assert's own check are reached
// transitively through the assert certificate, not reported as
// available-not-observed at function scope.
proof fn established(a: int, b: int)
    requires
        a == 3,
        b == 4,
    ensures
        a + b == 7,
{
    assert(a + b == 7);
}

} // verus!

fn main() {}
