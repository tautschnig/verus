use vstd::prelude::*;

verus! {

// Ambient evidence with recorded identity. The first postcondition observes
// the spec function's definition axiom (SpecDefinition, owner `double`); the
// second observes the broadcast lemma's axiom (Broadcast, owner
// `double_is_even`). Identities come from the ambient tap, never from
// parsing axiom labels.
spec fn double(x: int) -> int {
    2 * x
}

broadcast proof fn double_is_even(x: int)
    ensures
        #[trigger] double(x) % 2 == 0,
{
}

proof fn uses_ambient(x: int)
    ensures
        double(x) == 2 * x,
        double(x) % 2 == 0,
{
    broadcast use double_is_even;
}

} // verus!

fn main() {}
