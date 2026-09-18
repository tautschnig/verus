use vstd::prelude::*;

// Negative probes for the return-binding predicted row: none of these
// functions may get a predicted VarEquality return row, and alignment
// counts must still agree (0 unresolved is not required; no
// misattribution is).

verus! {

// 1. Return with NO postcondition: sst_to_air skips all postcondition
// work, no assume_var is emitted, no row may be predicted.
fn no_postcondition(a: u32) -> u32 {
    if a > 10 {
        return a;
    }
    a + 1
}

// 2. Postcondition with no named return destination (implicit unit).
fn unit_return(a: u32)
    ensures
        a == a,
{
}

// 3. Named destination + postcondition: the positive case (one predicted
// row per return site).
fn named_return(a: u32) -> (r: u32)
    requires
        a < 100,
    ensures
        r >= a,
{
    if a > 50 {
        return a;
    }
    a + 1
}

fn main() {}

} // verus!
