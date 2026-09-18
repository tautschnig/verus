use vstd::prelude::*;

verus! {

// The requirement is needed only by the generated overflow check for `-x`,
// an auxiliary obligation outside the postcondition slice. The function
// finding keeps the available-not-observed statement and qualifies it with
// the auxiliary terminal that did observe the requirement. The postcondition
// witness itself is carried by generated facts: both branch conditions, the
// parameter's type invariant, and the result assignment.
fn abs_like(x: i32) -> (r: i32)
    requires
        x > i32::MIN,
    ensures
        r >= 0,
{
    let r: i32;
    if x < 0 {
        r = -x;
    } else {
        r = x;
    }
    r
}

} // verus!

fn main() {}
