use vstd::prelude::*;

verus! {

// The lemma hypothesis `x > 5` is unnecessary for the nonlinear goal
// (squares are nonnegative unconditionally): it appears in no support
// witness, and ablating it breaks nothing. With every row in this function
// resolved, the finding is an unoccluded candidate-redundant — stated as
// candidate only: confirm by re-verification before deleting.
proof fn square_nonneg(x: int)
    ensures x * x >= 0,
{
    assert(x * x >= 0) by (nonlinear_arith)
        requires x > 5 || x <= 5;
}

fn main() {}

} // verus!
