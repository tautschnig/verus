use vstd::prelude::*;

verus! {

spec fn f(i: int) -> int {
    2 * i
}

proof fn forall_probe()
    ensures
        forall|i: int| 0 <= i < 10 ==> f(i) % 2 == 0,
{
    assert forall|i: int| 0 <= i < 10 implies f(i) % 2 == 0 by {
        assert(f(i) == 2 * i);
    };
}

fn main() {
    proof {
        forall_probe();
    }
}

} // verus!
