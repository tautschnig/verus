use vstd::prelude::*;

verus! {

proof fn joint_chain(p: bool, q: bool, unused: bool)
    requires
        p,
        p ==> q,
        unused,
    ensures
        q,
{
}

} // verus!

fn main() {}
