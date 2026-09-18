use vstd::prelude::*;

verus! {

fn ghost_probe(n: u32) -> (r: u32)
    requires
        n < 100,
    ensures
        r == n + 1,
{
    let ghost g: int = n as int;
    let r = n + 1;
    proof {
        assert(r as int == g + 1);
    }
    r
}

fn main() {}

} // verus!
