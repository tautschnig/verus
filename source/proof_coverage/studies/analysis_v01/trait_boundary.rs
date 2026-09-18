use vstd::prelude::*;

verus! {

trait Increment {
    fn inc(&self, x: u32) -> (r: u32)
        requires
            x < 10,
        ensures
            r == x + 1;
}

struct One {}

impl Increment for One {
    fn inc(&self, x: u32) -> (r: u32)
        ensures
            r == x + 1,
    {
        x + 1
    }
}

fn use_increment<I: Increment>(i: &I, x: u32) -> (r: u32)
    requires
        x < 10,
    ensures
        r == x + 1,
{
    i.inc(x)
}

} // verus!

fn main() {}
