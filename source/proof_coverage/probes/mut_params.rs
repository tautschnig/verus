use vstd::prelude::*;

verus! {

fn bump(x: &mut u32)
    requires
        *old(x) < 100,
    ensures
        *final(x) == *old(x) + 1,
{
    *x = *x + 1;
}

fn early_return(a: u32) -> (r: u32)
    ensures
        r >= a,
{
    if a > 50 {
        return a;
    }
    let mut b = a;
    bump(&mut b);
    b
}

fn main() {}

} // verus!
