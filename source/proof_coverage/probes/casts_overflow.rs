use vstd::prelude::*;

verus! {

fn casts(a: u8, b: u16) -> (r: u64)
    ensures
        r == a as u64 + b as u64,
{
    let x: u32 = a as u32;
    let y: u32 = b as u32;
    let s: u32 = x + y;
    s as u64
}

fn wrapping(a: u32) -> (r: u32)
    ensures
        r == a.wrapping_add(1),
{
    a.wrapping_add(1)
}

fn main() {}

} // verus!
