use vstd::prelude::*;

verus! {

fn double_calls(x: u32) -> (r: u32)
    requires x < 50,
    ensures r >= x,
{
    let a = add_one(x);      // site A
    let b = add_one(a);      // site B
    b
}

fn add_one(x: u32) -> (r: u32)
    requires x < 100,
    ensures r == x + 1,
{
    x + 1
}

#[verifier::loop_isolation(false)]
fn sum_no_iso(n: u32) -> (r: u32)
    requires n < 100,
    ensures r <= n,
{
    let mut i: u32 = 0;
    let mut acc: u32 = 0;
    while i < n
        invariant acc <= i, i <= n, n < 100,
        decreases n - i,
    {
        acc = acc + 1;
        i = i + 1;
    }
    acc
}

fn main() {}

} // verus!
