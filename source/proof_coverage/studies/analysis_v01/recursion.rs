use vstd::prelude::*;

verus! {

fn self_count(n: u32) -> (r: u32)
    ensures
        r == 0,
    decreases n,
{
    if n == 0 { 0 } else { self_count(n - 1) }
}

spec fn parity(n: nat) -> bool
    decreases n,
{
    if n == 0 { true } else { !parity((n - 1) as nat) }
}

proof fn even_p(n: nat)
    requires
        n % 2 == 0,
    ensures
        parity(n),
    decreases n,
{
    if n > 0 {
        odd_p((n - 1) as nat);
    }
}

proof fn odd_p(n: nat)
    requires
        n % 2 == 1,
    ensures
        !parity(n),
    decreases n,
{
    if n > 0 {
        even_p((n - 1) as nat);
    }
}

} // verus!

fn main() {}
