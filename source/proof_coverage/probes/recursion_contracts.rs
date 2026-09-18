use vstd::prelude::*;

verus! {

// 1. Recursive requires: the call must satisfy the callee's precondition.
proof fn bounded(n: nat)
    requires n <= 100,
    ensures n * 0 == 0,
    decreases n,
{
    if n > 0 { bounded((n - 1) as nat); }
}

// 2. Nontrivial mutually recursive contracts: each side consumes the
// other's ensures.
spec fn parity(n: nat) -> bool decreases n { if n == 0 { true } else { !parity((n - 1) as nat) } }
proof fn even_p(n: nat)
    requires n % 2 == 0,
    ensures parity(n),
    decreases n,
{
    if n > 0 { odd_p((n - 1) as nat); }
}
proof fn odd_p(n: nat)
    requires n % 2 == 1,
    ensures !parity(n),
    decreases n,
{
    if n > 0 { even_p((n - 1) as nat); }
}

// 3. Recursive return value: exec recursion whose result feeds the ensures.
fn count_down(n: u32) -> (r: u32)
    ensures r == 0,
    decreases n,
{
    if n == 0 { 0 } else { count_down(n - 1) }
}

// 4. Exec recursion with termination disabled: no decreases, so no
// termination guard is inserted; the recursive call must appear WITHOUT a
// RecursiveCallRecord and stays outside any observed component.
#[verifier::exec_allows_no_decreases_clause]
fn spin(n: u32) -> (r: u32)
    ensures r <= n,
{
    if n > 1000 { spin(n) } else { 0 }
}

fn main() {}

} // verus!
