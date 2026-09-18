use vstd::prelude::*;

verus! {

// 1. direct recursion
spec fn sum_to(n: nat) -> nat decreases n { if n == 0 { 0 } else { n + sum_to((n - 1) as nat) } }
proof fn direct(n: nat) ensures sum_to(n) >= n, decreases n {
    if n > 0 { direct((n - 1) as nat); }
}

// 2. multiple recursive calls in one body
proof fn multi(n: nat) ensures sum_to(n) >= n, decreases n {
    if n > 1 { multi((n - 1) as nat); multi((n - 2) as nat); }
    else if n == 1 { multi(0); }
}

// 3. mutual recursion
proof fn even_case(n: nat) ensures true, decreases n, 1int {
    if n > 0 { odd_case((n - 1) as nat); }
}
proof fn odd_case(n: nat) ensures true, decreases n, 0int {
    if n > 0 { even_case((n - 1) as nat); }
}

// 4. lexicographic decreases
proof fn lex(a: nat, b: nat) ensures true, decreases a, b {
    if b > 0 { lex(a, (b - 1) as nat); }
    else if a > 0 { lex((a - 1) as nat, 100); }
}

fn main() {}

} // verus!
