use vstd::prelude::*;

// Adversarial probe for the loop-exit attribution rules. Each function is a
// near-match trap: a rule keyed on shape or structural equality would
// misattribute here; the construction-exact rules must either attribute
// correctly (pointer identity) or leave rows Unresolved. The sweep asserts
// no audit violation; the specific expectations are checked by
// tools/check_adversarial.py-style assertions in the sweep commit tests.

verus! {

// 1. Two syntactically identical invariant clauses (distinct spans, distinct
// Expr allocations). Structural equality would join both exit assumes to the
// *first* clause's span; pointer identity must keep them separate.
fn duplicate_invariants(n: u32) -> (r: u32)
    requires
        n <= 100,
    ensures
        r <= n,
{
    let mut i: u32 = 0;
    while i < n
        invariant
            i <= n,
            i <= n,
        decreases n - i,
    {
        i = i + 1;
    }
    i
}

// 2. A loop with `ensures` clauses (exit-only facts with no entry check).
// The exit assumes of the ensures clauses have no armed entry expression to
// match; they must stay Unresolved rather than being force-matched.
fn loop_with_ensures(n: u32) -> (r: u32)
    requires
        n >= 1,
        n <= 100,
    ensures
        r >= 1,
{
    let mut i: u32 = 0;
    loop
        invariant_except_break
            i < n,
            n <= 100,
        ensures
            i >= 1,
            i <= n,
        decreases n - i,
    {
        i = i + 1;
        if i >= n {
            break;
        }
    }
    i
}

// 3. Complex loop condition (short-circuit && lowers through temporaries).
// The negated-condition rule must attribute exactly one Not(..) assume in
// the exit region, not any temporary-evaluation artifacts.
fn complex_condition(n: u32, flag: bool) -> (r: u32)
    requires
        n <= 100,
    ensures
        r <= n,
{
    let mut i: u32 = 0;
    while i < n && flag
        invariant
            i <= n,
        decreases n - i,
    {
        i = i + 1;
    }
    i
}

// 4. An unrelated negated proposition immediately after a loop. The
// exit-condition arm must already be disarmed (consumed by the loop's own
// negated condition), so this assert's implied assume must be attributed by
// the asserted-proposition rule, never as a loop exit condition.
fn unrelated_negation(n: u32) -> (r: u32)
    requires
        n <= 100,
    ensures
        r <= 100,
{
    let mut i: u32 = 0;
    while i < n
        invariant
            i <= n,
            n <= 100,
        decreases n - i,
    {
        i = i + 1;
    }
    assert(!(i > 100));
    i
}

// 5. An invariant clause structurally identical to a plain assertion that
// precedes the loop. If exit matching used structural equality, the
// assertion's expression could be captured as an "entry check"; with
// pointer identity plus the phase gate (only loop.establish arms), it
// cannot.
fn lookalike_assert(n: u32) -> (r: u32)
    requires
        n <= 100,
    ensures
        r <= n,
{
    let mut i: u32 = 0;
    assert(i <= n);
    while i < n
        invariant
            i <= n,
        decreases n - i,
    {
        i = i + 1;
    }
    i
}

// 6. A user-written assume(false) (dead code marker). Shape-wise identical
// to a synthesized path-termination fact; only the SST intent (UserAssume vs
// PathTermination) distinguishes them, which is why the const-false shape
// rule was demoted to Unresolved and the intent flows through alignment.
#[verifier::exec_allows_no_decreases_clause]
fn user_assume_false(n: u32) -> (r: u32)
    ensures
        r == 42,
{
    if n > 1000000 {
        proof {
            assume(false);
        }
        return 0;
    }
    42
}

fn main() {}

} // verus!
