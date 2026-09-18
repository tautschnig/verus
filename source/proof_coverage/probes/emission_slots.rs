// Emission-slot probe.
//
// Each function isolates one lowering template that has more than one named
// slot, so the recorded provenance can be compared against the slot the
// clause was actually emitted into.
//
// The load-bearing case is `three_clause_shapes`. `sst_to_air.rs:2760` splits
// the declared invariants into two vectors:
//
//     for inv in invs.iter() {
//         if inv.at_entry { invs_entry.push(..) }
//         if inv.at_exit  { invs_exit.push(..) }
//     }
//
// so a plain `invariant` (at_entry && at_exit) is pushed into BOTH. An ordinal
// taken from either split vector gives one source clause two identities, and
// makes two different clauses collide on index 0:
//
//     declared:    [0] invariant_except_break   [1] invariant   [2] ensures
//     invs_entry:  [0] except_break             [1] invariant
//     invs_exit:                                [0] invariant   [1] ensures
//
// Reading the exit slot with a split ordinal therefore attributes `invariant`
// to `invariant_except_break`. The ordinal must come from the declaring
// iteration, which is what this probe detects.

use vstd::prelude::*;

verus! {

// 1. Three LoopInv shapes on one loop.
//    invariant_except_break -> at_entry only
//    invariant              -> at_entry && at_exit  (the double push)
//    ensures                -> at_exit only
//    Exercises: LoopEstablish, LoopBodyEntry, LoopMaintain, LoopExit,
//    and the at-break assert of invs_exit.
fn three_clause_shapes(n: u32) -> (r: u32)
    requires
        n <= 100,
    ensures
        r <= 100,
{
    let mut i: u32 = 0;
    loop
        invariant_except_break
            i <= n,
        invariant
            n <= 100,
        ensures
            i <= 100,
        decreases n - i,
    {
        if i >= n {
            break;
        }
        i = i + 1;
    }
    i
}

// 2. A `while` loop forces every clause to at_entry && at_exit
//    (sst_to_air.rs:2763 asserts this when cond.is_some()), so both clauses
//    are pushed into both vectors. Two clauses must keep distinct ordinals
//    across all four entry/exit slots, and the negated loop condition must be
//    attributed to the exit-condition slot rather than to a clause.
fn while_two_invariants(n: u32) -> (r: u32)
    requires
        n <= 50,
    ensures
        r <= 50,
{
    let mut i: u32 = 0;
    let mut acc: u32 = 0;
    while i < n
        invariant
            i <= n,
            acc <= i,
        decreases n - i,
    {
        acc = acc + 1;
        i = i + 1;
    }
    acc
}

// 3. Nested loops: ordinals are per-loop, not per-query. The inner loop's
//    clause 0 must not be confused with the outer loop's clause 0.
fn nested_loops(n: u32) -> (r: u32)
    requires
        n <= 10,
    ensures
        r <= 10,
{
    let mut outer: u32 = 0;
    let mut seen: u32 = 0;
    while outer < n
        invariant
            outer <= n,
            seen <= n,
        decreases n - outer,
    {
        let mut inner: u32 = 0;
        while inner < n
            invariant
                inner <= n,
                seen <= n,
            decreases n - inner,
        {
            inner = inner + 1;
        }
        seen = inner;
        outer = outer + 1;
    }
    seen
}

// 4. Branch conditions: the then-arm assumes the condition and the else-arm
//    assumes its negation. Both are emitted by the same If template
//    (sst_to_air.rs:2598) and are currently told apart by walk position.
fn branches(a: u32, b: u32) -> (r: u32)
    requires
        a <= 10,
        b <= 10,
    ensures
        r <= 20,
{
    let mut out: u32 = 0;
    if a < b {
        out = a + b;
    } else {
        out = b + a;
    }
    out
}

// 5. A user assert exports its checked proposition as an assumption.
//    AssumeIntent::AssertedProposition already names this slot; the probe
//    shows whether the exact path or the positional walk rule attributes it.
fn assert_export(x: u32) -> (r: u32)
    requires
        x <= 10,
    ensures
        r >= 2,
{
    assert(x >= 0);
    let y = x + 2;
    assert(y >= 2);
    y
}

// 6. Several requires and several ensures clauses, so contract occurrences
//    must be told apart by clause ordinal rather than by span.
fn multi_contract(a: u32, b: u32) -> (r: u32)
    requires
        a <= 10,
        b <= 10,
        a <= b,
    ensures
        r >= a,
        r >= b,
        r <= 20,
{
    b + (b - a) - (b - a)
}

// 7. assert-forall: the AssertQuery template has requires-check,
//    requires-assume, goal, and ensures-assume slots.
spec fn is_even(x: int) -> bool {
    x % 2 == 0
}

proof fn assert_forall_slots()
    ensures
        forall|k: int| 0 <= k < 4 ==> is_even(#[trigger] (2 * k)),
{
    assert forall|k: int| 0 <= k < 4 implies is_even(#[trigger] (2 * k)) by {
        assert(2 * k == k + k);
    }
}

// 8. The final invariant is syntactically a negation. Exact LoopExit slot
//    metadata must keep it classified as an invariant; the positional
//    fallback must not reinterpret it as the loop's negated exit condition.
fn negated_final_invariant(n: u32) -> (r: u32)
    requires
        n <= 50,
    ensures
        r <= 50,
{
    let mut i: u32 = 0;
    let failed: bool = false;
    while i < n
        invariant
            i <= n,
            !failed,
        decreases n - i,
    {
        i = i + 1;
    }
    i
}

fn main() {}

} // verus!
