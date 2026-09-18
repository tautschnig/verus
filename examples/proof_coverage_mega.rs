// rust_verify/tests/example.rs expect-success
use vstd::prelude::*;

verus! {

// An opaque top-level specification forces the final proof to use the
// revealing lemma rather than unfolding the definition automatically.
#[verifier::opaque]
spec fn expected_result(limit: u64) -> int {
    5 * (limit as int) + 2
}

proof fn lemma_expected_result(limit: u64)
    ensures
        expected_result(limit) == 5 * (limit as int) + 2,
{
    reveal(expected_result);
}

proof fn lemma_phase_arithmetic(limit: u64)
    requires
        limit <= 7,
    ensures
        3 * limit + 2 * limit == 5 * limit,
        5 * limit <= 35,
        5 * limit + 1 <= 36,
        5 * limit + 2 <= 37,
        limit <= 5 * limit + 2,
{
}

// The trait contract contributes a call precondition and several independent
// postconditions. Generic callers can use only these guarantees.
trait Increment {
    fn increment(&self, input: u64) -> (output: u64)
        requires
            input <= 40,
        ensures
            output == input + 1,
            output > input,
            output <= 41,
            output != input,
    ;
}

struct AddOne;

impl Increment for AddOne {
    fn increment(&self, input: u64) -> (output: u64) {
        input + 1
    }
}

fn increment_twice<I: Increment>(incrementer: &I, input: u64) -> (output: u64)
    requires
        input <= 39,
    ensures
        output == input + 2,
        output > input,
        output >= 2,
        output <= 41,
        output != input,
{
    let first = incrementer.increment(input);
    assert(first == input + 1);
    assert(first > input);
    assert(first <= 40);

    let second = incrementer.increment(first);
    assert(second == first + 1);
    assert(second > first);
    second
}

// Three inner iterations are performed for each outer iteration. Disabling
// loop isolation keeps the surrounding facts available to the loop queries.
#[verifier::loop_isolation(false)]
fn nested_phase(limit: u64) -> (total: u64)
    requires
        limit <= 10,
    ensures
        total == 3 * limit,
        total <= 30,
        total >= limit,
        limit == 0 ==> total == 0,
        limit > 0 ==> total > 0,
{
    let mut outer: u64 = 0;
    let mut total: u64 = 0;

    while outer < limit
        invariant
            outer <= limit,
            total == 3 * outer,
            total <= 3 * limit,
            total <= 30,
            outer == 0 ==> total == 0,
            outer > 0 ==> total > 0,
        decreases
            limit - outer,
    {
        let ghost total_at_outer_start = total;
        let mut inner: u64 = 0;

        while inner < 3
            invariant
                outer < limit,
                outer <= limit,
                inner <= 3,
                total_at_outer_start == 3 * outer,
                total == total_at_outer_start + inner,
                total == 3 * outer + inner,
                total <= 3 * limit,
                total <= 30,
                inner == 0 ==> total == total_at_outer_start,
                inner > 0 ==> total > total_at_outer_start,
            decreases
                3 - inner,
        {
            total = total + 1;
            inner = inner + 1;
        }

        assert(inner == 3);
        assert(total == 3 * outer + 3);
        outer = outer + 1;
        assert(total == 3 * outer);
    }

    assert(outer == limit);
    total
}

// A separate for-loop phase contributes iterator invariants and ordinary
// mutable assignments.
fn for_phase(limit: u64) -> (total: u64)
    requires
        limit <= 10,
    ensures
        total == 2 * limit,
        total <= 20,
        total >= limit,
        limit == 0 ==> total == 0,
        limit > 0 ==> total > 0,
{
    let mut steps: u64 = 0;
    let mut total: u64 = 0;

    for i in 0..limit
        invariant
            limit <= 10,
            i <= limit,
            steps == i,
            steps <= limit,
            total == 2 * i,
            total == 2 * steps,
            total <= 2 * limit,
            total <= 20,
            i == 0 ==> total == 0,
            i > 0 ==> total > 0,
    {
        total = total + 2;
        steps = steps + 1;
    }

    assert(steps == limit);
    total
}

// This loop preserves the value computed by for_phase while changing its
// representation from "remaining work" to "completed steps".
fn drain_phase(value: u64) -> (steps: u64)
    requires
        value <= 20,
    ensures
        steps == value,
        steps <= 20,
        value == 0 ==> steps == 0,
        value > 0 ==> steps > 0,
{
    let mut remaining = value;
    let mut steps: u64 = 0;

    while remaining > 0
        invariant
            value <= 20,
            remaining <= value,
            steps <= value,
            steps + remaining == value,
            steps <= 20,
            remaining <= 20,
            remaining == value ==> steps == 0,
            steps > 0 ==> remaining < value,
        decreases
            remaining,
    {
        remaining = remaining - 1;
        steps = steps + 1;
    }

    assert(remaining == 0);
    steps
}

// The branch condition and disjunctive postcondition add a different shape of
// proof dependency from the arithmetic loops.
fn choose_larger(a: u64, b: u64) -> (result: u64)
    requires
        a <= 30,
        b <= 20,
    ensures
        result >= a,
        result >= b,
        result == a || result == b,
        result <= 30,
        a >= b ==> result == a,
        b > a ==> result == b,
{
    if a >= b {
        a
    } else {
        b
    }
}

fn mega_example<I: Increment>(limit: u64, incrementer: &I) -> (result: u64)
    requires
        limit <= 7,
    ensures
        result == 5 * limit + 2,
        result <= 37,
        result >= 2,
        result > limit,
        result as int == expected_result(limit),
{
    let nested_total = nested_phase(limit);
    assert(nested_total == 3 * limit);
    assert(nested_total <= 30);
    assert(nested_total >= limit);

    let for_total = for_phase(limit);
    assert(for_total == 2 * limit);
    assert(for_total <= 20);
    assert(for_total >= limit);

    let drained_total = drain_phase(for_total);
    assert(drained_total == for_total);
    assert(drained_total == 2 * limit);

    let larger = choose_larger(nested_total, drained_total);
    assert(larger >= nested_total);
    assert(larger >= drained_total);
    assert(larger == nested_total || larger == drained_total);
    assert(larger <= 30);

    if larger == nested_total {
        assert(larger >= drained_total);
    } else {
        assert(larger == drained_total);
        assert(larger >= nested_total);
    }

    proof {
        lemma_phase_arithmetic(limit);
    }

    // Deliberately use an ordinary assignment before the trait call.
    let mut combined: u64 = 0;
    combined = nested_total + drained_total;
    assert(combined == 3 * limit + 2 * limit);
    assert(combined == 5 * limit);
    assert(combined <= 35);

    let bumped = increment_twice(incrementer, combined);
    assert(bumped == combined + 2);
    assert(bumped == 5 * limit + 2);
    assert(bumped <= 37);

    proof {
        lemma_expected_result(limit);
    }
    assert(bumped as int == expected_result(limit));
    bumped
}

fn main() {
    let incrementer = AddOne;

    let zero = mega_example(0, &incrementer);
    assert(zero == 2);

    let middle = mega_example(4, &incrementer);
    assert(middle == 22);

    let upper = mega_example(7, &incrementer);
    assert(upper == 37);
}

} // verus!
