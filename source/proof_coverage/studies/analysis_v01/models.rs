use vstd::prelude::*;

verus! {

// Four sound models in one example.
//
// 1. assert-forall as a checked export: the proved body licenses the exported
//    quantified conclusion, so `value > 0` reaches the postcondition
//    transitively instead of looking auxiliary-only.
proof fn all_positive(values: Seq<u64>, value: u64)
    requires
        value > 0,
        forall|i: int| 0 <= i < values.len() ==> values[i] == value,
    ensures
        forall|i: int| 0 <= i < values.len() ==> values[i] > 0,
{
    assert forall|i: int| 0 <= i < values.len() implies values[i] > 0 by {
        assert(values[i] == value);
    }
}

// 2. for loops: the desugaring collapses several invariant spans onto the loop
//    header and the iterator, so clause identity comes from count-guarded
//    ordinal alignment per protocol position rather than span equality.
fn fill(length: usize, value: u64) -> (values: Vec<u64>)
    requires
        length <= 8,
    ensures
        values.len() == length,
{
    let mut values: Vec<u64> = Vec::new();
    for i in 0..length
        invariant
            length <= 8,
            values.len() == i,
    {
        values.push(value);
    }
    values
}

// 3. clause groups: `invariant_except_break` holds at entry and at every latch
//    but is not exported past a break, so it must not receive an exit
//    certificate; a plain `invariant` must.
fn count_to_limit(limit: u64) -> (count: u64)
    requires
        1 <= limit,
        limit <= 10,
    ensures
        count == limit,
{
    let mut count: u64 = 0;
    loop
        invariant_except_break
            count < limit,
        invariant
            count <= limit,
        ensures
            count == limit,
        decreases
            limit - count,
    {
        count = count + 1;
        if count == limit {
            break;
        }
    }
    count
}

// 4. trait refinement: the contract clauses are declared on the trait, so the
//    implementation's obligations project onto the trait's clause artifacts
//    through the recorded impl-to-trait relation.
trait Bounded {
    spec fn ok(&self, input: u64) -> bool;

    fn clamp(&self, input: u64) -> (output: u64)
        requires
            self.ok(input),
        ensures
            output == input,
    ;
}

struct UpToTen;

impl Bounded for UpToTen {
    spec fn ok(&self, input: u64) -> bool {
        input <= 10
    }

    fn clamp(&self, input: u64) -> (output: u64) {
        input
    }
}

// 5. no declared goals: the root policy reports `no-declared-goals` rather
//    than an empty analysis.
fn rootless(input: u64) {
    let doubled = input / 2;
    assert(doubled <= input);
}

} // verus!

fn main() {}
