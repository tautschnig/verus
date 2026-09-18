use vstd::prelude::*;

verus! {

#[verifier::exec_allows_no_decreases_clause]
fn pattern_and_control_probe(mut input: Option<u64>, gate: bool) {
    let Some(first) = input else {
        return;
    };

    let second = if let Some(value) = input {
        value
    } else {
        0
    };

    while let Some(_value) = input {
        input = None;
    }

    let mut observed = 0;
    if gate && {
        observed = first;
        second > 0
    } {
        observed = second;
    }

    let increment = |value: u64| -> (result: u64)
        requires
            value < u64::MAX,
        ensures
            result == value + 1,
    {
        value + 1
    };
    if first < u64::MAX {
        let next = increment(first);
        assert(next == first + 1);
    }

    assert(observed == 0 || observed == first);
}

async fn async_one() -> (result: usize)
    ensures
        result == 1,
{
    1
}

async fn await_probe() {
    let future = async_one();
    let value = future.await;
    assert(value == 1);
}

fn tail_bool() -> (result: bool)
    ensures
        result,
{
    true
}

fn tail_tuple_after_mut(value: &mut u64) -> (result: (u64, bool))
    ensures
        result.1,
{
    let observed = *value;
    (observed, true)
}

fn unit_tail_branch(gate: bool)
    ensures
        true,
{
    if gate {
    } else {
    }
}

fn main() {}

} // verus!
