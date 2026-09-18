use vstd::prelude::*;

verus! {

// The contract is declared on the trait. Two implementations refine it: `One`
// with the trait's contract, `Two` with a stronger postcondition of its own.
trait Step {
    fn step(&self, x: u32) -> (r: u32)
        requires
            x < 10,
        ensures
            r > x;
}

struct One {}
struct Two {}

impl Step for One {
    fn step(&self, x: u32) -> (r: u32)
        ensures
            r > x,
    {
        x + 1
    }
}

impl Step for Two {
    fn step(&self, x: u32) -> (r: u32)
        ensures
            r > x,
            r == x + 2,
    {
        x + 2
    }
}

// A generic call: the verifier assumes the trait's postcondition. Its truth
// for the verified program rests on every implementation refining it.
fn via_trait<S: Step>(s: &S, x: u32) -> (r: u32)
    requires
        x < 10,
    ensures
        r > x,
{
    s.step(x)
}

// A statically resolved call: the verifier assumes `Two`'s own postcondition,
// which is what lets the caller prove the exact value.
fn via_impl(x: u32) -> (r: u32)
    requires
        x < 10,
    ensures
        r == x + 2,
{
    let two = Two {};
    two.step(x)
}

// Even though the argument is concretely `Two`, this call crosses the
// `via_trait` contract boundary, which promises only `r > x`.
fn top_via_trait(x: u32)
    requires
        x < 10,
{
    let two = Two {};
    let r = via_trait(&two, x);
    assert(r > x);
    // assert(r == x + 2); // Fails: `via_trait` does not promise this.
}

// Calling the implementation directly exposes `Two::step`'s stronger
// postcondition to the caller.
fn top_direct(x: u32)
    requires
        x < 10,
{
    let two = Two {};
    let r = two.step(x);
    assert(r == x + 2);
}

} // verus!

fn main() {}
