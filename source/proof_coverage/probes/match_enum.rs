use vstd::prelude::*;

verus! {

enum Tree {
    Leaf(u32),
    Node(Box<Tree>, Box<Tree>),
}

impl Tree {
    spec fn sum(&self) -> int
        decreases self,
    {
        match self {
            Tree::Leaf(v) => *v as int,
            Tree::Node(l, r) => l.sum() + r.sum(),
        }
    }
}

fn max_leaf(t: &Tree) -> (m: u32)
    ensures
        m as int <= t.sum(),
    decreases t,
{
    match t {
        Tree::Leaf(v) => *v,
        Tree::Node(l, r) => {
            let a = max_leaf(l);
            let b = max_leaf(r);
            proof {
                assert(l.sum() >= 0 && r.sum() >= 0) by {
                    sum_nonneg(l);
                    sum_nonneg(r);
                };
            }
            if a > b { a } else { b }
        }
    }
}

proof fn sum_nonneg(t: &Tree)
    ensures
        t.sum() >= 0,
    decreases t,
{
    match t {
        Tree::Leaf(_) => {}
        Tree::Node(l, r) => {
            sum_nonneg(l);
            sum_nonneg(r);
        }
    }
}

fn main() {}

} // verus!
