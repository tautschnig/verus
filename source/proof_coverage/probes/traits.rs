use vstd::prelude::*;

verus! {

trait Shape {
    spec fn area(&self) -> int;

    fn scaled_area(&self, k: u32) -> (r: u64)
        requires
            self.area() >= 0,
            self.area() < 1000,
            k < 1000,
        ensures
            r as int == k * self.area();
}

struct Square {
    side: u32,
}

impl Shape for Square {
    spec fn area(&self) -> int {
        self.side * self.side
    }

    fn scaled_area(&self, k: u32) -> (r: u64)
        ensures
            r as int == k * self.area(),
    {
        proof {
            assert(self.area() < 1000);
        }
        assert(self.side < 32) by {
            assert(self.side * self.side < 1000);
            if self.side >= 32 {
                assert(self.side * self.side >= 32 * 32) by (nonlinear_arith)
                    requires self.side >= 32;
            }
        };
        let a: u64 = (self.side as u64) * (self.side as u64);
        proof {
            assert(a as int == self.area()) by (nonlinear_arith)
                requires a as int == self.side * self.side;
        }
        proof {
            assert((k as u64) * a < 1000 * 1000) by (nonlinear_arith)
                requires k < 1000, a < 1000;
            assert(k * self.area() == (k as u64) * a as int) by (nonlinear_arith)
                requires a as int == self.area();
        }
        (k as u64) * a
    }
}

fn use_shape<S: Shape>(s: &S) -> (r: u64)
    requires
        s.area() == 4,
    ensures
        r == 8,
{
    let r = s.scaled_area(2);
    assert(r as int == 2 * s.area());
    r
}

fn main() {
    let sq = Square { side: 2 };
    proof {
        assert(sq.area() == 4);
    }
    let x = use_shape(&sq);
}

} // verus!
