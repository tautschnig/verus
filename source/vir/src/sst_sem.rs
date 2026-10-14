//! A reference semantics of SST expressions for the `by (compute)` interpreter's correctness
//! (verus-work plan/28): `denote(e, sigma, m)` is the value AIR's encoding of `e`
//! (`sst_to_air::exp_to_expr` and the prelude) has in the model `m`, with the free variables
//! valued by `sigma`. `None`: `e` is outside the fragment (stage 1: integers and booleans), or
//! ill-typed.
//!
//! The model `m` holds what the encoding leaves uninterpreted: the clip functions outside their
//! ranges, Z3's `div`/`mod` by zero, the width bounds `uHi`/`iLo`/`iHi` outside the standard
//! widths, and `arch_size`. The interpreter is correct when its result has the same value as its
//! input in every model the prelude allows (`model_ok`), which is what `assert(e) by (compute)`
//! needs: a result `true` then means `e` is true in every model of the query.
//!
//! Spec code only (`cfg(verus_only)`): a normal build does not contain this module.

use crate::ast::{ArchWordBits, Constant, InequalityOp, IntRange, UnaryOp};
use crate::interpreter::InterpExp;
use crate::sst::{ArithOp, BinaryOp, BndX, Exp, ExpX, UniqueIdent};
use vstd::prelude::*;

verus! {

/// Values of the fragment
pub enum Val {
    Bool(bool),
    Int(int),
}

/// What the encoding leaves open (the prelude's uninterpreted functions and constants)
pub struct Model {
    /// `arch_size`
    pub arch_size: int,
    /// `uHi`, `iLo`, `iHi` (prelude axioms fix them at 8, 16, 32, 64, 128 bits)
    pub u_hi: spec_fn(int) -> int,
    pub i_lo: spec_fn(int) -> int,
    pub i_hi: spec_fn(int) -> int,
    /// `uClip`, `iClip`, `nClip`, `charClip` (the prelude fixes them inside their ranges)
    pub u_clip: spec_fn(int, int) -> int,
    pub i_clip: spec_fn(int, int) -> int,
    pub nat_clip: spec_fn(int) -> int,
    pub char_clip: spec_fn(int) -> int,
    /// Z3's `(div x 0)` and `(mod x 0)`
    pub div0: spec_fn(int) -> int,
    pub mod0: spec_fn(int) -> int,
}

pub open spec fn pow2(n: nat) -> int
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

/// The prelude's axioms about what `Model` holds (`prelude.rs`: `arch_size`, the width bounds,
/// the clip functions' ranges; the in-range identities are built into `denote`)
pub open spec fn model_ok(m: Model, arch: ArchWordBits) -> bool {
    &&& match arch {
        ArchWordBits::Either32Or64 => m.arch_size == 32 || m.arch_size == 64,
        ArchWordBits::Exactly(b) => m.arch_size == b as int,
    }
    &&& forall|b: nat| #![trigger pow2(b)] (b == 8 || b == 16 || b == 32 || b == 64 || b == 128) ==> {
        &&& (m.u_hi)(b as int) == pow2(b)
        &&& (m.i_lo)(b as int) == -pow2((b - 1) as nat)
        &&& (m.i_hi)(b as int) == pow2((b - 1) as nat)
    }
    &&& forall|b: int, i: int| 0 <= #[trigger] (m.u_clip)(b, i) < (m.u_hi)(b)
    &&& forall|b: int, i: int| (m.i_lo)(b) <= #[trigger] (m.i_clip)(b, i) < (m.i_hi)(b)
    &&& forall|i: int| 0 <= #[trigger] (m.nat_clip)(i)
    &&& forall|i: int| char_in_range(#[trigger] (m.char_clip)(i))
}

/// `charInv`: `[0, 0xD7FF]` or `[0xE000, 0x10FFFF]` (`unicode::CHAR_RANGE_*`)
pub open spec fn char_in_range(i: int) -> bool {
    (0 <= i <= 0xD7FF) || (0xE000 <= i <= 0x10FFFF)
}

pub open spec fn opt_val(sigma: Map<UniqueIdent, Val>, x: UniqueIdent) -> Option<Val> {
    if sigma.contains_key(x) { Some(sigma[x]) } else { None }
}

/// `Clip { range, truncate }`: `sst_to_air` encodes both kinds alike (`truncate` is ignored):
/// `IntRange::Int` is the value itself; otherwise `uClip`/`iClip`/`nClip`/`charClip` (with the
/// width, or `arch_size` for `USize`/`ISize`), which the prelude makes the identity in range.
pub open spec fn clip(range: IntRange, v: int, m: Model) -> int {
    match range {
        IntRange::Int => v,
        IntRange::Nat => if 0 <= v { v } else { (m.nat_clip)(v) },
        IntRange::Char => if char_in_range(v) { v } else { (m.char_clip)(v) },
        IntRange::U(b) => u_clip(b as int, v, m),
        IntRange::USize => u_clip(m.arch_size, v, m),
        IntRange::I(b) => i_clip(b as int, v, m),
        IntRange::ISize => i_clip(m.arch_size, v, m),
    }
}

pub open spec fn u_clip(b: int, v: int, m: Model) -> int {
    if 0 <= v < (m.u_hi)(b) { v } else { (m.u_clip)(b, v) }
}

pub open spec fn i_clip(b: int, v: int, m: Model) -> int {
    if (m.i_lo)(b) <= v < (m.i_hi)(b) { v } else { (m.i_clip)(b, v) }
}

/// `Arith` (`sst_to_air`: `Add`/`Sub`/`Mul`/`EucDiv`/`EucMod`, which the prelude equates with
/// `+ - * div mod`). Verus's `/` and `%` on `int` are Z3's (Euclidean) `div` and `mod`; by zero
/// they are Z3's uninterpreted `(div x 0)`, `(mod x 0)`.
pub open spec fn arith(op: ArithOp, x: int, y: int, m: Model) -> int {
    match op {
        ArithOp::Add => x + y,
        ArithOp::Sub => x - y,
        ArithOp::Mul => x * y,
        ArithOp::EuclideanDiv => if y != 0 { x / y } else { (m.div0)(x) },
        ArithOp::EuclideanMod => if y != 0 { x % y } else { (m.mod0)(x) },
    }
}

/// The value of `e`; `None` outside the fragment or when ill-typed. Each case is the
/// encoding's meaning (`sst_to_air::exp_to_expr`), quoted:
pub open spec fn denote(e: Exp, sigma: Map<UniqueIdent, Val>, m: Model) -> Option<Val>
    decreases e, 0int,
{
    match e.x {
        // `constant_to_expr`: `Bool(b)` and `Int(i)` (as an SMT numeral)
        ExpX::Const(Constant::Bool(b)) => Some(Val::Bool(b)),
        ExpX::Const(Constant::Int(i)) => Some(Val::Int(verus_spec_num_bigint::bi(i))),
        // `string_var(&suffix_local_unique_id(x))`: the variable; `FreeVar` is the interpreter's
        // name for a variable it found unbound (`cleanup_exp` turns it back into `Var`)
        ExpX::Var(x) => opt_val(sigma, x),
        ExpX::Interp(InterpExp::FreeVar(x)) => opt_val(sigma, x),
        ExpX::Unary(op, a) => match (op, denote(a, sigma, m)) {
            // `mk_not`
            (UnaryOp::Not, Some(Val::Bool(b))) => Some(Val::Bool(!b)),
            // the operand itself
            (UnaryOp::Trigger(_), Some(v)) => Some(v),
            // removed before `sst_to_air` (which panics on it); `as int` of an integer
            (UnaryOp::CastToInteger, Some(Val::Int(i))) => Some(Val::Int(i)),
            (UnaryOp::Clip { range, truncate: _ }, Some(Val::Int(i))) => Some(Val::Int(clip(range, i, m))),
            _ => None,
        },
        ExpX::Binary(op, l, r) => match (denote(l, sigma, m), denote(r, sigma, m)) {
            (Some(a), Some(b)) => binary(op, a, b, m),
            _ => None,
        },
        // `ite`: total, so the branch not taken need not be in the fragment
        ExpX::If(c, t, f) => match denote(c, sigma, m) {
            Some(Val::Bool(true)) => denote(t, sigma, m),
            Some(Val::Bool(false)) => denote(f, sigma, m),
            _ => None,
        },
        // `mk_let`: an SMT `let`, which binds in parallel: every binder's expression is valued
        // in the outer environment
        ExpX::Bind(bnd, body) => match bnd.x {
            BndX::Let(bs) => match denote_binders(bs@, 0, sigma, m) {
                Some(new) => denote(body, sigma.union_prefer_right(new), m),
                None => None,
            },
            _ => None,
        },
        // the body (triggers only steer instantiation)
        ExpX::WithTriggers(_, body) => denote(body, sigma, m),
        _ => None,
    }
}

/// The values of the binders `bs[i..]`, each valued in `sigma`; a later binder of the same name
/// wins, as in `mk_let`'s SMT `let` (which Verus never produces: binder names are distinct)
pub open spec fn denote_binders(
    bs: Seq<crate::ast::VarBinder<Exp>>,
    i: int,
    sigma: Map<UniqueIdent, Val>,
    m: Model,
) -> Option<Map<UniqueIdent, Val>>
    decreases bs, bs.len() - i,
{
    if i < 0 || i >= bs.len() {
        Some(Map::empty())
    } else {
        match (denote(bs[i].a, sigma, m), denote_binders(bs, i + 1, sigma, m)) {
            (Some(v), Some(rest)) => Some(map![bs[i].name => v].union_prefer_right(rest)),
            _ => None,
        }
    }
}

/// `Binary`: `mk_and`, `mk_or`, `mk_xor`, `mk_implies`, `=`, `not (=)`, `<= < >= >`, `arith`
pub open spec fn binary(op: BinaryOp, a: Val, b: Val, m: Model) -> Option<Val> {
    match (op, a, b) {
        (BinaryOp::And, Val::Bool(x), Val::Bool(y)) => Some(Val::Bool(x && y)),
        (BinaryOp::Or, Val::Bool(x), Val::Bool(y)) => Some(Val::Bool(x || y)),
        (BinaryOp::Xor, Val::Bool(x), Val::Bool(y)) => Some(Val::Bool(x != y)),
        (BinaryOp::Implies, Val::Bool(x), Val::Bool(y)) => Some(Val::Bool(!x || y)),
        (BinaryOp::Eq, _, _) => Some(Val::Bool(a == b)),
        (BinaryOp::Ne, _, _) => Some(Val::Bool(a != b)),
        (BinaryOp::Inequality(InequalityOp::Le), Val::Int(x), Val::Int(y)) => Some(Val::Bool(x <= y)),
        (BinaryOp::Inequality(InequalityOp::Lt), Val::Int(x), Val::Int(y)) => Some(Val::Bool(x < y)),
        (BinaryOp::Inequality(InequalityOp::Ge), Val::Int(x), Val::Int(y)) => Some(Val::Bool(x >= y)),
        (BinaryOp::Inequality(InequalityOp::Gt), Val::Int(x), Val::Int(y)) => Some(Val::Bool(x > y)),
        (BinaryOp::Arith(aop), Val::Int(x), Val::Int(y)) => Some(Val::Int(arith(aop, x, y, m))),
        _ => None,
    }
}

/// An environment (the interpreter's `env`: bound variables to their values) agrees with
/// `sigma`: each bound variable's value is what its expression denotes
pub open spec fn env_agrees(env: Map<UniqueIdent, Exp>, sigma: Map<UniqueIdent, Val>, m: Model) -> bool {
    forall|x: UniqueIdent| #[trigger] env.contains_key(x) ==> opt_val(sigma, x) == denote(env[x], sigma, m)
}

/// Functional correctness of one evaluation (plan/28 (FC)): in every model the prelude allows,
/// for every valuation that agrees with the environment, if `e` has a value then `e2` has the
/// same value
#[verifier::opaque]
pub open spec fn fc(env: Map<UniqueIdent, Exp>, arch: ArchWordBits, e: Exp, e2: Exp) -> bool {
    forall|sigma: Map<UniqueIdent, Val>, m: Model|
        model_ok(m, arch) && env_agrees(env, sigma, m) && #[trigger] denote(e, sigma, m) is Some
            ==> denote(e2, sigma, m) == denote(e, sigma, m)
}

/// An unchanged expression is correct
pub proof fn lemma_fc_refl(env: Map<UniqueIdent, Exp>, arch: ArchWordBits, e: Exp)
    ensures fc(env, arch, e, e),
{
    reveal(fc);
}

} // verus!
