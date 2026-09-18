//! Classification rules: reading the encoding, never guessing.
//!
//! Three signal tiers, all derived from what the verifier itself constructs
//! (`PROOF_COVERAGE.md` §3):
//!
//! 1. Reserved head symbols (`ens%f`, `req%f`, `fuel_bool`, `has_type`,
//!    literal `false`) — the encoding's own vocabulary from `vir::def`.
//! 2. Structure: an `Assume` directly following an `Assert` of the same
//!    formula is the asserted proposition; the first `Assume` of a `Switch`
//!    arm is that arm's branch condition.
//! 3. Diagnostics *constants*: obligation messages are matched exactly
//!    against `vir::def`'s `pub const` failure strings (not parsed), and
//!    obligation spans come from downcasting the structured message.
//!
//! Anything not identified stays `unresolved:*` with a bounded shape summary.

use crate::record::{
    EmissionRole, FuelSite, InvariantBlockPoint, Origin, OriginKind, TerminationPoint,
    TypeInvariantSite,
};
use air::ast::{BinaryOp, Constant, Expr, ExprX, MultiOp, UnaryOp};
use vir::def::{FUEL_BOOL, FUEL_BOOL_DEFAULT, HAS_TYPE, PREFIX_ENSURES, PREFIX_REQUIRES};

pub struct Classification {
    pub origin: Origin,
    /// The typed emission role. `None` exactly when the row is unresolved.
    pub role: Option<EmissionRole>,
    /// Ledger rule id (crate::rules) that justified this attribution.
    /// Empty for unresolved rows.
    pub rule: &'static str,
}

/// An attributed classification: origin kind, diagnostic detail, typed role.
fn c(kind: OriginKind, detail: impl Into<String>, role: EmissionRole) -> Classification {
    Classification { origin: Origin { kind, detail: detail.into() }, role: Some(role), rule: "" }
}

/// An unresolved classification: no role; `detail` is the diagnostic shape.
fn unresolved(detail: impl Into<String>) -> Classification {
    Classification {
        origin: Origin { kind: OriginKind::Unresolved, detail: detail.into() },
        role: None,
        rule: "",
    }
}

impl Classification {
    pub fn cite(mut self, rule: &'static str) -> Classification {
        self.rule = rule;
        self
    }
}

pub fn is_unresolved(class: &Classification) -> bool {
    class.origin.kind == OriginKind::Unresolved
}

/// Tier 1: classify a premise formula by the encoding's reserved vocabulary.
pub fn classify_premise(expr: &Expr) -> Classification {
    match &**expr {
        // Shape-only conclusions are heuristic and not allowed to
        // attribute: a bare `false` could be a synthesized path termination
        // *or* a user-written `assume(false)` — the SST intent
        // (PathTermination vs UserAssume) is the typed source, recovered by
        // alignment. Same for `true` and for bare equalities (an invariant
        // clause at loop exit is Eq-shaped too).
        ExprX::Const(Constant::Bool(false)) => unresolved("const_false"),
        ExprX::Const(Constant::Bool(true)) => unresolved("const_true"),
        ExprX::Apply(name, _) => classify_apply(name),
        ExprX::Var(name) => {
            if name.as_str() == vir::def::FUEL_DEFAULTS {
                c(OriginKind::Generated, "fuel", EmissionRole::Fuel { site: FuelSite::Statement })
                    .cite(crate::rules::R_FUEL)
            } else {
                unresolved("bare_var")
            }
        }
        ExprX::ApplyFun(_, f, _) => match &**f {
            ExprX::Var(name) => classify_apply(name),
            _ => unresolved("apply_fun"),
        },
        ExprX::Binary(BinaryOp::Eq, _, _) => unresolved("equality"),
        ExprX::Multi(MultiOp::And, exprs) => {
            let classes: Vec<Classification> = exprs.iter().map(classify_premise).collect();
            match classes.first() {
                Some(first)
                    if !is_unresolved(first)
                        && classes.iter().all(|x| x.origin.detail == first.origin.detail) =>
                {
                    let role = first.role.clone().expect("attributed rows carry a role");
                    c(first.origin.kind, first.origin.detail.clone(), role)
                }
                _ => unresolved("conjunction"),
            }
        }
        ExprX::Bind(bind, body) => {
            // Fuel witness: (exists fuel. fuel_nat%f == succ^k fuel)
            if matches!(&**bind, air::ast::BindX::Quant(air::ast::Quant::Exists, ..)) {
                if let ExprX::Binary(BinaryOp::Eq, lhs, _) = &**body {
                    if let ExprX::Var(name) = &**lhs {
                        if name.starts_with(vir::def::PREFIX_FUEL_NAT) {
                            return c(
                                OriginKind::Generated,
                                "fuel",
                                EmissionRole::Fuel { site: FuelSite::Statement },
                            )
                            .cite(crate::rules::R_FUEL);
                        }
                    }
                }
            }
            unresolved("binder")
        }
        ExprX::Unary(UnaryOp::Not, inner) => {
            let inner_class = classify_premise(inner);
            if is_unresolved(&inner_class) {
                unresolved("negation")
            } else {
                let role = inner_class.role.clone().expect("attributed rows carry a role");
                c(inner_class.origin.kind, format!("not:{}", inner_class.origin.detail), role)
            }
        }
        _ => unresolved("other"),
    }
}

fn classify_apply(name: &str) -> Classification {
    // `tr_bound%<trait>`: a trait-bound fact for a type parameter's
    // dictionary (vir::def::PREFIX_TRAIT_BOUND). Generated by trait
    // elaboration; carries which trait, joins later work.
    if let Some(tr) = name.strip_prefix(vir::def::PREFIX_TRAIT_BOUND) {
        return c(OriginKind::Generated, format!("trait_bound:{}", tr), EmissionRole::TraitBound)
            .cite(crate::rules::R_TRAIT_BOUND);
    }
    use vir::def::{CHECK_DECREASE_HEIGHT, FUEL_DEFAULTS, HAS_RESOLVED, I_INV, SIZED_BOUND, U_INV};
    if let Some(callee) = name.strip_prefix(PREFIX_ENSURES) {
        c(
            OriginKind::Source,
            format!("ensures_of:{}", callee),
            EmissionRole::CallPostcondition { callee: callee.to_string() },
        )
        .cite(crate::rules::R_CALLEE_ENS)
    } else if let Some(callee) = name.strip_prefix(PREFIX_REQUIRES) {
        c(
            OriginKind::Source,
            format!("requires_of:{}", callee),
            EmissionRole::CallPrecondition { callee: Some(callee.to_string()) },
        )
        .cite(crate::rules::R_CALLEE_REQ)
    } else if name == FUEL_BOOL || name == FUEL_BOOL_DEFAULT || name == FUEL_DEFAULTS {
        c(OriginKind::Generated, "fuel", EmissionRole::Fuel { site: FuelSite::Statement })
            .cite(crate::rules::R_FUEL)
    } else if name == HAS_TYPE || name == U_INV || name == I_INV || name == SIZED_BOUND {
        c(
            OriginKind::Generated,
            "type_invariant",
            EmissionRole::TypeInvariant { site: TypeInvariantSite::Statement },
        )
        .cite(crate::rules::R_TYPE_INV)
    } else if name == CHECK_DECREASE_HEIGHT {
        c(OriginKind::Generated, "decreases_check", EmissionRole::DecreaseHeightCheck)
            .cite(crate::rules::R_DECREASE_CHECK)
    } else if name == HAS_RESOLVED {
        c(OriginKind::Generated, "resolution", EmissionRole::Resolution)
            .cite(crate::rules::R_RESOLUTION)
    } else if name.starts_with("str%") || name.starts_with("bytes%") {
        // Reveal-string/byte-string literal facts (STRSLICE_*/BYTESTR_*).
        c(OriginKind::Generated, "string_literal", EmissionRole::StringLiteral)
            .cite(crate::rules::R_STRING_LITERAL)
    } else {
        unresolved("apply")
    }
}

/// Map an obligation's diagnostic note to an origin and role by *exact*
/// match against the failure-string constants the verifier itself defines.

pub fn classify_obligation_note(note: &str) -> Classification {
    let cls = classify_obligation_note_inner(note);
    if cls.rule.is_empty() && !is_unresolved(&cls) {
        cls.cite(crate::rules::R_NOTE_VOCAB)
    } else {
        cls
    }
}

fn classify_obligation_note_inner(note: &str) -> Classification {
    if note == vir::def::PATTERN_MATCH_FAIL_MESSAGE {
        return c(OriginKind::Generated, "pattern_match_check", EmissionRole::PatternMatchCheck)
            .cite(crate::rules::R_PATTERN_MATCH);
    }
    use crate::record::{AssertionPoint, LoopPoint};
    use vir::def::{
        DEC_FAIL_LOOP_CONTINUE, DEC_FAIL_LOOP_END, INV_FAIL_LOOP_END, INV_FAIL_LOOP_FRONT,
        POSTCONDITION_FAILURE, PRECONDITION_FAILURE,
    };
    if note == POSTCONDITION_FAILURE {
        c(OriginKind::Source, "ensures", EmissionRole::FunctionEnsures)
    } else if note == PRECONDITION_FAILURE {
        // The callee is named by the checked formula, attached by the walker.
        c(
            OriginKind::Source,
            "requires_of_callee",
            EmissionRole::CallPrecondition { callee: None },
        )
    } else if note == DEC_FAIL_LOOP_CONTINUE {
        c(
            OriginKind::Generated,
            "decreases",
            EmissionRole::TerminationCheck { at: TerminationPoint::LoopContinue },
        )
    } else if note == DEC_FAIL_LOOP_END {
        c(
            OriginKind::Generated,
            "decreases",
            EmissionRole::TerminationCheck { at: TerminationPoint::LoopEnd },
        )
    } else if note == INV_FAIL_LOOP_FRONT {
        c(
            OriginKind::Source,
            "loop_invariant",
            EmissionRole::LoopInvariant { point: LoopPoint::Establish },
        )
    } else if note == INV_FAIL_LOOP_END {
        c(
            OriginKind::Source,
            "loop_invariant",
            EmissionRole::LoopInvariant { point: LoopPoint::Maintain },
        )
    } else if note == "assertion failed" {
        c(OriginKind::Source, "assertion", EmissionRole::Assertion { point: AssertionPoint::Check })
    } else if note == "loop invariant not satisfied" {
        // Break/continue sites; the label distinguishes which.
        c(
            OriginKind::Source,
            "loop_invariant",
            EmissionRole::LoopInvariant { point: LoopPoint::Transfer },
        )
    } else if note == "possible arithmetic underflow/overflow" {
        c(OriginKind::Generated, "arith_overflow_check", EmissionRole::ArithOverflowCheck)
    } else if note == "could not prove termination" {
        c(
            OriginKind::Generated,
            "decreases",
            EmissionRole::TerminationCheck { at: TerminationPoint::Function },
        )
    } else if note == "Cannot show invariant holds at end of block" {
        c(
            OriginKind::Source,
            "opened_invariant",
            EmissionRole::InvariantBlock { point: InvariantBlockPoint::Close },
        )
    } else {
        unresolved(format!("obligation_note:{}", note))
    }
}

/// Structural equality of two AIR expressions (used for the
/// assert-then-assume rule). Cheap pointer check first.
pub fn exprs_equal(a: &Expr, b: &Expr) -> bool {
    std::sync::Arc::ptr_eq(a, b) || format!("{:?}", a) == format!("{:?}", b)
}

/// Bounded head-shape summary for unresolved rows (gap analysis).
pub fn shape(expr: &Expr) -> String {
    let mut s = shape_depth(expr, 2);
    s.truncate(120);
    s
}

fn shape_depth(expr: &Expr, depth: u32) -> String {
    if depth == 0 {
        return "_".to_string();
    }
    match &**expr {
        ExprX::Const(cnst) => format!("const:{:?}", cnst),
        ExprX::Var(x) => format!("var:{}", x),
        ExprX::Old(..) => "old".to_string(),
        ExprX::Apply(name, args) => {
            let inner: Vec<String> =
                args.iter().take(3).map(|a| shape_depth(a, depth - 1)).collect();
            format!("{}({})", name, inner.join(","))
        }
        ExprX::ApplyFun(_, f, _) => format!("applyfun:{}", shape_depth(f, depth - 1)),
        ExprX::Unary(op, e) => format!("{:?}({})", op, shape_depth(e, depth - 1)),
        ExprX::Binary(op, a, b) => {
            format!("{:?}({},{})", op, shape_depth(a, depth - 1), shape_depth(b, depth - 1))
        }
        ExprX::Multi(op, exprs) => {
            let inner: Vec<String> =
                exprs.iter().take(4).map(|e| shape_depth(e, depth - 1)).collect();
            format!("{:?}({})", op, inner.join(","))
        }
        ExprX::IfElse(..) => "ite".to_string(),
        ExprX::Array(..) => "array".to_string(),
        ExprX::Bind(bind, e) => {
            let kind = match &**bind {
                air::ast::BindX::Let(..) => "let",
                air::ast::BindX::Quant(air::ast::Quant::Forall, ..) => "forall",
                air::ast::BindX::Quant(air::ast::Quant::Exists, ..) => "exists",
                air::ast::BindX::Lambda(..) => "lambda",
                air::ast::BindX::Choose(..) => "choose",
            };
            format!("{}({})", kind, shape_depth(e, depth - 1))
        }
        ExprX::LabeledAxiom(..) => "labeled_axiom".to_string(),
        ExprX::LabeledAssertion(..) => "labeled_assertion".to_string(),
    }
}

/// If the formula is a `req%<callee>` application, return the callee.
pub fn callee_of_requires(expr: &Expr) -> Option<String> {
    match &**expr {
        ExprX::Apply(name, _) => name.strip_prefix(PREFIX_REQUIRES).map(|s| s.to_string()),
        ExprX::ApplyFun(_, f, _) => match &**f {
            ExprX::Var(name) => name.strip_prefix(PREFIX_REQUIRES).map(|s| s.to_string()),
            _ => None,
        },
        _ => None,
    }
}

/// Op-skeleton signature of an AIR formula, for per-signature alignment
/// against SST expressions. Boxing/coercion applications (`%`-prefixed
/// heads with one argument) are transparent.
pub fn air_sig(expr: &Expr) -> String {
    match &**expr {
        ExprX::Const(_) => "const".to_string(),
        ExprX::Var(_) | ExprX::Old(..) => "var".to_string(),
        ExprX::Apply(name, args) => {
            if name.starts_with('%') && args.len() == 1 {
                air_sig(&args[0])
            } else {
                "app".to_string()
            }
        }
        ExprX::ApplyFun(..) => "app".to_string(),
        ExprX::Unary(UnaryOp::Not, e) => format!("not({})", air_sig(e)),
        ExprX::Unary(_, e) => air_sig(e),
        ExprX::Binary(op, a, b) => {
            let tok = match op {
                BinaryOp::Implies => "implies",
                BinaryOp::Eq => "eq",
                BinaryOp::Le => "le",
                BinaryOp::Ge => "ge",
                BinaryOp::Lt => "lt",
                BinaryOp::Gt => "gt",
                _ => "binop",
            };
            format!("{}({},{})", tok, air_sig(a), air_sig(b))
        }
        ExprX::Multi(MultiOp::And, _) => "and".to_string(),
        ExprX::Multi(MultiOp::Or, _) => "or".to_string(),
        ExprX::Multi(..) => "multi".to_string(),
        ExprX::IfElse(..) => "ite".to_string(),
        ExprX::Bind(bind, _) => match &**bind {
            air::ast::BindX::Quant(air::ast::Quant::Forall, ..) => "forall".to_string(),
            air::ast::BindX::Quant(air::ast::Quant::Exists, ..) => "exists".to_string(),
            air::ast::BindX::Let(..) => "let".to_string(),
            air::ast::BindX::Lambda(..) => "lambda".to_string(),
            air::ast::BindX::Choose(..) => "choose".to_string(),
        },
        _ => "other".to_string(),
    }
}
