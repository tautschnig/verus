use crate::ast::{
    ComputeMode, Fun, Ident, Mode, SpannedTyped, Typ, TypX, UnaryOp, VarIdent, VirErr,
};
use crate::ast_to_sst_func::SstMap;
use crate::context::Ctx;
use crate::def::{Spanned, unique_local};
use crate::messages::{ToAny, WarningAllow, error_with_label};
use crate::sst::{BndX, CallFun, Exp, ExpX, FuncCheckSst, FunctionSst, Stm, StmX, UniqueIdent};
use crate::sst_visitor::{NoScoper, Rewrite, Visitor};
use crate::triggers::build_triggers;
use crate::util::vec_map_result;
use crate::visitor::Returner;
use air::messages::Diagnostics;
use std::collections::HashMap;
use std::sync::Arc;

fn elaborate_one_exp<D: Diagnostics + ?Sized>(
    ctx: &Ctx,
    diagnostics: &D,
    fun_ssts: &HashMap<Fun, FunctionSst>,
    is_native: &mut Option<HashMap<VarIdent, bool>>,
    exp: &Exp,
) -> Result<Exp, VirErr> {
    match &exp.x {
        ExpX::Call(CallFun::Fun(fun, resolved_method), typs, args) => {
            let (fun, typs) =
                if let Some((f, ts)) = resolved_method { (f, ts) } else { (fun, typs) };
            if let Some(func) = fun_ssts.get(fun)
                && let Some(spec_axioms) = func.x.axioms.spec_axioms.as_ref()
                && func.x.attrs.inline
                && func.x.kind.inline_okay()
            {
                let typ_params = &func.x.typ_params;
                let pars = &func.x.pars;
                let body = &spec_axioms.body_exp;
                let mut typ_substs: HashMap<Ident, Typ> = HashMap::new();
                let mut substs: HashMap<UniqueIdent, Exp> = HashMap::new();
                assert!(typ_params.len() == typs.len());
                for (name, typ) in typ_params.iter().zip(typs.iter()) {
                    assert!(!typ_substs.contains_key(name));
                    typ_substs.insert(name.clone(), typ.clone());
                }
                assert!(pars.len() == args.len());
                for (par, arg) in pars.iter().zip(args.iter()) {
                    let unique = unique_local(&par.x.name);
                    assert!(!substs.contains_key(&unique));
                    substs.insert(unique, arg.clone());
                }
                let e = crate::sst_util::subst_exp(&typ_substs, &substs, body);
                // keep the original outer span for better trigger messages
                // keep the original type so that poly.rs can perform the proper box/unbox on e
                let e = SpannedTyped::new(&exp.span, &exp.typ, e.x.clone());
                return Ok(e);
            }
            Ok(exp.clone())
        }
        ExpX::Bind(bnd, body) => match &bnd.x {
            BndX::Quant(quant, bs, trigs, assert_by_vars) => {
                assert!(trigs.len() == 0);
                let mut vars: Vec<VarIdent> = Vec::new();
                for b in bs.iter() {
                    match &*b.a {
                        TypX::TypeId => vars.push(crate::def::suffix_typ_param_var(&b.name)),
                        _ => vars.push(b.name.clone()),
                    }
                }
                let trigs = build_triggers(ctx, &exp.span, &vars, &body, false)?;
                if let Some(assert_by_vars) = assert_by_vars {
                    let natives = crate::triggers::native_quant_vars(bs, &trigs);
                    assert!(assert_by_vars.len() == bs.len());
                    for (x, b) in assert_by_vars.iter().zip(bs.iter()) {
                        let native = natives.contains(&b.name);
                        if let Some(is_native) = is_native {
                            if let Some(n) = is_native.insert(x.clone(), native) {
                                assert!(n == native);
                            }
                        }
                    }
                }
                let bnd =
                    Spanned::new(bnd.span.clone(), BndX::Quant(*quant, bs.clone(), trigs, None));
                Ok(SpannedTyped::new(&exp.span, &exp.typ, ExpX::Bind(bnd, body.clone())))
            }
            BndX::Choose(bs, trigs, cond) => {
                assert!(trigs.len() == 0);
                let vars = bs.iter().map(|b| b.name.clone()).collect();
                let trigs = build_triggers(ctx, &exp.span, &vars, &cond, false)?;
                let bnd =
                    Spanned::new(bnd.span.clone(), BndX::Choose(bs.clone(), trigs, cond.clone()));
                Ok(SpannedTyped::new(&exp.span, &exp.typ, ExpX::Bind(bnd, body.clone())))
            }
            BndX::Lambda(bs, trigs) => {
                assert!(trigs.len() == 0);
                let vars = bs.iter().map(|b| b.name.clone()).collect();
                let trigs = build_triggers(ctx, &exp.span, &vars, &body, true)?;
                if trigs.len() > 0 {
                    let msg = "#[trigger] on a spec_fn closure is deprecated - \
                        generally spec_fn closures don't need triggers because spec_fn \
                        closures are triggered automatically by calls to to closures. \
                        If you think you need additional triggers, see the discussion in \
                        https://github.com/verus-lang/verus/pull/331 \
                        for alternatives.";
                    ctx.warning_maybe_if_in_local_crate(
                        &exp.span,
                        &WarningAllow::TriggerOnSpecFn,
                        || msg,
                        |msg| diagnostics.report(&msg.to_any()),
                    );
                }
                let bnd = Spanned::new(bnd.span.clone(), BndX::Lambda(bs.clone(), trigs));
                Ok(SpannedTyped::new(&exp.span, &exp.typ, ExpX::Bind(bnd, body.clone())))
            }
            _ => Ok(exp.clone()),
        },
        // remove MustBeElaborated marker to vouch that elaborate_one_exp was called
        ExpX::Unary(UnaryOp::MustBeElaborated, e1) => Ok(e1.clone()),
        _ => Ok(exp.clone()),
    }
}

fn elaborate_one_stm<D: Diagnostics + ?Sized>(
    ctx: &Ctx,
    diagnostics: &D,
    fun_ssts: &SstMap,
    stm: &Stm,
) -> Result<Stm, VirErr> {
    match &stm.x {
        StmX::AssertCompute(id, exp, compute) => {
            let (interp_exp, trace) = crate::interpreter::eval_expr_with_trace(
                ctx,
                exp,
                Some(diagnostics),
                fun_ssts.clone(),
                ctx.global.rlimit,
                ctx.global.arch,
                *compute,
                &mut ctx.global.interpreter_log.lock().unwrap(),
            )?;
            let err = error_with_label(
                &exp.span.clone(),
                "assertion failed",
                format!("simplified to {}", interp_exp.x.to_user_string(&ctx.global)),
            );
            let main = match compute {
                ComputeMode::Z3 => stm.new_x(StmX::Assert(id.clone(), Some(err), interp_exp.clone())),
                ComputeMode::ComputeOnly => stm.new_x(StmX::Block(Arc::new(vec![]))),
            };
            if !ctx.global.check_compute {
                return Ok(main);
            }
            // Closed sequence operands of `=~=` in the assertion: their values as push chains,
            // computed by the interpreter, so that the final check can relate them element by
            // element (`subrange`, `add`, `seq![..]`). Each `operand == value` is itself checked.
            let eval_chain = |o: &Exp| -> Option<Exp> {
                let (v, _) = crate::interpreter::eval_expr_with_trace(
                    ctx,
                    o,
                    None::<&air::messages::Reporter>,
                    fun_ssts.clone(),
                    ctx.global.rlimit,
                    ctx.global.arch,
                    ComputeMode::Z3,
                    &mut ctx.global.interpreter_log.lock().unwrap(),
                )
                .ok()?;
                if is_push_chain(&v) { Some(v) } else { None }
            };
            let mut seq_values: Vec<(Exp, Exp)> = vec![];
            for o in closed_seq_operands(exp) {
                // a closure inside the operand: its elements need --check-compute-all
                if !ctx.global.check_compute_all && contains_lambda(&o) {
                    continue;
                }
                if let Ok((v, _)) = crate::interpreter::eval_expr_with_trace(
                    ctx,
                    &o,
                    None::<&air::messages::Reporter>,
                    fun_ssts.clone(),
                    ctx.global.rlimit,
                    ctx.global.arch,
                    ComputeMode::Z3,
                    &mut ctx.global.interpreter_log.lock().unwrap(),
                ) {
                    if is_push_chain(&v) {
                        seq_values.push((o, v));
                    }
                }
            }
            let (mut stms, skipped) = compute_step_checks(
                ctx,
                fun_ssts,
                stm,
                exp,
                &interp_exp,
                &trace,
                &seq_values,
                &eval_chain,
            );
            if trace.unexpressible + skipped > 0 {
                diagnostics.report(
                    &crate::messages::warning(
                        &exp.span,
                        format!(
                            "--check-compute: {} of {} by (compute) step(s) not checked (bitwise \
                             steps that are not closed after unfolding, equations between \
                             functions, quantifiers or closures without --check-compute-all, \
                             bound variables without a trigger, or functions outside this \
                             query's context)",
                            trace.unexpressible + skipped,
                            trace.unexpressible + trace.steps.len() + 1
                        ),
                    )
                    .to_any(),
                );
            }
            stms.push(main);
            Ok(stm.new_x(StmX::Block(Arc::new(stms))))
        }
        StmX::AssertBitVector { requires, ensures } => {
            if ctx.global.no_bv_simplify {
                return Ok(stm.clone());
            }
            let reqs = vec_map_result(requires, |e| {
                crate::interpreter::eval_expr(
                    ctx,
                    e,
                    None::<&air::messages::Reporter>, // Don't print (internal) diagnostics
                    fun_ssts.clone(),
                    ctx.global.rlimit,
                    ctx.global.arch,
                    crate::ast::ComputeMode::Z3,
                    &mut ctx.global.interpreter_log.lock().unwrap(),
                )
            })?;
            let ens = vec_map_result(ensures, |e| {
                crate::interpreter::eval_expr(
                    ctx,
                    e,
                    None::<&air::messages::Reporter>, // Don't print (internal) diagnostics
                    fun_ssts.clone(),
                    ctx.global.rlimit,
                    ctx.global.arch,
                    crate::ast::ComputeMode::Z3,
                    &mut ctx.global.interpreter_log.lock().unwrap(),
                )
            })?;
            Ok(stm.new_x(StmX::AssertBitVector { requires: reqs.into(), ensures: ens.into() }))
        }
        _ => Ok(stm.clone()),
    }
}

struct ElaborateVisitor1<'a, 'b, 'c, D: Diagnostics> {
    ctx: &'a Ctx,
    diagnostics: &'b D,
    fun_ssts: &'c HashMap<Fun, FunctionSst>,
    is_native: Option<HashMap<VarIdent, bool>>,
}

impl<'a, 'b, 'c, D: Diagnostics> Visitor<Rewrite, VirErr, NoScoper>
    for ElaborateVisitor1<'a, 'b, 'c, D>
{
    fn visit_exp(&mut self, exp: &Exp) -> Result<Exp, VirErr> {
        let exp = self.visit_exp_rec(exp)?;
        elaborate_one_exp(self.ctx, self.diagnostics, &self.fun_ssts, &mut self.is_native, &exp)
    }

    fn visit_stm(&mut self, stm: &Stm) -> Result<Stm, VirErr> {
        self.visit_stm_rec(stm)
    }

    fn visit_func_check(&mut self, def: &FuncCheckSst) -> Result<FuncCheckSst, VirErr> {
        self.is_native = Some(HashMap::new());
        let reqs = self.visit_exps(&def.reqs)?;
        let post_condition = self.visit_postcondition(&def.post_condition)?;
        let body = self.visit_stm(&def.body)?;
        let local_decls =
            Rewrite::map_vec(&def.local_decls, &mut |decl| self.visit_local_decl(decl))?;
        let local_decls_decreases_init = self.visit_stms(&def.local_decls_decreases_init)?;
        let unwind = self.visit_unwind(&def.unwind)?;
        let is_native = self.is_native.take().expect("is_native");

        let mut def = FuncCheckSst {
            reqs: Arc::new(reqs),
            post_condition: Arc::new(post_condition),
            unwind,
            body,
            local_decls: Arc::new(local_decls),
            local_decls_decreases_init: Arc::new(local_decls_decreases_init),
            statics: def.statics.clone(),
        };

        rewrite_locals(&is_native, &mut def);

        Ok(def)
    }
}

fn rewrite_locals(is_native: &HashMap<VarIdent, bool>, function: &mut crate::sst::FuncCheckSst) {
    for local in Arc::make_mut(&mut function.local_decls) {
        use crate::sst::LocalDeclKind;
        if matches!(local.kind, LocalDeclKind::AssertByVar { .. }) {
            let native = is_native[&local.ident];
            Arc::make_mut(local).kind = LocalDeclKind::AssertByVar { native };
        }
    }
}

struct ElaborateVisitor2<'a, 'b, D: Diagnostics> {
    ctx: &'a Ctx,
    diagnostics: &'b D,
    fun_ssts: SstMap,
}

impl<'a, 'b, D: Diagnostics> Visitor<Rewrite, VirErr, NoScoper> for ElaborateVisitor2<'a, 'b, D> {
    fn visit_stm(&mut self, stm: &Stm) -> Result<Stm, VirErr> {
        let stm = self.visit_stm_rec(stm)?;
        elaborate_one_stm(self.ctx, self.diagnostics, &self.fun_ssts, &stm)
    }
}

// Triggers and inlining
pub(crate) fn elaborate_function1<'a, 'b, 'c, D: Diagnostics>(
    ctx: &'a Ctx,
    diagnostics: &'b D,
    fun_ssts: &'c HashMap<Fun, FunctionSst>,
    function: &mut FunctionSst,
) -> Result<(), VirErr> {
    let mut visitor = ElaborateVisitor1 { ctx, diagnostics, fun_ssts, is_native: None };
    *function = visitor.visit_function(function)?;

    if function.x.axioms.proof_exec_axioms.is_some() {
        let typ_params = function.x.typ_params.clone();
        let span = function.span.clone();
        let axioms = Arc::make_mut(&mut Arc::make_mut(function).x.axioms);
        let (params, exp, triggers) = axioms.proof_exec_axioms.as_ref().unwrap();
        assert!(triggers.len() == 0);
        let mut vars: Vec<VarIdent> = Vec::new();
        for name in typ_params.iter() {
            vars.push(crate::def::suffix_typ_param_id(&name));
        }
        for param in params.iter() {
            vars.push(param.x.name.clone());
        }
        let triggers = build_triggers(ctx, &span, &vars, exp, false)?;
        axioms.proof_exec_axioms = Some((params.clone(), exp.clone(), triggers));
    }

    Ok(())
}

// Compute and rewrite-recursive-calls
pub(crate) fn elaborate_function_rewrite_recursive<'a, 'b, D: Diagnostics>(
    ctx: &'a Ctx,
    diagnostics: &'b D,
    fun_ssts: SstMap,
    function: &mut FunctionSst,
) -> Result<(), VirErr> {
    let mut visitor = ElaborateVisitor2 { ctx, diagnostics, fun_ssts };
    *function = visitor.visit_function(function)?;

    if function.x.has.is_recursive && function.x.mode == Mode::Spec {
        let function_ref = &function.clone();
        let axioms = Arc::make_mut(&mut Arc::make_mut(function).x.axioms);
        if let Some(spec_body) = &mut axioms.spec_axioms {
            // Rewrite recursive calls to use fuel
            let (body_exp, _) = crate::recursion::rewrite_spec_recursive_fun_with_fueled_rec_call(
                ctx,
                function_ref,
                &spec_body.body_exp,
            )?;
            spec_body.body_exp = body_exp;
        }
    }

    Ok(())
}

// Expand expressions using the interpreter
fn expand<'a>(ctx: &'a Ctx, fun_ssts: &SstMap, exps: Vec<Exp>) -> Result<Vec<Exp>, VirErr> {
    vec_map_result(&exps, |e| {
        crate::interpreter::eval_expr(
            ctx,
            e,
            None::<&air::messages::Reporter>,
            fun_ssts.clone(),
            ctx.global.rlimit,
            ctx.global.arch,
            crate::ast::ComputeMode::Z3,
            &mut ctx.global.interpreter_log.lock().unwrap(),
        )
    })
}

// Use the interpreter to inline spec functions (and otherwise apply its usual simplifications)
// to bit-vector assertions/proofs
pub(crate) fn elaborate_function_bv<'a>(
    ctx: &'a Ctx,
    fun_ssts: SstMap,
    function: &mut FunctionSst,
) -> Result<(), VirErr> {
    if function.x.attrs.bit_vector {
        if let Some(exec_proof_check_arc) = &mut Arc::make_mut(function).x.exec_proof_check {
            let exec_proof_check_mut = Arc::make_mut(exec_proof_check_arc);
            // Expand reqs and ens_exps using the interpreter
            let reqs = expand(ctx, &fun_ssts, exec_proof_check_mut.reqs.to_vec())?;
            let ens_exps =
                expand(ctx, &fun_ssts, exec_proof_check_mut.post_condition.ens_exps.to_vec())?;

            // Update the exec_proof_check fields directly
            exec_proof_check_mut.reqs = Arc::new(reqs);
            let post = Arc::make_mut(&mut exec_proof_check_mut.post_condition);
            post.ens_exps = Arc::new(ens_exps);
        }
    }
    Ok(())
}

/// Hints for each closed `Seq` operand `x` of an extensional equality in `e`: `x.len()`
/// (and of each prefix of a push chain), and for a push chain `x[i]` with the pushed element
fn seq_len_hints(e: &Exp) -> Vec<(Exp, Option<Exp>)> {
    let len_fun = Arc::new(crate::ast::FunX {
        path: Arc::new(crate::ast::PathX {
            krate: crate::ast::CrateId::Vstd,
            segments: Arc::new(
                ["seq", "Seq", "len"].iter().map(|s| Arc::new(s.to_string())).collect(),
            ),
        }),
    });
    let index_fun = Arc::new(crate::ast::FunX {
        path: Arc::new(crate::ast::PathX {
            krate: crate::ast::CrateId::Vstd,
            segments: Arc::new(
                ["seq", "Seq", "index"].iter().map(|s| Arc::new(s.to_string())).collect(),
            ),
        }),
    });
    let mut out = vec![];
    let mut map = crate::sst_visitor::VisitorScopeMap::new();
    let _ = crate::sst_visitor::exp_visitor_check(e, &mut map, &mut |x: &Exp, map| {
        if let ExpX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(_, t), a, b) = &x.x {
            if let crate::ast::TypX::Datatype(crate::ast::Dt::Path(p), targs, _) =
                &*crate::ast_util::undecorate_typ(t)
            {
                let is_seq = p.krate == crate::ast::CrateId::Vstd
                    && p.segments.iter().map(|s| s.as_str()).collect::<Vec<_>>() == ["seq", "Seq"];
                // only closed operands: a bound variable would be out of scope in the hint
                for o in [a, b] {
                    let closed = crate::sst_util::free_vars_exp(o).keys().all(|v| !map.contains_key(v));
                    if is_seq && closed && targs.len() == 1 {
                        // `x[i]` for each position of a push chain (`seq![..]` cleaned up by
                        // the interpreter), so a differing element can be found
                        let mut n = 0usize;
                        let mut elems: Vec<Exp> = vec![];
                        let mut cur = o.clone();
                        let mk_len = |x: &Exp| {
                            SpannedTyped::new(
                                &x.span,
                                &Arc::new(crate::ast::TypX::Int(crate::ast::IntRange::Nat)),
                                ExpX::Call(
                                    CallFun::Fun(len_fun.clone(), None),
                                    targs.clone(),
                                    Arc::new(vec![x.clone()]),
                                ),
                            )
                        };
                        let known_len = loop {
                            if !Arc::ptr_eq(&cur, o) {
                                out.push((mk_len(&cur), None));
                            }
                            match &cur.x {
                                ExpX::Call(CallFun::Fun(f, _), _, args)
                                    if f.path.segments.last().map(|s| s.as_str()) == Some("push")
                                        && args.len() == 2 =>
                                {
                                    n += 1;
                                    elems.push(args[1].clone());
                                    cur = args[0].clone();
                                }
                                ExpX::Call(CallFun::Fun(f, _), _, args)
                                    if f.path.segments.last().map(|s| s.as_str()) == Some("empty")
                                        && args.is_empty() =>
                                {
                                    break Some(n);
                                }
                                _ => break None,
                            }
                        };
                        if let Some(n) = known_len.filter(|n| *n <= 16) {
                            elems.reverse();
                            for i in 0..n {
                                let idx = SpannedTyped::new(
                                    &o.span,
                                    &Arc::new(crate::ast::TypX::Int(crate::ast::IntRange::Int)),
                                    ExpX::Const(crate::ast::Constant::Int(num_bigint::BigInt::from(i))),
                                );
                                out.push((
                                    SpannedTyped::new(
                                        &o.span,
                                        &targs[0],
                                        ExpX::Call(
                                            CallFun::Fun(index_fun.clone(), None),
                                            targs.clone(),
                                            Arc::new(vec![o.clone(), idx]),
                                        ),
                                    ),
                                    Some(elems[i].clone()),
                                ));
                            }
                        }
                        out.push((mk_len(o), None));
                    }
                }
            }
        }
        Ok::<(), ()>(())
    });
    out
}

/// More distinct steps than this are not checked (reported as unchecked)
const MAX_COMPUTE_STEP_CHECKS: usize = 2000;

/// `--check-compute`: one isolated SMT check per call the interpreter evaluated, and one for
/// the final result. Each step `f(args) == r` is checked with `f`'s definition (fuel 1) and the
/// calls made while evaluating the body assumed (each is a step, checked in turn); the final
/// check is `exp == result` with the top-level calls assumed. By induction on the steps, the
/// interpreter's result then follows from Verus's SMT encoding of the same definitions.
fn compute_step_checks(
    ctx: &Ctx,
    fun_ssts: &SstMap,
    stm: &Stm,
    exp: &Exp,
    result: &Exp,
    trace: &crate::interpreter::ComputeTrace,
    seq_values: &[(Exp, Exp)],
    eval_chain: &dyn Fn(&Exp) -> Option<Exp>,
) -> (Vec<Stm>, usize) {
    // `==` for values; extensional equality for vstd collections, whose interpreter results
    // (push chains) are equal to the call only extensionally
    let is_collection = |t: &crate::ast::Typ| match &*crate::ast_util::undecorate_typ(t) {
        crate::ast::TypX::Datatype(crate::ast::Dt::Path(p), _, _) => {
            p.krate == crate::ast::CrateId::Vstd
                && matches!(
                    p.segments.iter().map(|s| s.as_str()).collect::<Vec<_>>()[..],
                    ["seq", "Seq"] | ["set", "Set"] | ["map", "Map"]
                )
        }
        _ => false,
    };
    let eq = |a: &Exp, b: &Exp| {
        let x = if is_collection(&a.typ) {
            ExpX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(false, a.typ.clone()), a.clone(), b.clone())
        } else {
            ExpX::Binary(crate::sst::BinaryOp::Eq, a.clone(), b.clone())
        };
        SpannedTyped::new(&a.span, &Arc::new(crate::ast::TypX::Bool), x)
    };
    // A step is checkable if every function it names is in this query's (pruned) context,
    // and it uses no operation that the default integer encoding leaves uninterpreted
    // (bitwise operators: they would need a bit-vector query). Steps that equate functions
    // are skipped below.
    let in_scope = crate::sst_util::free_vars_exp(exp);
    let known = |e: &Exp| {
        let mut map = crate::sst_visitor::VisitorScopeMap::new();
        crate::sst_visitor::exp_visitor_check(e, &mut map, &mut |e: &Exp, map| match &e.x {
            ExpX::Call(CallFun::Fun(f, r), _, _)
                if !ctx.func_map.contains_key(f)
                    || r.as_ref().map_or(false, |(g, _)| !ctx.func_map.contains_key(g)) =>
            {
                Err(())
            }
            ExpX::Binary(crate::sst::BinaryOp::Bitwise(..), _, _)
            | ExpX::Unary(crate::ast::UnaryOp::BitNot(_), _) => Err(()),
            _ => Ok(()),
        })
        .is_ok()
    };
    // ... and the same for the bodies of the functions a step unfolds
    let body_ok = |f: &crate::ast::Fun| {
        fun_ssts.get(f).map_or(true, |fs| {
            fs.x.axioms.spec_axioms.as_ref().map_or(true, |a| {
                let mut map = crate::sst_visitor::VisitorScopeMap::new();
                crate::sst_visitor::exp_visitor_check(&a.body_exp, &mut map, &mut |e: &Exp, _| {
                    match &e.x {
                        ExpX::Binary(crate::sst::BinaryOp::Bitwise(..), _, _)
                        | ExpX::Unary(crate::ast::UnaryOp::BitNot(_), _) => Err(()),
                        _ => Ok(()),
                    }
                })
                .is_ok()
            })
        })
    };
    // A step evaluated under a binder of the assertion (or of a callee) mentions the bound
    // variable; it holds for every value of it, so it is checked, and used as a fact, as
    // `forall|v| call == result`, triggered on the call.
    let forall_over = |call: &Exp, body: Exp| -> Option<Exp> {
        let vars: Vec<(UniqueIdent, crate::ast::Typ)> = crate::sst_util::free_vars_exp(&body)
            .into_iter()
            .filter(|(x, _)| !in_scope.contains_key(x))
            .collect();
        if vars.is_empty() {
            return Some(body);
        }
        let in_call = crate::sst_util::free_vars_exp(call);
        if !vars.iter().all(|(x, _)| in_call.contains_key(x)) {
            return None; // no trigger covers all of them
        }
        let binders: Vec<crate::ast::VarBinder<crate::ast::Typ>> = vars
            .into_iter()
            .map(|(name, a)| Arc::new(crate::ast::VarBinderX { name, a }))
            .collect();
        let bnd = Spanned::new(
            body.span.clone(),
            BndX::Quant(
                crate::ast::Quant { quant: air::ast::Quant::Forall },
                Arc::new(binders),
                Arc::new(vec![Arc::new(vec![call.clone()])]),
                None,
            ),
        );
        let span = body.span.clone();
        Some(SpannedTyped::new(&span, &Arc::new(crate::ast::TypX::Bool), ExpX::Bind(bnd, body)))
    };
    let mut out = vec![];
    let mut skipped = 0usize;
    let mut bv_checked = 0usize;
    let pending_lemmas: std::cell::RefCell<Vec<Exp>> = std::cell::RefCell::new(vec![]);
    // A step with bitwise operators is checked in a bit-vector query (as `by (bit_vector)`):
    // the function's body with the arguments substituted, `body[args] == result`, if that is a
    // closed, call-free equation over fixed-width integers. (A bit-vector query has no function
    // axioms, so the unfolding is done here, by substitution, and the children must already be
    // evaluated away: no calls left.)
    let call_free = |e: &Exp| {
        let mut map = crate::sst_visitor::VisitorScopeMap::new();
        crate::sst_visitor::exp_visitor_check(e, &mut map, &mut |e: &Exp, _| match &e.x {
            ExpX::Call(..) | ExpX::Bind(..) => Err(()),
            _ => Ok(()),
        })
        .is_ok()
    };
    let bv_goal = |funs: &[crate::ast::Fun], g: (&Exp, &Exp)| -> Option<Exp> {
        let (call, res) = g;
        let unfolded = match &call.x {
            ExpX::Call(CallFun::Fun(_, _), typs, args) if funs.len() >= 1 => {
                let f = funs.last().unwrap();
                let fs = fun_ssts.get(f)?;
                let body = &fs.x.axioms.spec_axioms.as_ref()?.body_exp;
                let mut vs: HashMap<UniqueIdent, Exp> = HashMap::new();
                for (p, a) in fs.x.pars.iter().zip(args.iter()) {
                    vs.insert(p.x.name.clone(), a.clone());
                }
                let mut ts: HashMap<crate::ast::Ident, crate::ast::Typ> = HashMap::new();
                for (p, t) in fs.x.typ_params.iter().zip(typs.iter()) {
                    ts.insert(p.clone(), t.clone());
                }
                crate::sst_util::subst_exp(&ts, &vs, body)
            }
            _ if funs.is_empty() => call.clone(),
            _ => return None,
        };
        let e = eq(&unfolded, res);
        if crate::sst_util::free_vars_exp(&e).is_empty() && call_free(&e) {
            Some(e)
        } else {
            None
        }
    };
    let mut add = |funs: &[crate::ast::Fun], facts: &[(Exp, Exp)], g: (&Exp, &Exp), what: String| {
        let bitwise = !known(g.0) || !known(g.1) || !funs.iter().all(|f| body_ok(f));
        if bitwise {
            if let Some(e) = bv_goal(funs, g) {
                // the step is checked in a bit-vector query; on failure Verus reports the
                // assertion's span
                out.push(stm.new_x(StmX::AssertBitVector {
                    requires: Arc::new(vec![]),
                    ensures: Arc::new(vec![e]),
                }));
                bv_checked += 1;
                return;
            }
        }
        if bitwise || facts.iter().any(|(c, r)| !known(c) || !known(r)) {
            skipped += 1;
            return;
        }
        // equations between functions (closures) are not decidable by the solver
        let fn_typed = |e: &Exp| {
            matches!(&*crate::ast_util::undecorate_typ(&e.typ), crate::ast::TypX::SpecFn(..))
        };
        if fn_typed(g.0) || facts.iter().any(|(c, _)| fn_typed(c)) {
            skipped += 1;
            return;
        }
        // quantifiers, `choose` and closures in a step: the solver often cannot relate two
        // quantified formulas by E-matching, or two copies of a closure, so these are checked
        // only with --check-compute-all
        let has_binder = |e: &Exp| {
            let mut map = crate::sst_visitor::VisitorScopeMap::new();
            crate::sst_visitor::exp_visitor_check(e, &mut map, &mut |e: &Exp, _| match &e.x {
                ExpX::Bind(b, _)
                    if matches!(b.x, BndX::Quant(..) | BndX::Choose(..) | BndX::Lambda(..)) =>
                {
                    Err(())
                }
                _ => Ok(()),
            })
            .is_err()
        };
        if !ctx.global.check_compute_all
            && (has_binder(g.0) || has_binder(g.1) || facts.iter().any(|(c, r)| has_binder(c) || has_binder(r)))
        {
            skipped += 1;
            return;
        }
        let Some(goal) = forall_over(g.0, eq(g.0, g.1)) else {
            skipped += 1;
            return;
        };
        let Some(facts) =
            facts.iter().map(|(c, r)| forall_over(c, eq(c, r))).collect::<Option<Vec<Exp>>>()
        else {
            skipped += 1;
            return;
        };
        let mut b: Vec<Stm> = vec![];
        for f in funs {
            // fuel exists for spec functions with a body in this context (`context.rs`);
            // a body the interpreter used but the context lacks makes the check fail, which is
            // the correct outcome
            let has_fuel = ctx.func_map.get(f).map_or(false, |g| {
                g.x.mode == crate::ast::Mode::Spec && g.x.body.is_some()
            });
            if has_fuel {
                b.push(stm.new_x(StmX::Fuel(f.clone(), 1)));
            }
        }
        for f in facts {
            b.push(stm.new_x(StmX::Assume(f)));
        }
        // Trigger hints: `x.len() >= 0` for each `Seq` operand of an
        // extensional equality (`!(seq![1] =~= seq![])` needs the `len` terms for
        // `axiom_seq_ext_equal` to give a contradiction)
        for (h, elem) in seq_len_hints(&goal) {
            if let Some(v) = elem {
                // an element: `x[i] == e_i` is asserted (checked, then a fact): the solver
                // proves it from the push axioms in its own query and needs it as a lemma
                let t = SpannedTyped::new(
                    &h.span,
                    &Arc::new(crate::ast::TypX::Bool),
                    ExpX::Binary(crate::sst::BinaryOp::Eq, h.clone(), v),
                );
                let m = error_with_label(
                    &exp.span,
                    "by (compute) step not confirmed by the SMT encoding (--check-compute)",
                    format!("hint {}", t.x.to_user_string(&ctx.global)),
                );
                b.push(stm.new_x(StmX::Assert(None, Some(m), t)));
                continue;
            }
            // `len` returns a `nat`, so `len(x) >= 0` is a fact; a trivial `x == x` would be
            // simplified away before reaching the solver
            let zero = SpannedTyped::new(
                &h.span,
                &h.typ,
                ExpX::Const(crate::ast::Constant::Int(num_bigint::BigInt::from(0))),
            );
            let ge = SpannedTyped::new(
                &h.span,
                &Arc::new(crate::ast::TypX::Bool),
                ExpX::Binary(
                    crate::sst::BinaryOp::Inequality(crate::ast::InequalityOp::Ge),
                    h.clone(),
                    zero,
                ),
            );
            b.push(stm.new_x(StmX::Assume(ge)));
        }
        for l in pending_lemmas.borrow_mut().drain(..) {
            for (h, elem) in seq_len_hints(&l) {
                if let Some(v) = elem {
                    let t = SpannedTyped::new(
                        &h.span,
                        &Arc::new(crate::ast::TypX::Bool),
                        ExpX::Binary(crate::sst::BinaryOp::Eq, h.clone(), v),
                    );
                    let m = error_with_label(
                        &exp.span,
                        "by (compute) step not confirmed by the SMT encoding (--check-compute)",
                        format!("hint {}", t.x.to_user_string(&ctx.global)),
                    );
                    b.push(stm.new_x(StmX::Assert(None, Some(m), t)));
                }
            }
            let m = error_with_label(
                &exp.span,
                "by (compute) step not confirmed by the SMT encoding (--check-compute)",
                format!("sequence value {}", l.x.to_user_string(&ctx.global)),
            );
            b.push(stm.new_x(StmX::Assert(None, Some(m), l)));
        }
        let msg = error_with_label(
            &exp.span,
            "by (compute) step not confirmed by the SMT encoding (--check-compute)",
            what,
        );
        b.push(stm.new_x(StmX::Assert(None, Some(msg), goal)));
        out.push(stm.new_x(StmX::DeadEnd(stm.new_x(StmX::Block(Arc::new(b))))));
    };
    // identical steps (same call, same result, up to spans) need one check: a step's
    // children are themselves steps, so either copy's children suffice
    let key = |e: &Exp| {
        let e = crate::sst_visitor::map_exp_visitor(e, &mut |e: &Exp| {
            SpannedTyped::new(&ctx.global.no_span, &e.typ, e.x.clone())
        });
        format!("{:?}", e.x)
    };
    // A step's result that still mentions one of the callee's own parameters (not in scope at
    // the assertion) is an interpreter bug (upstream #3089: a `choose` kept the formal), not
    // something to leave unchecked.
    let mut leaks: Vec<(String, String)> = vec![];
    for st in trace.steps.iter() {
        for f in st.funs.iter() {
            let Some(fs) = fun_ssts.get(f) else { continue };
            for (x, _) in crate::sst_util::free_vars_exp(&st.result).iter() {
                if !in_scope.contains_key(x) && fs.x.pars.iter().any(|p| &p.x.name == x) {
                    leaks.push((
                        format!("{}", x.0),
                        format!(
                            "{} == {}",
                            st.call.x.to_user_string(&ctx.global),
                            st.result.x.to_user_string(&ctx.global)
                        ),
                    ));
                }
            }
        }
    }
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut capped = 0usize;
    for st in trace.steps.iter() {
        if !seen.insert(format!("{}\u{0}{}", key(&st.call), key(&st.result))) {
            continue;
        }
        if seen.len() > MAX_COMPUTE_STEP_CHECKS {
            capped += 1;
            continue;
        }
        // Seq-valued sub-terms of the unfolded body over the (evaluated) arguments, such as
        // `s.subrange(1, s.len())` for `s` a push chain: their values as push chains, asserted
        // (checked) before the step, so that the step's children, recorded with evaluated
        // arguments, match the body's terms
        let mut lemmas = vec![];
        if let (ExpX::Call(_, typs, args), Some(f)) = (&st.call.x, st.funs.last()) {
            if let Some(body) = fun_ssts
                .get(f)
                .and_then(|fs| fs.x.axioms.spec_axioms.as_ref().map(|a| (fs, a.body_exp.clone())))
            {
                let (fs, body) = body;
                let mut vs: HashMap<UniqueIdent, Exp> = HashMap::new();
                for (p, a) in fs.x.pars.iter().zip(args.iter()) {
                    vs.insert(p.x.name.clone(), a.clone());
                }
                let mut ts: HashMap<crate::ast::Ident, crate::ast::Typ> = HashMap::new();
                for (p, t) in fs.x.typ_params.iter().zip(typs.iter()) {
                    ts.insert(p.clone(), t.clone());
                }
                // the push-chain arguments' elements (`s.index(0)` in the body)
                for a in args.iter() {
                    if is_push_chain(a) {
                        lemmas.push(eq(a, a));
                    }
                }
                let ub = crate::sst_util::subst_exp(&ts, &vs, &body);
                for t in seq_subterms(&ub) {
                    if contains_lambda(&t) && !ctx.global.check_compute_all {
                        continue;
                    }
                    if let Some(v) = eval_chain(&t) {
                        if format!("{:?}", v.x) != format!("{:?}", t.x) {
                            lemmas.push(eq(&t, &v));
                        }
                    }
                }
            }
        }
        *pending_lemmas.borrow_mut() = lemmas;
        add(
            &st.funs,
            &st.children,
            (&st.call, &st.result),
            format!(
                "{} == {}",
                st.call.x.to_user_string(&ctx.global),
                st.result.x.to_user_string(&ctx.global)
            ),
        );
    }
    // the final check: the sequence operands' values are asserted first (checked lemmas,
    // `operand =~= chain`), then the goal is asserted with the operands rewritten to their chains
    let mut lemmas: Vec<Exp> = vec![];
    let mut goal_exp = exp.clone();
    for (o, v) in seq_values.iter() {
        lemmas.push(eq(o, v));
        let (o2, v2) = (o.clone(), v.clone());
        goal_exp = crate::sst_visitor::map_exp_visitor(&goal_exp, &mut |x: &Exp| {
            if format!("{:?}", x.x) == format!("{:?}", o2.x) { v2.clone() } else { x.clone() }
        });
    }
    *pending_lemmas.borrow_mut() = lemmas;
    add(
        &[],
        &trace.top,
        (&goal_exp, result),
        format!(
            "{} == {}",
            exp.x.to_user_string(&ctx.global),
            result.x.to_user_string(&ctx.global)
        ),
    );
    // The final result may only mention variables in scope at the assertion: a variable of a
    // callee in the result (upstream #3089: a `choose` kept the formal) is an interpreter bug,
    // whatever the solver would make of it.
    let leaked: Vec<String> = crate::sst_util::free_vars_exp(result)
        .keys()
        .filter(|x| !in_scope.contains_key(*x))
        .map(|x| format!("{}", x.0))
        .collect();
    if !leaked.is_empty() {
        leaks.push((
            leaked.join(", "),
            format!("result {}", result.x.to_user_string(&ctx.global)),
        ));
    }
    for (vars, what) in leaks {
        let msg = error_with_label(
            &exp.span,
            "by (compute) step mentions variables not in scope (--check-compute)",
            format!("{}: {}", vars, what),
        );
        let f = SpannedTyped::new(
            &exp.span,
            &Arc::new(crate::ast::TypX::Bool),
            ExpX::Const(crate::ast::Constant::Bool(false)),
        );
        out.push(stm.new_x(StmX::DeadEnd(stm.new_x(StmX::Assert(None, Some(msg), f)))));
    }
    (out, skipped + capped)
}

/// The closed `Seq` operands of `=~=` in `e` (no variables bound in `e` or free)
fn closed_seq_operands(e: &Exp) -> Vec<Exp> {
    let mut out = vec![];
    let mut map = crate::sst_visitor::VisitorScopeMap::new();
    let _ = crate::sst_visitor::exp_visitor_check(e, &mut map, &mut |x: &Exp, _map| {
        if let ExpX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(_, t), a, b) = &x.x {
            if let crate::ast::TypX::Datatype(crate::ast::Dt::Path(p), _, _) =
                &*crate::ast_util::undecorate_typ(t)
            {
                if p.krate == crate::ast::CrateId::Vstd
                    && p.segments.iter().map(|s| s.as_str()).collect::<Vec<_>>() == ["seq", "Seq"]
                {
                    for o in [a, b] {
                        if crate::sst_util::free_vars_exp(o).is_empty() && !is_value_chain(o) {
                            out.push(o.clone());
                        }
                    }
                }
            }
        }
        Ok::<(), ()>(())
    });
    out
}

/// `Seq::empty().push(..)..push(..)`
fn is_push_chain(e: &Exp) -> bool {
    let mut cur = e.clone();
    loop {
        match &cur.x {
            ExpX::Call(CallFun::Fun(f, _), _, args)
                if f.path.segments.last().map(|s| s.as_str()) == Some("push") && args.len() == 2 =>
            {
                cur = args[0].clone();
            }
            ExpX::Call(CallFun::Fun(f, _), _, args)
                if f.path.segments.last().map(|s| s.as_str()) == Some("empty") && args.is_empty() =>
            {
                return true;
            }
            _ => return false,
        }
    }
}

/// a push chain whose elements are constants
fn is_value_chain(e: &Exp) -> bool {
    let mut cur = e.clone();
    loop {
        match &cur.x {
            ExpX::Call(CallFun::Fun(f, _), _, args)
                if f.path.segments.last().map(|s| s.as_str()) == Some("push") && args.len() == 2 =>
            {
                if !matches!(&args[1].x, ExpX::Const(_)) {
                    return false;
                }
                cur = args[0].clone();
            }
            ExpX::Call(CallFun::Fun(f, _), _, args)
                if f.path.segments.last().map(|s| s.as_str()) == Some("empty") && args.is_empty() =>
            {
                return true;
            }
            _ => return false,
        }
    }
}

fn contains_lambda(e: &Exp) -> bool {
    let mut map = crate::sst_visitor::VisitorScopeMap::new();
    crate::sst_visitor::exp_visitor_check(e, &mut map, &mut |x: &Exp, _| match &x.x {
        ExpX::Bind(b, _) if matches!(b.x, BndX::Lambda(..)) => Err(()),
        _ => Ok(()),
    })
    .is_err()
}

/// Seq-valued `subrange`/`add`/`update`/`push` applications in `e` with no bound variables
fn seq_subterms(e: &Exp) -> Vec<Exp> {
    let mut out: Vec<Exp> = vec![];
    let mut map = crate::sst_visitor::VisitorScopeMap::new();
    let _ = crate::sst_visitor::exp_visitor_check(e, &mut map, &mut |x: &Exp, map| {
        if let ExpX::Call(CallFun::Fun(f, _), _, _) = &x.x {
            let last = f.path.segments.last().map(|s| s.as_str());
            let is_seq = f.path.krate == crate::ast::CrateId::Vstd
                && f.path.segments.len() >= 3
                && f.path.segments[0].as_str() == "seq";
            if is_seq
                && matches!(last, Some("subrange" | "add" | "update"))
                && crate::sst_util::free_vars_exp(x).keys().all(|v| !map.contains_key(v))
                && !out.iter().any(|o| format!("{:?}", o.x) == format!("{:?}", x.x))
            {
                out.push(x.clone());
            }
        }
        Ok::<(), ()>(())
    });
    out
}

