use crate::ast::{
    Axiom, BinaryOp, BindX, Decl, DeclX, Expr, ExprX, Ident, MultiOp, Quant, Query, StmtX, TypX,
    UnaryOp,
};
use crate::ast_util::{ident_var, mk_and, mk_not};
use crate::context::{AssertionInfo, AxiomInfo, Context, ContextState, SmtSolver, ValidityResult};
use crate::def::{GLOBAL_PREFIX_LABEL, PREFIX_LABEL};
use crate::messages::{ArcDynMessage, Diagnostics};
pub use crate::model::{Model, ModelDef};
use std::collections::HashMap;
use std::sync::Arc;

fn label_asserts<'ctx>(
    context: &mut Context,
    infos: &mut Vec<AssertionInfo>,
    axiom_infos: &mut Vec<AxiomInfo>,
    expr: &Expr,
) -> Expr {
    match &**expr {
        ExprX::Binary(op @ BinaryOp::Implies, lhs, rhs)
        | ExprX::Binary(op @ BinaryOp::Eq, lhs, rhs) => {
            // asserts are on rhs of =>
            // (slight hack to also allow rhs of == for quantified function definitions)
            Arc::new(ExprX::Binary(
                op.clone(),
                lhs.clone(),
                label_asserts(context, infos, axiom_infos, rhs),
            ))
        }
        ExprX::Multi(op @ MultiOp::And, exprs) | ExprX::Multi(op @ MultiOp::Or, exprs) => {
            let mut exprs_vec: Vec<Expr> = Vec::new();
            for expr in exprs.iter() {
                exprs_vec.push(label_asserts(context, infos, axiom_infos, expr));
            }
            Arc::new(ExprX::Multi(*op, Arc::new(exprs_vec)))
        }
        ExprX::Bind(bind, body) => match &**bind {
            BindX::Quant(Quant::Forall, _, _, _) => Arc::new(ExprX::Bind(
                bind.clone(),
                label_asserts(context, infos, axiom_infos, body),
            )),
            _ => expr.clone(),
        },
        ExprX::LabeledAssertion(assert_id, error, filter, expr) => {
            let label = Arc::new(PREFIX_LABEL.to_string() + &infos.len().to_string());
            let decl = Arc::new(DeclX::Const(label.clone(), Arc::new(TypX::Bool)));
            let assertion_info = AssertionInfo {
                assert_id: assert_id.clone(),
                error: error.clone(),
                label: label.clone(),
                filter: filter.clone(),
                decl,
                disabled: false,
            };
            infos.push(assertion_info);
            let lhs = Arc::new(ExprX::Var(label));
            Arc::new(ExprX::Binary(
                BinaryOp::Implies,
                lhs,
                label_asserts(context, infos, axiom_infos, expr),
            ))
        }
        ExprX::LabeledAxiom(labels, filter, expr) => {
            let count = context.axiom_infos_count;
            context.axiom_infos_count += 1;
            let label = Arc::new(GLOBAL_PREFIX_LABEL.to_string() + &count.to_string());
            let decl = Arc::new(DeclX::Const(label.clone(), Arc::new(TypX::Bool)));
            let axiom_info = AxiomInfo {
                labels: labels.clone(),
                label: label.clone(),
                filter: filter.clone(),
                decl,
            };
            axiom_infos.push(axiom_info);
            let lhs = Arc::new(ExprX::Var(label));
            Arc::new(ExprX::Binary(
                BinaryOp::Implies,
                lhs,
                label_asserts(context, infos, axiom_infos, expr),
            ))
        }
        _ => expr.clone(),
    }
}

/// In SMT-LIB, functions applied to zero arguments are considered constants.
/// REVIEW: maybe AIR should follow this design for consistency.
fn elim_zero_args_expr(expr: &Expr) -> Expr {
    crate::visitor::map_expr_visitor(expr, &mut |expr| match &**expr {
        ExprX::Apply(x, es) if es.len() == 0 => Arc::new(ExprX::Var(x.clone())),
        _ => expr.clone(),
    })
}

pub(crate) fn smt_add_decl<'ctx>(context: &mut Context, decl: &Decl) {
    match &**decl {
        DeclX::Sort(_) | DeclX::Datatypes(_) | DeclX::Const(_, _) | DeclX::Fun(_, _, _) => {
            context.smt_log.log_decl(decl);
        }
        DeclX::Var(_, _) => {}
        DeclX::Axiom(Axiom { named, expr }) => {
            let expr = elim_zero_args_expr(expr);
            let mut infos: Vec<AssertionInfo> = Vec::new();
            let mut axiom_infos: Vec<AxiomInfo> = Vec::new();
            let labeled_expr = label_asserts(context, &mut infos, &mut axiom_infos, &expr);
            for info in axiom_infos {
                crate::typecheck::add_decl(context, &info.decl, true).unwrap();
                context
                    .axiom_infos
                    .insert(info.label.clone(), Arc::new(info.clone()))
                    .expect("internal error: duplicate assert_info");
                smt_add_decl(context, &info.decl);
            }
            context.smt_log.log_assert(named, &labeled_expr);
        }
    }
}

impl SmtSolver {
    /// The `(get-info :reason-unknown)` responses that mean "the solver hit its
    /// resource/time budget".  These vary across Z3 versions.
    pub fn reason_unknown_canceled_strs(&self) -> &'static [&'static str] {
        match self {
            SmtSolver::Z3 => &[
                "(:reason-unknown \"canceled\")",
                "(:reason-unknown \"max. resource limit exceeded\")",
            ],
            SmtSolver::Cvc5 => &["(:reason-unknown resourceout)"],
        }
    }

    pub fn reason_unknown_incomplete_str(&self) -> &str {
        match self {
            SmtSolver::Z3 => "(:reason-unknown \"(incomplete",
            SmtSolver::Cvc5 => "(:reason-unknown incomplete)",
        }
    }
}

pub type ReportLongRunning<'a> =
    (std::time::Duration, Box<dyn FnMut(std::time::Duration, bool) -> () + 'a>);

const GET_VERSION_RESPONSE_PREFIX: &str = "(:version";

pub(crate) fn smt_check_assertion<'ctx>(
    context: &mut Context,
    diagnostics: &impl Diagnostics,
    mut infos: Vec<AssertionInfo>,
    air_model: Model,
    only_check_earlier: bool,
    report_long_running: Option<&mut ReportLongRunning>,
) -> ValidityResult {
    let disabled_expr = if only_check_earlier {
        // disable all labels that come after the first known error
        let mut disabled: Vec<Expr> = Vec::new();
        let mut found_disabled = false;
        let mut found_enabled = false;
        for info in infos.iter_mut() {
            if found_disabled && !info.disabled {
                info.disabled = true;
                disabled.push(mk_not(&ident_var(&info.label)));
            }
            if info.disabled {
                found_disabled = true;
            } else {
                found_enabled = true;
            }
        }
        if only_check_earlier && !found_enabled {
            // no earlier assertions to check
            return ValidityResult::Valid(crate::context::UsageInfo::None);
        }
        Some(mk_and(&disabled))
    } else {
        None
    };

    context.smt_log.log_get_info("version");
    let smt_init_start_time = std::time::Instant::now();
    let smt_data = context.smt_log.take_pipe_data();
    // Under cross-check this chunk carries the declarations + query the secondary needs to
    // stay in lockstep; send_fanned mirrors it (draining the secondary's version reply).
    let early_smt_output = context.send_fanned(smt_data);
    context.time_smt_init += smt_init_start_time.elapsed();
    for line in early_smt_output {
        if line.starts_with(GET_VERSION_RESPONSE_PREFIX) {
            if let Some(expected_version) = &context.expected_solver_version {
                let value: &str = &line[GET_VERSION_RESPONSE_PREFIX.len()..line.len() - 1];
                let version = value.trim_matches(&[' ', '"'][..]);
                if version != expected_version.as_str() {
                    let solver = context.solver.name();
                    diagnostics.report(&context.message_interface.unexpected_solver_version(
                        solver,
                        &expected_version,
                        version,
                    ));
                    panic!(
                        "The verifier expects {} version \"{}\", found version \"{}\"",
                        solver, expected_version, version
                    );
                }
            }
        } else if context.ignore_unexpected_smt {
            diagnostics.report(&context.message_interface.bare(
                crate::messages::MessageLevel::Warning,
                format!("warning: unexpected SMT output: {}", line).as_str(),
            ));
        } else {
            return ValidityResult::UnexpectedOutput(line);
        }
    }

    if let Some(disabled_expr) = disabled_expr {
        context.smt_log.log_assert(&None, &disabled_expr);
    }

    let cross_check = context.cross_check_enabled();
    if matches!(context.solver, SmtSolver::Z3) && !cross_check {
        context.smt_log.log_set_option("rlimit", &context.rlimit.to_string());
        context.set_solver_option_u32("rlimit", context.rlimit, false);
    }

    context.smt_log.log_word("check-sat");

    // Run SMT solver
    let smt_run_start_time = std::time::Instant::now();
    let smt_data = context.smt_log.take_pipe_data();
    let (smt_output, secondary_output) = if cross_check {
        // The shared stream stays solver-neutral: inject the Z3-only rlimit into the primary
        // stream only, and fan the identical check-sat text to both solvers in parallel.
        let primary_prefix = format!("(set-option :rlimit {})\n", context.rlimit).into_bytes();
        context.check_sat_fanned(smt_data, primary_prefix, report_long_running)
    } else {
        let commands_handle = context.get_smt_process().send_commands_async(smt_data);
        let smt_output = if let Some((report_threshold, report_fn)) = report_long_running {
            match commands_handle.wait_timeout(*report_threshold) {
                Ok(smt_output) => smt_output,
                Err(handle) => {
                    report_fn(smt_run_start_time.elapsed(), false);
                    let smt_output = handle.wait();
                    report_fn(smt_run_start_time.elapsed(), true);
                    smt_output
                }
            }
        } else {
            commands_handle.wait()
        };
        (smt_output, None)
    };
    context.time_smt_run += smt_run_start_time.elapsed();

    // Cross-check reconciliation (design 05 §2.2): compare the two verdicts on the identical
    // query before interpreting the primary's. An unsat/sat disagreement (or, under Strict,
    // an unconfirmed proof) becomes a hard error dumped to .verus-solver-log; a Warn-level
    // non-confirmation emits a warning and defers to the primary.
    if let Some(secondary_output) = &secondary_output {
        if let Some(err) = context.cross_check_finish(diagnostics, &smt_output, secondary_output) {
            context.state = ContextState::FoundResult;
            return ValidityResult::Invalid(None, Some(err), None);
        }
    }

    #[derive(PartialEq, Eq)]
    enum SmtOutput {
        Unsat,
        Sat,
        Unknown,
    }

    // Process SMT results
    let mut unsat = None;
    for line in smt_output {
        if line == "unsat" {
            assert!(unsat == None);
            unsat = Some(SmtOutput::Unsat);
        } else if line == "sat" {
            assert!(unsat == None);
            unsat = Some(SmtOutput::Sat);
        } else if line == "unknown" || line == "cvc5 interrupted by timeout." {
            assert!(unsat == None);
            unsat = Some(SmtOutput::Unknown);
        } else if context.ignore_unexpected_smt {
            diagnostics.report(&context.message_interface.bare(
                crate::messages::MessageLevel::Warning,
                format!("warning: unexpected SMT output: {}", line).as_str(),
            ));
        } else {
            return ValidityResult::UnexpectedOutput(line);
        }
    }

    if matches!(context.solver, SmtSolver::Z3) && !cross_check {
        context.smt_log.log_set_option("rlimit", "0");
        context.set_solver_option_u32("rlimit", 0, false);
    }

    let unsat = unsat.expect("expected sat/unsat/unknown from SMT solver");

    enum ResultDetermination<T> {
        Determined(ValidityResult),
        Undetermined(T),
    }

    let unsat_result = match unsat {
        SmtOutput::Unsat => ResultDetermination::Undetermined(true),
        SmtOutput::Sat => ResultDetermination::Undetermined(false),
        SmtOutput::Unknown => {
            context.smt_log.log_get_info("reason-unknown");
            let smt_data = context.smt_log.take_pipe_data();
            let smt_output = context.get_smt_process().send_commands(smt_data);

            #[derive(PartialEq, Eq)]
            enum SmtReasonUnknown {
                Canceled,
                Incomplete,
                Unknown,
            }

            let mut reason = None;
            for line in smt_output {
                if context.solver.reason_unknown_canceled_strs().iter().any(|s| line == *s) {
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Canceled);
                } else if line == "(:reason-unknown \"unknown\")" {
                    // it appears this sometimes happens when rlimit is exceeded
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Unknown);
                } else if line.starts_with(context.solver.reason_unknown_incomplete_str()) {
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Incomplete);
                } else if line
                    == "(:reason-unknown \"smt tactic failed to show goal to be sat/unsat (incomplete quantifiers)\")"
                {
                    // longer message shows up when there's no push/pop around the query
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Incomplete);
                } else if context.ignore_unexpected_smt {
                    diagnostics.report(&context.message_interface.bare(
                        crate::messages::MessageLevel::Warning,
                        format!("warning: unexpected SMT output: {}", line).as_str(),
                    ));
                } else {
                    return ValidityResult::UnexpectedOutput(line);
                }
            }

            match reason.expect("expected :reason-unknown") {
                SmtReasonUnknown::Canceled | SmtReasonUnknown::Unknown => {
                    context.state = ContextState::Canceled;
                    ResultDetermination::Determined(ValidityResult::Canceled)
                }
                SmtReasonUnknown::Incomplete => ResultDetermination::Undetermined(false),
            }
        }
    };

    match unsat_result {
        ResultDetermination::Determined(r) => r,
        ResultDetermination::Undetermined(true) => {
            context.state = ContextState::FoundResult;

            let usage_info = if context.usage_info_enabled {
                context.smt_log.log_word("get-unsat-core");

                let smt_data = context.smt_log.take_pipe_data();
                let smt_output = context.get_smt_process().send_commands(smt_data);

                let mut smt_output = smt_output.into_iter();
                let unsat_core_str =
                    smt_output.next().expect("expected one line in the unsat core output");
                assert!(smt_output.next().is_none());

                let fun_names: Vec<Ident> = unsat_core_str
                    .strip_prefix('(')
                    .expect("invalid unsat core")
                    .strip_suffix(')')
                    .expect("invalid unsat core")
                    .split_terminator(' ')
                    .map(|x| Arc::new(x.to_owned()))
                    .collect();
                crate::context::UsageInfo::UsedAxioms(fun_names)
            } else {
                crate::context::UsageInfo::None
            };

            ValidityResult::Valid(usage_info)
        }
        ResultDetermination::Undetermined(false) => {
            if context.single_check_query {
                // one obligation: nothing to localize, report it at the query level
                context.state = ContextState::FoundInvalid(infos, None);
                ValidityResult::Invalid(None, None, None)
            } else {
                smt_get_model(context, infos, air_model)
            }
        }
    }
}

pub(crate) fn smt_get_rlimit_count(context: &mut Context) -> Result<u64, ValidityResult> {
    assert!(matches!(context.solver, SmtSolver::Z3)); // the CVC5 output format for statistics is different

    // Under cross-check, the accumulated declarations must reach the secondary before this
    // Z3-only statistics query (which is sent to the primary alone).
    context.flush_shared_pending();
    context.smt_log.log_get_info("all-statistics");
    let smt_data = context.smt_log.take_pipe_data();
    let smt_output = context.get_smt_process().send_commands(smt_data);
    let statistics = crate::parser::parse_sexpression(&smt_output);
    let stats_map = statistics
        .as_list()
        .unwrap()
        .chunks(2)
        .map(|chunk| {
            let [key, value] = chunk else {
                return Err(ValidityResult::UnexpectedOutput(format!(
                    "expected key-value pair in statistics"
                )));
            };
            let Some((key, value)) = key
                .as_atom()
                .map(|key| &key.as_str()[1..])
                .and_then(|key| value.as_atom().map(|value| (key, value.as_str())))
            else {
                return Err(ValidityResult::UnexpectedOutput(format!(
                    "expected key-value pair in statistics"
                )));
            };
            Ok((key, value))
        })
        .collect::<Result<HashMap<&str, &str>, ValidityResult>>()?;
    // `rlimit-count` may be absent (e.g. a prelude-free bit_vector query with nothing yet to count);
    // treat it as zero. This is resource accounting only, never the verification result.
    let rlimit_count = match stats_map.get("rlimit-count") {
        None => 0,
        Some(value) => {
            let Some(count) = value.parse().ok() else {
                return Err(ValidityResult::UnexpectedOutput(format!(
                    "expected rlimit-count in smt statistics"
                )));
            };
            count
        }
    };
    Ok(rlimit_count)
}

/// Check whether the assertion with label `infos[i].label` is violated on its own:
/// under `(push)`, disable every other still-enabled label and re-run `check-sat`.
/// `sat` means the violation is attributable to this assertion; `unsat` means the
/// label was merely assigned `true` by the solver without its assertion failing.
/// Anything else (unknown, timeout, unexpected output) is treated conservatively as
/// confirmed, so that an error is never suppressed by a solver hiccup.
fn confirm_label(context: &mut Context, infos: &Vec<AssertionInfo>, i: usize) -> bool {
    context.smt_log.log_push();
    for (j, info) in infos.iter().enumerate() {
        if j != i && !info.disabled {
            context.smt_log.log_assert(&None, &mk_not(&ident_var(&info.label)));
        }
    }
    if matches!(context.solver, SmtSolver::Z3) {
        context.smt_log.log_set_option("rlimit", &context.rlimit.to_string());
    }
    context.smt_log.log_word("check-sat");
    if matches!(context.solver, SmtSolver::Z3) {
        context.smt_log.log_set_option("rlimit", "0");
    }
    context.smt_log.log_pop();
    let smt_data = context.smt_log.take_pipe_data();
    let smt_output = context.get_smt_process().send_commands(smt_data);
    let mut result = true;
    for line in smt_output {
        if line == "unsat" {
            result = false;
        } else if line == "sat" {
            result = true;
        }
    }
    result
}

/// Check whether the premise (axiom) labelled `target` is genuinely the clause whose
/// failure produced the counterexample for assertion `infos[assertion]`. A callee's
/// requires axiom has the shape `req%f(args) == (G_1 => c_1) && .. && (G_n => c_n)`, so
/// `req%f` can be false only via a clause `c_k` whose label `G_k` is true. Z3's partial
/// model leaves the irrelevant `G_k` unconstrained (at most one true); cvc5's total model
/// assigns every constant, so several `G_k` come back true and the genuine one must be
/// distinguished.
///
/// The test isolates a single clause: keep the chosen assertion active (disable every
/// other still-enabled assertion label), force `target` true and every other candidate
/// premise label false, then re-run `check-sat`. With the other premise labels off their
/// clauses are vacuous, so `req%f` collapses to exactly `c_target`, and:
///   * `sat` — `c_target` on its own can still make the assertion fail, so it is a
///     genuine culprit: keep the label (return `true`).
///   * `unsat` — with only `c_target` active the assertion can no longer fail, so
///     `c_target` holds and the label is spurious (return `false`).
///   * anything else (unknown, timeout, unexpected output) — treated conservatively as
///     genuine, so an informative label is never dropped on a solver hiccup.
/// Note the polarity matches `confirm_label` (`sat` confirms), but the extra assumptions
/// differ: here we pin one premise clause on and the rest off, rather than pinning one
/// assertion on and the rest off.
fn confirm_axiom_label(
    context: &mut Context,
    infos: &Vec<AssertionInfo>,
    assertion: usize,
    target: &Ident,
    other_candidates: &[Ident],
) -> bool {
    context.smt_log.log_push();
    for (j, info) in infos.iter().enumerate() {
        if j != assertion && !info.disabled {
            context.smt_log.log_assert(&None, &mk_not(&ident_var(&info.label)));
        }
    }
    context.smt_log.log_assert(&None, &ident_var(target));
    for other in other_candidates {
        context.smt_log.log_assert(&None, &mk_not(&ident_var(other)));
    }
    if matches!(context.solver, SmtSolver::Z3) {
        context.smt_log.log_set_option("rlimit", &context.rlimit.to_string());
    }
    context.smt_log.log_word("check-sat");
    if matches!(context.solver, SmtSolver::Z3) {
        context.smt_log.log_set_option("rlimit", "0");
    }
    context.smt_log.log_pop();
    let smt_data = context.smt_log.take_pipe_data();
    let smt_output = context.get_smt_process().send_commands(smt_data);
    let mut result = true;
    for line in smt_output {
        if line == "unsat" {
            result = false;
        } else if line == "sat" {
            result = true;
        }
    }
    result
}

fn smt_get_model(
    context: &mut Context,
    mut infos: Vec<AssertionInfo>,
    air_model: Model,
) -> ValidityResult {
    let mut discovered_additional_info: Vec<ArcDynMessage> = Vec::new();

    context.smt_log.log_word("get-model");

    let smt_data = context.smt_log.take_pipe_data();
    let smt_output = context.get_smt_process().send_commands(smt_data);

    if smt_output.iter().any(|line| line.contains("model is not available")) {
        // when we don't use incremental solving, sometime the model is not available when the z3 result is unknown
        context.state = ContextState::FoundInvalid(infos, None);
        return ValidityResult::Invalid(None, None, None);
    };

    let model =
        crate::parser::Parser::new(context.message_interface.clone()).lines_to_model(&smt_output);
    let mut model_defs: HashMap<Ident, ModelDef> = HashMap::new();
    for def in model.iter() {
        model_defs.insert(def.name.clone(), def.clone());
    }
    // Each assertion A_i is encoded as (label_i => A_i), so a violated assertion has
    // label_i = true in the model. The converse does not hold: a label that is
    // irrelevant to the violation is unconstrained, and the solver is free to assign
    // it true as well. Z3's (partial) models leave such labels out, but cvc5 assigns a
    // value to every constant, so several labels can be true at once. When that
    // happens, confirm a candidate before reporting it: with every other enabled label
    // disabled, the query must still be satisfiable.
    let candidates: Vec<usize> = infos
        .iter()
        .enumerate()
        .filter(|(_, info)| {
            !info.disabled
                && model_defs.get(&info.label).map(|def| *def.body == "true").unwrap_or(false)
        })
        .map(|(i, _)| i)
        .collect();
    let needs_confirmation = candidates.len() > 1;
    let mut spurious: usize = 0;
    // Select the failing assertion, but defer disabling its label: the axiom-label
    // confirmation below needs to re-run `check-sat` with this assertion still active
    // (isolated) so it can test which premise the failure genuinely depends on.
    let mut chosen: Option<usize> = None;
    for i in candidates {
        if needs_confirmation && !confirm_label(context, &infos, i) {
            spurious += 1;
            continue;
        }
        chosen = Some(i);
        break;
    }
    if context.debug && spurious > 0 {
        println!("ignored {} spuriously true assertion label(s) in model", spurious);
    }
    let chosen = chosen.expect("discovered_error");
    let discovered_error = infos[chosen].clone();
    let discovered_assert_id = infos[chosen].assert_id.clone();

    let mut axiom_infos: Vec<Arc<AxiomInfo>> =
        context.axiom_infos.map().values().cloned().collect();
    axiom_infos.sort_by_key(|info| info.label.clone());
    // stabilize order
    // Axiom (premise) labels attribute additional info to the error, e.g. which
    // precondition of a callee failed. A callee's requires axiom has the shape
    // `req%f(args) == (G_1 => c_1) && .. && (G_n => c_n)`, so a model sets `G_k = true`
    // only when clause `c_k` participates in the counterexample. Z3's partial model
    // leaves the irrelevant `G_k` unconstrained, so at most one is true; cvc5's total
    // model assigns every constant, so several `G_k` can be true and the first in sorted
    // order may be a premise that actually holds — dropping the genuine `proof_note`
    // label. When more than one candidate premise label is true, `confirm_axiom_label`
    // isolates each clause to find the genuine culprit (see its doc comment).
    let axiom_candidates: Vec<usize> = axiom_infos
        .iter()
        .enumerate()
        .filter(|(_, info)| {
            model_defs.get(&info.label).map(|def| *def.body == "true").unwrap_or(false)
                && (info.filter.is_none() || info.filter == discovered_error.filter)
        })
        .map(|(i, _)| i)
        .collect();
    let needs_axiom_confirmation = axiom_candidates.len() > 1;
    let candidate_labels: Vec<Ident> =
        axiom_candidates.iter().map(|&i| axiom_infos[i].label.clone()).collect();
    let mut spurious_axioms: usize = 0;
    for (pos, &i) in axiom_candidates.iter().enumerate() {
        if needs_axiom_confirmation {
            let others: Vec<Ident> = candidate_labels
                .iter()
                .enumerate()
                .filter(|(p, _)| *p != pos)
                .map(|(_, l)| l.clone())
                .collect();
            if !confirm_axiom_label(context, &infos, chosen, &axiom_infos[i].label, &others) {
                spurious_axioms += 1;
                continue;
            }
        }
        discovered_additional_info.append(&mut axiom_infos[i].labels.clone());
        break;
    }
    if context.debug && spurious_axioms > 0 {
        println!("ignored {} spuriously true axiom label(s) in model", spurious_axioms);
    }

    // Disable the chosen assertion's label so subsequent check-sat calls surface the
    // remaining errors.
    infos[chosen].disabled = true;
    let disable_label = mk_not(&ident_var(&infos[chosen].label));
    context.smt_log.log_assert(&None, &disable_label);

    if context.debug {
        println!("Z3 model: {:?}", model);
    }

    // Attach the additional info to the error
    // For example, the error might be something like "precondition not satisfied"
    // (an error which comes from the air assert statement)
    // and the additional info might tell you _which_ precondition failed
    // (a label that comes from one of the axioms associated
    // to the function precondition)

    let error = discovered_error.error;
    let e = context.message_interface.append_labels(&error, &discovered_additional_info);
    context.state = ContextState::FoundInvalid(infos, Some(air_model.clone()));
    ValidityResult::Invalid(Some(air_model), Some(e), discovered_assert_id)
}

pub(crate) fn smt_check_query<'ctx>(
    context: &mut Context,
    diagnostics: &impl Diagnostics,
    query: &Query,
    air_model: Model,
    report_long_running: Option<&mut ReportLongRunning>,
) -> ValidityResult {
    if !context.single_check_query {
        context.smt_log.log_push();
        context.push_name_scope();
    }

    let rlimit_count_1 = if matches!(context.solver, SmtSolver::Z3) {
        let rlimit_count = match smt_get_rlimit_count(context) {
            Ok(rlimit_count) => rlimit_count,
            Err(e) => return e,
        };
        Some(rlimit_count)
    } else {
        None
    };

    // add query-local declarations
    for decl in query.local.iter() {
        if let Err(err) = crate::typecheck::add_decl(context, decl, false) {
            return ValidityResult::TypeError(err);
        }
        smt_add_decl(context, decl);
    }

    // after lowering, there should be just one assertion
    let assertion = match &*query.assertion {
        StmtX::Assert(_, _, _, expr) => expr,
        _ => panic!("internal error: query not lowered"),
    };
    let assertion = elim_zero_args_expr(assertion);

    // add labels to assertions for error reporting
    let mut infos: Vec<AssertionInfo> = Vec::new();
    let mut axiom_infos: Vec<AxiomInfo> = Vec::new();
    let labeled_assertion = label_asserts(context, &mut infos, &mut axiom_infos, &assertion);
    for info in &infos {
        context.smt_log.comment(&context.message_interface.get_note(&info.error));
        if let Err(err) = crate::typecheck::add_decl(context, &info.decl, false) {
            return ValidityResult::TypeError(err);
        }
        smt_add_decl(context, &info.decl);
    }

    // check assertion
    let not_expr = Arc::new(ExprX::Unary(UnaryOp::Not, labeled_assertion));
    context.smt_log.log_assert(&None, &not_expr);

    let rlimit_count_2 = if matches!(context.solver, SmtSolver::Z3) {
        let rlimit_count = match smt_get_rlimit_count(context) {
            Ok(rlimit_count) => rlimit_count,
            Err(e) => return e,
        };
        Some(rlimit_count)
    } else {
        None
    };

    let result =
        smt_check_assertion(context, diagnostics, infos, air_model, false, report_long_running);

    if matches!(context.solver, SmtSolver::Z3) {
        let (ctx_rlimit_init, ctx_rlimit_run) = context.rlimit_count.unwrap();
        let rlimit_count_3 = match smt_get_rlimit_count(context) {
            Ok(rlimit_count) => rlimit_count,
            Err(e) => return e,
        };
        let rlimit_init = rlimit_count_2.unwrap() - rlimit_count_1.unwrap();
        let rlimit_run = rlimit_count_3 - rlimit_count_2.unwrap();
        context.rlimit_count = Some((ctx_rlimit_init + rlimit_init, ctx_rlimit_run + rlimit_run));
    }

    result
}
