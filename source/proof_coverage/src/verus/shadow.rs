//! Shadow evidence pipeline: instrument, replay, solve, retrieve cores.
//!
//! The canonical query is never modified (`PROOF_COVERAGE.md` §2).
//! For each observed solver context we buffer the ambient command stream and
//! an *instrumented clone* of every query; at `on_finish` we replay them into
//! our own `air::Context` (same code, same prelude, own Z3 process) with
//! unsat-core production enabled, and join the returned label sets back to
//! occurrences.
//!
//! Instrumentation polarity (the load-bearing invariant):
//!
//! ```text
//! premise      Assume(P)     ->  Assume(z => P)                    plus named unit axiom z
//! obligation   Assert(G)     ->  Assert(z && G)                    plus named unit axiom z
//! ```
//!
//! Statements are otherwise untouched; the clone is the canonical query plus
//! guards. The equalities the SSA pass (`var_to_const`) itself generates —
//! one per `Assign` (`x@n+1 == e`) and the version reconciliations at every
//! control-flow join (`x@m == x@k` per `Switch` arm, `Breakable` exit and
//! `Break`) — are guarded *after* SSA, through the pass's own generation
//! trace (`air::var_to_const::SsaTrace`) and the `Context::ssa_rewrite` hook:
//!
//! ```text
//! SSA-generated  Assume(x@m == e)   ->  Assume(z => x@m == e)      z minted from the trace
//! ```
//!
//! The trace is computed once here, on the structured clone, to mint the
//! activations and to name each equality's site: an `Assign`'s equality keeps
//! the statement's own site; a reconciliation gets a `Reconciliation` site
//! naming the join statement, arm, variable and versions. At solve time the
//! hook receives the trace of the query as actually lowered and checks it
//! against the plan position by position before guarding; any disagreement
//! discards the query's evidence (`ssa_trace_mismatch`).
//!
//! With every `z` asserted true the query proves exactly what it did before.
//! A label returned by the solver belongs to one jointly sufficient support
//! witness. Cores are generally non-minimal and non-unique, so absence from
//! one core is never interpreted as semantic irrelevance. An obligation
//! label in the witness distinguishes a non-vacuous refutation of that
//! obligation from a contradictory prefix that can discharge `!z` directly.

use air::ast::{
    AssertId, Axiom, BinaryOp, BindX, Command, Commands, Decl, DeclX, Expr, ExprX, MultiOp, Query,
    QueryX, Stmt, StmtX,
};
use air::context::{Context, SmtSolver, SolverReplayConfig, UsageInfo, ValidityResult};
use air::messages::{ArcDynMessage, Diagnostics, MessageLevel};
use air::var_to_const::{SsaOrigin, SsaTrace};
use proof_coverage_core::identity::{QuerySiteId, SolverToken, SsaJoin};
use std::collections::{BTreeMap, HashMap};
use std::path::Path;
use std::sync::{Arc, Mutex};

/// Buffered work for one solver context, replayed in order at finish.
pub enum ShadowEvent {
    /// Ambient commands (setup, function-context axioms) as installed.
    Ambient { solver_config: SolverReplayConfig, commands: Commands },
    /// An instrumented clone of a canonical query; `record_idx` points at the
    /// producer's `QueryRecord`.
    Query {
        solver_config: SolverReplayConfig,
        record_idx: usize,
        command: Command,
        /// The post-SSA guards to apply, in SSA generation order.
        ssa_plan: Vec<SsaStep>,
    },
}

/// One planned post-SSA guard: what the k-th equality the SSA pass generates
/// must be, and the activation constant to guard it with (`None`: leave it
/// unguarded — a reconciliation of a join the focused query no longer shares
/// with its batch).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SsaStep {
    pub kind: SsaKind,
    pub z: Option<String>,
}

/// The shape of an SSA-generated equality, for checking a trace against a
/// plan without pointer identities.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SsaKind {
    Assign,
    Reconcile { join: SsaJoin, var: String, from: u32, to: u32 },
}

fn ssa_join(join: air::var_to_const::SsaJoin) -> SsaJoin {
    match join {
        air::var_to_const::SsaJoin::SwitchArm(i) => SsaJoin::SwitchArm(i as u32),
        air::var_to_const::SsaJoin::Fallthrough => SsaJoin::Fallthrough,
        air::var_to_const::SsaJoin::Break => SsaJoin::Break,
    }
}

fn ssa_kind(origin: &SsaOrigin) -> SsaKind {
    match origin {
        SsaOrigin::Assign { .. } => SsaKind::Assign,
        SsaOrigin::Reconcile { join, var, from, to, .. } => {
            SsaKind::Reconcile { join: ssa_join(*join), var: var.to_string(), from: *from, to: *to }
        }
    }
}

/// Structural path of every statement of a structured query, by pointer.
/// The same coordinates `instr_stmt` and the producer's walker use.
fn ptr_paths(stmt: &Stmt) -> HashMap<usize, String> {
    fn walk(stmt: &Stmt, path: &mut Vec<String>, out: &mut HashMap<usize, String>) {
        out.insert(Arc::as_ptr(stmt) as usize, path.join("."));
        match &**stmt {
            StmtX::Block(stmts) => {
                for (i, s) in stmts.iter().enumerate() {
                    path.push(format!("b{}", i));
                    walk(s, path, out);
                    path.pop();
                }
            }
            StmtX::Switch(stmts) => {
                for (i, s) in stmts.iter().enumerate() {
                    path.push(format!("s{}", i));
                    walk(s, path, out);
                    path.pop();
                }
            }
            StmtX::DeadEnd(s) => {
                path.push("d".to_string());
                walk(s, path, out);
                path.pop();
            }
            StmtX::Breakable(_, s) => {
                path.push("k".to_string());
                walk(s, path, out);
                path.pop();
            }
            StmtX::Assume(..)
            | StmtX::Assert(..)
            | StmtX::Assign(..)
            | StmtX::Havoc(..)
            | StmtX::Snapshot(..)
            | StmtX::Break(..) => {}
        }
    }
    let mut out = HashMap::new();
    walk(stmt, &mut Vec::new(), &mut out);
    out
}

/// Run the SSA pass on a structured query for its trace only, and name each
/// generated equality's site in the query's own coordinates.
fn ssa_sites(query: &Query) -> Result<Vec<(SsaKind, QuerySiteId)>, String> {
    let paths = ptr_paths(&query.assertion);
    let (_, _, _, trace) = air::var_to_const::lower_query(query);
    trace
        .generated
        .iter()
        .map(|(_, origin)| {
            let source = match origin {
                SsaOrigin::Assign { source } | SsaOrigin::Reconcile { source, .. } => *source,
            };
            let at = paths
                .get(&source)
                .ok_or_else(|| {
                    format!("SSA trace names a statement outside the query: {origin:?}")
                })?
                .clone();
            let kind = ssa_kind(origin);
            let site = match &kind {
                SsaKind::Assign => QuerySiteId::Statement(at),
                SsaKind::Reconcile { join, var, from, to } => QuerySiteId::Reconciliation {
                    at,
                    join: *join,
                    var: var.clone(),
                    from: *from,
                    to: *to,
                },
            };
            Ok((kind, site))
        })
        .collect()
}

/// Shared between a replay context and its `ssa_rewrite` hook: the plan for
/// the query about to be checked, and the first disagreement observed.
#[derive(Default)]
struct SsaHookState {
    plan: Option<Vec<SsaStep>>,
    mismatch: Option<String>,
}

/// Guard the SSA-generated equalities of a lowered query according to `plan`.
/// The trace must agree with the plan position by position.
fn apply_ssa_plan(query: &Query, trace: &SsaTrace, plan: &[SsaStep]) -> Result<Query, String> {
    if trace.generated.len() != plan.len() {
        return Err(format!(
            "SSA generated {} equalities, plan expected {}",
            trace.generated.len(),
            plan.len()
        ));
    }
    let mut guards: HashMap<usize, String> = HashMap::new();
    for ((ptr, origin), step) in trace.generated.iter().zip(plan) {
        let kind = ssa_kind(origin);
        if kind != step.kind {
            return Err(format!("SSA trace {:?} disagrees with plan {:?}", kind, step.kind));
        }
        if let Some(z) = &step.z {
            guards.insert(*ptr, z.clone());
        }
    }
    let mut applied = 0usize;
    fn rewrite(stmt: &Stmt, guards: &HashMap<usize, String>, applied: &mut usize) -> Stmt {
        if let Some(z) = guards.get(&(Arc::as_ptr(stmt) as usize)) {
            if let StmtX::Assume(expr) = &**stmt {
                *applied += 1;
                let z = air::ast_util::ident_var(&Arc::new(z.clone()));
                return Arc::new(StmtX::Assume(air::ast_util::mk_implies(&z, expr)));
            }
        }
        match &**stmt {
            StmtX::Block(stmts) => Arc::new(StmtX::Block(Arc::new(
                stmts.iter().map(|s| rewrite(s, guards, applied)).collect(),
            ))),
            StmtX::Switch(stmts) => Arc::new(StmtX::Switch(Arc::new(
                stmts.iter().map(|s| rewrite(s, guards, applied)).collect(),
            ))),
            StmtX::DeadEnd(s) => Arc::new(StmtX::DeadEnd(rewrite(s, guards, applied))),
            StmtX::Breakable(label, s) => {
                Arc::new(StmtX::Breakable(label.clone(), rewrite(s, guards, applied)))
            }
            _ => stmt.clone(),
        }
    }
    let assertion = rewrite(&query.assertion, &guards, &mut applied);
    if applied != guards.len() {
        return Err(format!(
            "SSA plan guarded {} equalities, {} were found in the lowered query",
            guards.len(),
            applied
        ));
    }
    Ok(Arc::new(QueryX { local: query.local.clone(), assertion }))
}

/// Swallows solver diagnostics from shadow runs (the canonical run already
/// reported everything user-visible).
struct SilentDiagnostics;

impl Diagnostics for SilentDiagnostics {
    fn report(&self, _msg: &ArcDynMessage) {}
    fn report_now(&self, _msg: &ArcDynMessage) {}
    fn report_as(&self, _msg: &ArcDynMessage, _level: MessageLevel) {}
    fn report_as_now(&self, _msg: &ArcDynMessage, _level: MessageLevel) {}
}

/// Result of shadow-solving one query.
pub struct ShadowOutcome {
    pub record_idx: usize,
    pub result: &'static str,
    /// Labels from `get-unsat-core` when the query was valid and measured.
    pub core: Option<Vec<String>>,
    /// Which solver-evidence path produced the core.
    pub evidence_backend: Option<&'static str>,
}

struct ReplayContext {
    context: Context,
    ssa: Arc<Mutex<SsaHookState>>,
    applied_options: Vec<(String, String)>,
    solver: SmtSolver,
    ignore_unexpected_smt: bool,
    debug: bool,
    expected_solver_version: Option<String>,
    single_check_query: bool,
    minimize_cores: bool,
}

impl ReplayContext {
    fn new(
        config: &SolverReplayConfig,
        proof_production: bool,
        minimize_cores: bool,
        log_prefix: Option<&Path>,
    ) -> Result<Self, &'static str> {
        if config.solver != SmtSolver::Z3 {
            return Err("unsupported_solver");
        }
        let message_interface = Arc::new(vir::messages::VirMessageInterface {});
        let mut context = Context::new(message_interface, config.solver);
        context.set_ignore_unexpected_smt(config.ignore_unexpected_smt);
        context.set_debug(config.debug);
        if let Some(version) = &config.expected_solver_version {
            context.set_expected_solver_version(version.clone());
        }
        context.set_rlimit(config.rlimit);
        for (option, value) in &config.option_history {
            context.set_z3_param(option, value);
        }
        if minimize_cores {
            // The shadow solver exists only to measure premise use. Ask Z3
            // to shrink each returned core without changing the canonical
            // verifier context or its option history.
            context.set_z3_param("smt.core.minimize", "true");
        }
        if config.single_check_query {
            context.set_single_check_query();
        }
        context.enable_usage_info();
        if proof_production {
            context.enable_proof_production();
        }
        let ssa: Arc<Mutex<SsaHookState>> = Arc::new(Mutex::new(SsaHookState::default()));
        let hook_state = Arc::clone(&ssa);
        context.ssa_rewrite = Some(Box::new(move |query: &Query, trace: &SsaTrace| {
            let mut state = hook_state.lock().unwrap();
            let Some(plan) = state.plan.take() else {
                return query.clone();
            };
            match apply_ssa_plan(query, trace, &plan) {
                Ok(query) => query,
                Err(error) => {
                    state.mismatch = Some(error);
                    query.clone()
                }
            }
        }));
        if let Some(prefix) = log_prefix {
            context.set_air_initial_log(Box::new(
                std::fs::File::create(prefix.with_extension("air-initial")).unwrap(),
            ));
            context.set_air_final_log(Box::new(
                std::fs::File::create(prefix.with_extension("air-final")).unwrap(),
            ));
            context.set_smt_log(Box::new(
                std::fs::File::create(prefix.with_extension("smt2")).unwrap(),
            ));
        }
        Ok(Self {
            context,
            ssa,
            applied_options: config.option_history.clone(),
            solver: config.solver,
            ignore_unexpected_smt: config.ignore_unexpected_smt,
            debug: config.debug,
            expected_solver_version: config.expected_solver_version.clone(),
            single_check_query: config.single_check_query,
            minimize_cores,
        })
    }

    /// Check one query command under a post-SSA guard plan. A trace that
    /// disagrees with the plan yields `ssa_trace_mismatch` and no evidence.
    fn check_planned(
        &mut self,
        command: &Command,
        ssa_plan: &[SsaStep],
    ) -> (&'static str, Option<Vec<String>>) {
        {
            let mut state = self.ssa.lock().unwrap();
            state.plan = Some(ssa_plan.to_vec());
            state.mismatch = None;
        }
        let result = self.context.command(
            &vir::messages::VirMessageInterface {},
            &SilentDiagnostics,
            command,
            Default::default(),
        );
        let mut state = self.ssa.lock().unwrap();
        state.plan = None;
        if let Some(error) = state.mismatch.take() {
            eprintln!("proof-coverage: shadow SSA trace mismatch: {error}");
            return ("ssa_trace_mismatch", None);
        }
        classify_result(result)
    }

    /// Advance to a later snapshot of the same canonical solver context.
    /// Option histories must be prefix-compatible: replay never guesses how
    /// to undo or reorder a setting.
    fn apply(&mut self, config: &SolverReplayConfig) -> Result<(), &'static str> {
        if config.solver != self.solver
            || config.ignore_unexpected_smt != self.ignore_unexpected_smt
            || config.debug != self.debug
            || config.option_history.len() < self.applied_options.len()
            || config.option_history[..self.applied_options.len()] != self.applied_options
        {
            return Err("config_mismatch");
        }
        match (&self.expected_solver_version, &config.expected_solver_version) {
            (Some(old), Some(new)) if old != new => return Err("config_mismatch"),
            (Some(_), None) => return Err("config_mismatch"),
            (None, Some(version)) => {
                self.context.set_expected_solver_version(version.clone());
                self.expected_solver_version = Some(version.clone());
            }
            _ => {}
        }
        if self.single_check_query && !config.single_check_query {
            return Err("config_mismatch");
        }
        let new_options = &config.option_history[self.applied_options.len()..];
        let core_minimize_overridden =
            new_options.iter().any(|(option, _)| option == "smt.core.minimize");
        for (option, value) in new_options {
            self.context.set_z3_param(option, value);
        }
        if self.minimize_cores && core_minimize_overridden {
            self.context.set_z3_param("smt.core.minimize", "true");
        }
        self.applied_options = config.option_history.clone();
        self.context.set_rlimit(config.rlimit);
        if config.single_check_query && !self.single_check_query {
            self.context.set_single_check_query();
            self.single_check_query = true;
        }
        Ok(())
    }
}

fn run_commands(replay: &mut ReplayContext, commands: &Commands) -> Result<(), &'static str> {
    let message_interface = vir::messages::VirMessageInterface {};
    let diagnostics = SilentDiagnostics;
    for command in commands.iter() {
        match replay.context.command(&message_interface, &diagnostics, command, Default::default())
        {
            ValidityResult::Valid(_) => {}
            ValidityResult::Invalid(..) => return Err("ambient_invalid"),
            ValidityResult::Canceled => return Err("ambient_canceled"),
            ValidityResult::TypeError(_) => return Err("ambient_type_error"),
            ValidityResult::UnexpectedOutput(_) => return Err("ambient_unexpected_output"),
        }
    }
    Ok(())
}

fn classify_result(result: ValidityResult) -> (&'static str, Option<Vec<String>>) {
    match result {
        ValidityResult::Valid(UsageInfo::UsedAxioms(names)) => {
            ("valid", Some(names.iter().map(|n| n.to_string()).collect::<Vec<_>>()))
        }
        ValidityResult::Valid(UsageInfo::None) => ("valid", Some(Vec::new())),
        ValidityResult::Invalid(..) => ("invalid", None),
        ValidityResult::Canceled => ("canceled", None),
        ValidityResult::TypeError(_) => ("type_error", None),
        ValidityResult::UnexpectedOutput(_) => ("unexpected_output", None),
    }
}

fn fresh_solve(
    ambient: &[(SolverReplayConfig, Commands)],
    query_config: &SolverReplayConfig,
    command: &Command,
    ssa_plan: &[SsaStep],
    proof_production: bool,
    minimize_cores: bool,
) -> Result<(&'static str, Option<Vec<String>>), &'static str> {
    let first_config = ambient.first().map(|(config, _)| config).unwrap_or(query_config);
    let mut replay = ReplayContext::new(first_config, proof_production, minimize_cores, None)?;
    for (config, commands) in ambient {
        replay.apply(config)?;
        run_commands(&mut replay, commands)?;
    }
    replay.apply(query_config)?;
    Ok(replay.check_planned(command, ssa_plan))
}

/// Replay one solver context's events and solve its instrumented queries.
/// The primary solve preserves the effective canonical AIR configuration and
/// adds unsat-core production and, when requested, shadow-only core
/// minimization. A canceled Z3 solve gets one fresh replay with proof
/// production additionally enabled; evidence is still obtained solely from
/// `get-unsat-core`.
pub fn solve_context(
    events: &[ShadowEvent],
    trace: bool,
    minimize_cores: bool,
    log_prefix: Option<&Path>,
    query_finished: &mut dyn FnMut(usize),
) -> Vec<ShadowOutcome> {
    let first_config = events.iter().find_map(|event| match event {
        ShadowEvent::Ambient { solver_config, .. } | ShadowEvent::Query { solver_config, .. } => {
            Some(solver_config)
        }
    });
    let Some(first_config) = first_config else {
        return Vec::new();
    };
    if first_config.solver != SmtSolver::Z3 {
        let outcomes: Vec<_> = events
            .iter()
            .filter_map(|event| match event {
                ShadowEvent::Query { record_idx, .. } => Some(ShadowOutcome {
                    record_idx: *record_idx,
                    result: "unsupported_solver",
                    core: None,
                    evidence_backend: None,
                }),
                _ => None,
            })
            .collect();
        for outcome in &outcomes {
            query_finished(outcome.record_idx);
        }
        return outcomes;
    }

    let mut replay = match ReplayContext::new(first_config, false, minimize_cores, log_prefix) {
        Ok(replay) => replay,
        Err(result) => {
            let outcomes: Vec<_> = events
                .iter()
                .filter_map(|event| match event {
                    ShadowEvent::Query { record_idx, .. } => Some(ShadowOutcome {
                        record_idx: *record_idx,
                        result,
                        core: None,
                        evidence_backend: None,
                    }),
                    _ => None,
                })
                .collect();
            for outcome in &outcomes {
                query_finished(outcome.record_idx);
            }
            return outcomes;
        }
    };
    let mut ambient: Vec<(SolverReplayConfig, Commands)> = Vec::new();
    let mut outcomes = Vec::new();
    let mut context_failure: Option<&'static str> = None;

    for event in events {
        match event {
            ShadowEvent::Ambient { solver_config, commands } => {
                ambient.push((solver_config.clone(), commands.clone()));
                if context_failure.is_none() {
                    context_failure = replay
                        .apply(solver_config)
                        .and_then(|()| run_commands(&mut replay, commands))
                        .err();
                }
            }
            ShadowEvent::Query { solver_config, record_idx, command, ssa_plan } => {
                if let Some(result) = context_failure {
                    outcomes.push(ShadowOutcome {
                        record_idx: *record_idx,
                        result,
                        core: None,
                        evidence_backend: None,
                    });
                    query_finished(*record_idx);
                    continue;
                }
                let start = std::time::Instant::now();
                if trace {
                    eprintln!(
                        "proof-coverage-shadow: start record_idx={} rlimit={} single_check={}",
                        record_idx, solver_config.rlimit, solver_config.single_check_query
                    );
                }
                let mut primary_issued = false;
                let primary = if solver_config.single_check_query {
                    primary_issued = true;
                    fresh_solve(
                        &ambient,
                        solver_config,
                        command,
                        ssa_plan,
                        false,
                        minimize_cores,
                    )
                } else {
                    replay.apply(solver_config).map(|()| {
                        primary_issued = true;
                        replay.check_planned(command, ssa_plan)
                    })
                };
                let (mut result, mut core) = match primary {
                    Ok(outcome) => outcome,
                    Err(result) => (result, None),
                };
                let mut evidence_backend = (result == "valid").then_some("unsat_core");
                let mut used_fallback = false;
                if result == "canceled" {
                    used_fallback = true;
                    match fresh_solve(
                        &ambient,
                        solver_config,
                        command,
                        ssa_plan,
                        true,
                        minimize_cores,
                    ) {
                        Ok(("valid", fallback_core)) => {
                            result = "valid";
                            core = fallback_core;
                            evidence_backend = Some("proof_enabled_unsat_core");
                        }
                        Ok(("canceled", _)) => result = "proof_fallback_canceled",
                        Ok(("invalid", _)) => result = "proof_fallback_invalid",
                        Ok(("type_error", _)) => result = "proof_fallback_type_error",
                        Ok(("unexpected_output", _)) => result = "proof_fallback_unexpected_output",
                        Ok((other, _)) => result = other,
                        Err(failure) => result = failure,
                    }
                }
                if trace {
                    eprintln!(
                        "proof-coverage-shadow: finish record_idx={} result={} elapsed_ms={} backend={} fallback={}",
                        record_idx,
                        result,
                        start.elapsed().as_millis(),
                        evidence_backend.unwrap_or("-"),
                        used_fallback,
                    );
                }
                outcomes.push(ShadowOutcome {
                    record_idx: *record_idx,
                    result,
                    core,
                    evidence_backend,
                });
                query_finished(*record_idx);
                if !solver_config.single_check_query && primary_issued {
                    replay.context.finish_query();
                }
            }
        }
    }
    outcomes
}

/// Instrument a structured query. Solver tokens are joined back to occurrence
/// records by typed structural site, never by parallel-walk position.
pub struct Instrumented {
    pub query: Query,
    pub site_tokens: BTreeMap<QuerySiteId, SolverToken>,
    /// Set when instrumentation discovered a duplicate structural identity.
    pub identity_error: Option<String>,
    /// Label for each query-local axiom, in declaration order.
    pub local_labels: Vec<String>,
    /// For each obligation, in walk order: the shadow-only assert id planted
    /// on it and its original (uninstrumented) formula — inputs to terminal
    /// decomposition and focusing.
    pub obligations: Vec<ObligationSite>,
    /// Definitions of lowering temporaries (`tmp%n = rhs` equality assumes),
    /// used to inline through Verus's lazy-&& encoding when decomposing.
    pub temp_defs: std::collections::BTreeMap<String, Expr>,
    /// (activation constant, label) for every activation minted, in order.
    /// Presence of a label in a derived query is decided by whether its
    /// constant *occurs* in that query — never by matching an expected
    /// formula shape, since air's constructors simplify (`mk_implies(z,
    /// false)` becomes `¬z`, `mk_implies(z, true)` disappears entirely).
    /// SSA-guarded sites are the exception: their constants occur only after
    /// SSA, so their presence is decided by the derived query's own trace.
    pub activations: Vec<(String, String)>,
    /// Activation constant per site, for planning derived queries.
    pub site_z: BTreeMap<QuerySiteId, String>,
    /// The post-SSA guard plan of the batch query itself.
    pub ssa_plan: Vec<SsaStep>,
}

pub struct ObligationSite {
    /// Label of the obligation's batch activation (identifies the parent
    /// occurrence).
    pub batch_label: String,
    /// Structural path of the obligation statement.
    pub path: String,
    /// Shadow-only assert id planted on the instrumented assert, used to
    /// locate it for focusing. Never observable outside the shadow run.
    pub shadow_assert_id: air::ast::AssertId,
    /// The original formula, before activation wrapping.
    pub original: Expr,
    pub msg: air::messages::ArcDynMessage,
    pub filter: air::ast::AxiomInfoFilter,
}

pub fn instrument_query(query_id: u64, query: &Query) -> Instrumented {
    let mut state = InstrState {
        query_id,
        counter: 0,
        site_tokens: BTreeMap::new(),
        site_z: BTreeMap::new(),
        identity_error: None,
        decls: Vec::new(),
        obligations: Vec::new(),
        temp_defs: std::collections::BTreeMap::new(),
        activations: Vec::new(),
    };
    let assertion = instr_stmt(&mut state, &query.assertion, &mut Vec::new());

    // Name the local axioms that have no name; keep existing names.
    let mut local: Vec<Decl> = Vec::new();
    let mut local_labels: Vec<String> = Vec::new();
    for decl in query.local.iter() {
        match &**decl {
            DeclX::Axiom(Axiom { named, expr }) => {
                let label = match named {
                    Some(n) => n.to_string(),
                    None => format!("pc%{}%local%{}", query_id, local_labels.len()),
                };
                let site = QuerySiteId::LocalAxiom(local_labels.len() as u32);
                if state.site_tokens.insert(site.clone(), SolverToken::new(label.clone())).is_some()
                {
                    state.identity_error =
                        Some(format!("duplicate query-local instrumentation site: {:?}", site));
                }
                local_labels.push(label.clone());
                local.push(Arc::new(DeclX::Axiom(Axiom {
                    named: Some(Arc::new(label)),
                    expr: expr.clone(),
                })));
            }
            _ => local.push(decl.clone()),
        }
    }

    // The equalities SSA will generate, from the pass's own trace over the
    // guarded clone: mint one activation per equality, at the `Assign`
    // statement's site or at a join's `Reconciliation` site.
    let structured =
        Arc::new(QueryX { local: Arc::new(local.clone()), assertion: assertion.clone() });
    let mut ssa_plan = Vec::new();
    match ssa_sites(&structured) {
        Ok(sites) => {
            for (kind, site) in sites {
                let (z, _) = state.activation(site);
                let ExprX::Var(z) = &*z else { unreachable!("activation is a variable") };
                ssa_plan.push(SsaStep { kind, z: Some(z.to_string()) });
            }
        }
        Err(error) => state.identity_error = Some(error),
    }

    // Declare activation constants and assert them as named unit axioms.
    local.extend(state.decls);

    Instrumented {
        query: Arc::new(QueryX { local: Arc::new(local), assertion }),
        site_tokens: state.site_tokens,
        identity_error: state.identity_error,
        local_labels,
        obligations: state.obligations,
        temp_defs: state.temp_defs,
        activations: state.activations,
        site_z: state.site_z,
        ssa_plan,
    }
}

struct InstrState {
    query_id: u64,
    counter: u64,
    site_tokens: BTreeMap<QuerySiteId, SolverToken>,
    site_z: BTreeMap<QuerySiteId, String>,
    identity_error: Option<String>,
    decls: Vec<Decl>,
    obligations: Vec<ObligationSite>,
    temp_defs: std::collections::BTreeMap<String, Expr>,
    activations: Vec<(String, String)>,
}

impl InstrState {
    /// Mint an activation: declare the constant, assert it as a named unit
    /// axiom, record the label, return the constant as an expression.
    fn activation(&mut self, site: QuerySiteId) -> (Expr, SolverToken) {
        let label = format!("pc%{}%{}", self.query_id, self.counter);
        let z_name = format!("pc_z%{}%{}", self.query_id, self.counter);
        self.counter += 1;
        let z = Arc::new(z_name);
        self.decls.push(Arc::new(DeclX::Const(z.clone(), air::ast_util::bool_typ())));
        self.decls.push(Arc::new(DeclX::Axiom(Axiom {
            named: Some(Arc::new(label.clone())),
            expr: air::ast_util::ident_var(&z),
        })));
        let token = SolverToken::new(label.clone());
        if self.site_tokens.insert(site.clone(), token.clone()).is_some() {
            self.identity_error =
                Some(format!("duplicate statement instrumentation site: {:?}", site));
        }
        self.site_z.insert(site, (*z).clone());
        self.activations.push(((*z).clone(), label));
        (air::ast_util::ident_var(&z), token)
    }
}

fn instr_stmt(state: &mut InstrState, stmt: &Stmt, path: &mut Vec<String>) -> Stmt {
    match &**stmt {
        StmtX::Assume(expr) => {
            // Record lowering-temporary definitions (`tmp%n = rhs`) so
            // decomposition can inline through the lazy-&& encoding.
            if let ExprX::Binary(BinaryOp::Eq, lhs, rhs) = &**expr {
                if let ExprX::Var(name) = &**lhs {
                    if name.starts_with(vir::def::PREFIX_TEMP_VAR) {
                        state.temp_defs.insert(name.to_string(), rhs.clone());
                    }
                }
            }
            let (z, _) = state.activation(QuerySiteId::Statement(path.join(".")));
            Arc::new(StmtX::Assume(air::ast_util::mk_implies(&z, expr)))
        }
        StmtX::Assert(_assert_id, msg, filter, expr) => {
            let (z, batch_token) = state.activation(QuerySiteId::Statement(path.join(".")));
            // Plant a shadow-only assert id so `air::focus` can locate this
            // obligation when building focused queries. The canonical query
            // is untouched; original ids are irrelevant inside the shadow.
            let shadow_assert_id: AssertId =
                Arc::new(vec![u64::MAX, state.obligations.len() as u64]);
            state.obligations.push(ObligationSite {
                batch_label: batch_token.into_string(),
                path: path.join("."),
                shadow_assert_id: shadow_assert_id.clone(),
                original: expr.clone(),
                msg: msg.clone(),
                filter: filter.clone(),
            });
            Arc::new(StmtX::Assert(
                Some(shadow_assert_id),
                msg.clone(),
                filter.clone(),
                air::ast_util::mk_and(&vec![z, expr.clone()]),
            ))
        }
        StmtX::Block(stmts) => {
            let mut out = Vec::with_capacity(stmts.len());
            for (i, stmt) in stmts.iter().enumerate() {
                path.push(format!("b{}", i));
                out.push(instr_stmt(state, stmt, path));
                path.pop();
            }
            Arc::new(StmtX::Block(Arc::new(out)))
        }
        StmtX::Switch(stmts) => {
            let mut out = Vec::with_capacity(stmts.len());
            for (i, stmt) in stmts.iter().enumerate() {
                path.push(format!("s{}", i));
                out.push(instr_stmt(state, stmt, path));
                path.pop();
            }
            Arc::new(StmtX::Switch(Arc::new(out)))
        }
        StmtX::DeadEnd(s) => {
            path.push("d".to_string());
            let inner = instr_stmt(state, s, path);
            path.pop();
            Arc::new(StmtX::DeadEnd(inner))
        }
        StmtX::Breakable(label, s) => {
            path.push("k".to_string());
            let inner = instr_stmt(state, s, path);
            path.pop();
            Arc::new(StmtX::Breakable(label.clone(), inner))
        }
        // Assignments stay as written: their equality is born in the SSA pass
        // and guarded there (`apply_ssa_plan`).
        StmtX::Assign(..) => stmt.clone(),
        StmtX::Havoc(..) | StmtX::Snapshot(..) | StmtX::Break(..) => stmt.clone(),
    }
}

/// Terminal decomposition (`overview.tex` §query-level-coverage): split a
/// formula into conjuncts such that the formula is equivalent to their
/// conjunction. Descends conjunctions; descends implication consequents
/// retaining the antecedent; descends `forall` and `let` bodies retaining the
/// binder; never splits disjunctions. Returns `(structural_path, terminal)`
/// pairs; a formula with no applicable rule is its own single terminal.
pub fn decompose(
    expr: &Expr,
    temp_defs: &std::collections::BTreeMap<String, Expr>,
) -> Vec<(String, Expr)> {
    let mut out = Vec::new();
    decompose_rec(expr, temp_defs, &mut Vec::new(), &mut out, 0);
    out
}

fn decompose_rec(
    expr: &Expr,
    temp_defs: &std::collections::BTreeMap<String, Expr>,
    path: &mut Vec<String>,
    out: &mut Vec<(String, Expr)>,
    depth: u32,
) {
    // Inline lowering temporaries: `assert tmp%n` decomposes as its
    // definition (the defining equality assume stays in the prefix, so the
    // substitution is justified). Depth-capped for safety.
    if depth < 16 {
        if let ExprX::Var(name) = &**expr {
            if let Some(def) = temp_defs.get(name.as_str()) {
                return decompose_rec(def, temp_defs, path, out, depth + 1);
            }
        }
    }
    match &**expr {
        ExprX::Multi(MultiOp::And, exprs) if exprs.len() >= 2 => {
            for (i, e) in exprs.iter().enumerate() {
                path.push(format!("a{}", i));
                decompose_rec(e, temp_defs, path, out, depth);
                path.pop();
            }
        }
        ExprX::Binary(BinaryOp::Implies, antecedent, consequent) => {
            let mut inner = Vec::new();
            path.push("i".to_string());
            decompose_rec(consequent, temp_defs, path, &mut inner, depth);
            path.pop();
            if inner.len() <= 1 {
                out.push((path.join("."), expr.clone()));
            } else {
                for (p, term) in inner {
                    out.push((
                        p,
                        Arc::new(ExprX::Binary(BinaryOp::Implies, antecedent.clone(), term)),
                    ));
                }
            }
        }
        ExprX::Bind(bind, body) => {
            let descend =
                matches!(&**bind, BindX::Quant(air::ast::Quant::Forall, ..) | BindX::Let(..));
            if descend {
                let mut inner = Vec::new();
                path.push("q".to_string());
                decompose_rec(body, temp_defs, path, &mut inner, depth);
                path.pop();
                if inner.len() <= 1 {
                    out.push((path.join("."), expr.clone()));
                } else {
                    for (p, term) in inner {
                        out.push((p, Arc::new(ExprX::Bind(bind.clone(), term))));
                    }
                }
            } else {
                out.push((path.join("."), expr.clone()));
            }
        }
        _ => out.push((path.join("."), expr.clone())),
    }
}

/// A focused query for one terminal of one obligation.
pub struct FocusedQuery {
    pub query: Query,
    /// Batch activation label of the parent obligation.
    pub parent_label: String,
    /// Fresh activation label of the terminal target.
    pub target_label: String,
    /// Structural path of the terminal within the parent obligation formula.
    pub terminal_path: String,
    /// Labels available to this query: the activations surviving in the
    /// focused prefix plus every query-local axiom label. This is the
    /// per-obligation premise scope `I_{q,j}` of the formalization — what
    /// separates "never in scope" from "in scope but unused".
    pub available: Vec<String>,
    /// The post-SSA guard plan of this focused query.
    pub ssa_plan: Vec<SsaStep>,
}

/// Build one focused query per terminal of every obligation in the
/// instrumented query. Prefix retention is `air::focus` (assumes and
/// statements before the target kept, only the containing switch arm kept,
/// later assertions dropped, DeadEnd/Breakable structure preserved); the
/// target assert is then replaced by `z_t && terminal` with a fresh labeled
/// activation.
pub fn focused_queries(query_id: u64, instrumented: &Instrumented) -> Vec<FocusedQuery> {
    let mut out = Vec::new();
    for (ob_idx, site) in instrumented.obligations.iter().enumerate() {
        let (prefix, found) = focus_in_place(&instrumented.query.assertion, &site.shadow_assert_id);
        assert!(
            found,
            "proof-coverage: focused-query construction lost batch obligation {}",
            site.batch_label
        );
        let terminals = decompose(&site.original, &instrumented.temp_defs);
        assert!(
            !terminals.is_empty(),
            "proof-coverage: terminal decomposition produced no child for batch obligation {}",
            site.batch_label
        );
        for (t_idx, (terminal_path, terminal)) in terminals.into_iter().enumerate() {
            let target_label = format!("pc%{}%t%{}%{}", query_id, ob_idx, t_idx);
            let z_name = format!("pc_zt%{}%{}%{}", query_id, ob_idx, t_idx);
            let z = Arc::new(z_name);
            // Every activation stays declared: dropping declarations for
            // statements the focus removed would leave dangling references in
            // surviving formulas. Out-of-scope labels that a (non-minimal) Z3
            // core may still return are filtered by consumers against
            // `available`, never by mutating the query.
            let mut local: Vec<Decl> = (*instrumented.query.local).clone();
            local.push(Arc::new(DeclX::Const(z.clone(), air::ast_util::bool_typ())));
            local.push(Arc::new(DeclX::Axiom(Axiom {
                named: Some(Arc::new(target_label.clone())),
                expr: air::ast_util::ident_var(&z),
            })));
            let target_assert = Arc::new(StmtX::Assert(
                None,
                site.msg.clone(),
                site.filter.clone(),
                air::ast_util::mk_and(&vec![air::ast_util::ident_var(&z), terminal.clone()]),
            ));
            let assertion = replace_assert_by_id(&prefix, &site.shadow_assert_id, &target_assert);
            // The per-obligation premise scope `I_{q,j}`: exactly the
            // activations occurring in the query as discharged (after the
            // target assert is replaced, so the parent obligation's own
            // activation is gone), plus the query-local axioms.
            let mut available: Vec<String> = instrumented
                .activations
                .iter()
                .filter(|(z, _)| stmt_mentions_var(&assertion, z))
                .map(|(_, label)| label.clone())
                .collect();
            available.extend(instrumented.local_labels.iter().cloned());
            available.push(target_label.clone());
            // SSA-generated equalities of the focused query: those whose site
            // the batch minted are guarded with the batch's constant, and are
            // in scope unless they reconcile a join that *encloses* the
            // focus — those lie after the target and are unguarded.
            let focused = Arc::new(QueryX { local: Arc::new(local), assertion });
            let ssa_plan = match ssa_sites(&focused) {
                Ok(sites) => sites
                    .into_iter()
                    .map(|(kind, ssa_site)| {
                        let encloses = match &ssa_site {
                            QuerySiteId::Reconciliation { at, .. } => {
                                site.path == *at || site.path.starts_with(&format!("{at}."))
                            }
                            _ => false,
                        };
                        let z = if encloses {
                            None
                        } else {
                            instrumented.site_z.get(&ssa_site).cloned()
                        };
                        if z.is_some() {
                            if let Some(token) = instrumented.site_tokens.get(&ssa_site) {
                                available.push(token.as_str().to_string());
                            }
                        }
                        SsaStep { kind, z }
                    })
                    .collect(),
                Err(error) => panic!("proof-coverage: focused query SSA trace: {error}"),
            };
            available.sort();
            available.dedup();
            out.push(FocusedQuery {
                query: focused,
                parent_label: site.batch_label.clone(),
                target_label,
                terminal_path,
                available,
                ssa_plan,
            });
        }
    }
    out
}

/// Focus a structured query on one obligation, preserving the tree's
/// structure so that statement paths — and with them the SSA trace's
/// coordinates — stay those of the batch query. Equivalent to
/// `air::focus::focus_stmt_on_assert_id`: statements after the target and
/// non-target asserts become empty blocks in place; the other arms of every
/// enclosing `Switch` become `assume false` instead of being dropped.
fn focus_in_place(stmt: &Stmt, id: &AssertId) -> (Stmt, bool) {
    let empty = || Arc::new(StmtX::Block(Arc::new(vec![])));
    match &**stmt {
        StmtX::Assert(Some(aid), ..) if aid == id => (stmt.clone(), true),
        StmtX::Assert(..) => (empty(), false),
        StmtX::Assume(..)
        | StmtX::Havoc(..)
        | StmtX::Assign(..)
        | StmtX::Snapshot(..)
        | StmtX::Break(..) => (stmt.clone(), false),
        StmtX::DeadEnd(s) => {
            let (s, found) = focus_in_place(s, id);
            if found { (Arc::new(StmtX::DeadEnd(s)), true) } else { (empty(), false) }
        }
        StmtX::Breakable(label, s) => {
            let (s, found) = focus_in_place(s, id);
            (Arc::new(StmtX::Breakable(label.clone(), s)), found)
        }
        StmtX::Block(stmts) => {
            let mut out = Vec::with_capacity(stmts.len());
            let mut found = false;
            for s in stmts.iter() {
                if found {
                    out.push(empty());
                } else {
                    let (s, f) = focus_in_place(s, id);
                    out.push(s);
                    found = f;
                }
            }
            (Arc::new(StmtX::Block(Arc::new(out))), found)
        }
        StmtX::Switch(stmts) => {
            let arms: Vec<(Stmt, bool)> = stmts.iter().map(|s| focus_in_place(s, id)).collect();
            let found = arms.iter().any(|(_, f)| *f);
            let out: Vec<Stmt> = arms
                .into_iter()
                .map(|(s, f)| {
                    if found && !f { Arc::new(StmtX::Assume(air::ast_util::mk_false())) } else { s }
                })
                .collect();
            (Arc::new(StmtX::Switch(Arc::new(out))), found)
        }
    }
}

/// Replace the (unique) assert carrying `id` with `replacement`.
fn replace_assert_by_id(stmt: &Stmt, id: &AssertId, replacement: &Stmt) -> Stmt {
    match &**stmt {
        StmtX::Assert(Some(aid), ..) if aid == id => replacement.clone(),
        StmtX::Block(stmts) => Arc::new(StmtX::Block(Arc::new(
            stmts.iter().map(|s| replace_assert_by_id(s, id, replacement)).collect(),
        ))),
        StmtX::Switch(stmts) => Arc::new(StmtX::Switch(Arc::new(
            stmts.iter().map(|s| replace_assert_by_id(s, id, replacement)).collect(),
        ))),
        StmtX::DeadEnd(s) => Arc::new(StmtX::DeadEnd(replace_assert_by_id(s, id, replacement))),
        StmtX::Breakable(label, s) => {
            Arc::new(StmtX::Breakable(label.clone(), replace_assert_by_id(s, id, replacement)))
        }
        _ => stmt.clone(),
    }
}

#[cfg(test)]
mod focus_invariant_tests {
    use super::*;
    use air::ast::{BinaryOp, Constant, ExprX};

    fn int_typ() -> air::ast::Typ {
        Arc::new(air::ast::TypX::Int)
    }
    fn int(n: u32) -> Expr {
        Arc::new(ExprX::Const(Constant::Nat(Arc::new(n.to_string()))))
    }
    fn var(x: &str) -> Expr {
        air::ast_util::string_var(&x.to_string())
    }

    /// `x` declared; `Block[ Assign x=1; Switch[ Assign x=2 ; Assume true ]; Assert x>0 ]`.
    /// The SSA pass generates: the two assignment equalities and one
    /// reconciliation for the switch arm that did not assign (`x@2 == x@1`).
    fn mutation_query() -> Query {
        let x = Arc::new("x".to_string());
        let assertion = Arc::new(StmtX::Block(Arc::new(vec![
            Arc::new(StmtX::Assign(x.clone(), int(1))),
            Arc::new(StmtX::Switch(Arc::new(vec![
                Arc::new(StmtX::Assign(x.clone(), int(2))),
                Arc::new(StmtX::Assume(air::ast_util::mk_true())),
            ]))),
            Arc::new(StmtX::Assert(
                None,
                Arc::new(()),
                None,
                Arc::new(ExprX::Binary(BinaryOp::Gt, var("x"), int(0))),
            )),
        ])));
        Arc::new(QueryX { local: Arc::new(vec![Arc::new(DeclX::Var(x, int_typ()))]), assertion })
    }

    /// The SSA trace names each generated equality by the statement it came
    /// from; assignments keep their statement site, reconciliations get a
    /// join site. Every one has an activation, and the plan lists them in
    /// generation order.
    #[test]
    fn ssa_trace_names_assignment_and_reconciliation_sites() {
        let instrumented = instrument_query(3, &mutation_query());
        assert_eq!(instrumented.identity_error, None);
        let sites: Vec<&QuerySiteId> = instrumented.site_tokens.keys().collect();
        assert!(sites.contains(&&QuerySiteId::Statement("b0".to_string())), "{sites:?}");
        assert!(sites.contains(&&QuerySiteId::Statement("b1.s0".to_string())), "{sites:?}");
        let reconciliation = QuerySiteId::Reconciliation {
            at: "b1".to_string(),
            join: SsaJoin::SwitchArm(1),
            var: "x".to_string(),
            from: 1,
            to: 2,
        };
        assert!(sites.contains(&&reconciliation), "{sites:?}");
        assert_eq!(
            instrumented.ssa_plan.iter().map(|s| s.kind.clone()).collect::<Vec<_>>(),
            vec![
                SsaKind::Assign,
                SsaKind::Assign,
                SsaKind::Reconcile {
                    join: SsaJoin::SwitchArm(1),
                    var: "x".to_string(),
                    from: 1,
                    to: 2
                },
            ]
        );
        assert!(instrumented.ssa_plan.iter().all(|s| s.z.is_some()));
        // The clone's statements are the canonical ones plus guards: no
        // temporaries, no havocs.
        assert!(!stmt_mentions_var(&instrumented.query.assertion, "pc_t%3%0"));
    }

    /// The hook guards exactly the traced equalities, in place, and refuses a
    /// trace that disagrees with the plan.
    #[test]
    fn plan_guards_traced_equalities_and_rejects_disagreement() {
        let instrumented = instrument_query(4, &mutation_query());
        let (lowered, _, _, trace) = air::var_to_const::lower_query(&instrumented.query);
        let guarded =
            apply_ssa_plan(&lowered, &trace, &instrumented.ssa_plan).expect("plan applies");
        for step in &instrumented.ssa_plan {
            assert!(stmt_mentions_var(&guarded.assertion, step.z.as_ref().unwrap()));
        }
        let mut wrong = instrumented.ssa_plan.clone();
        wrong.pop();
        assert!(apply_ssa_plan(&lowered, &trace, &wrong).is_err());
        let mut wrong = instrumented.ssa_plan.clone();
        wrong[0].kind =
            SsaKind::Reconcile { join: SsaJoin::Break, var: "x".to_string(), from: 0, to: 1 };
        assert!(apply_ssa_plan(&lowered, &trace, &wrong).is_err());
    }

    /// Focusing preserves the tree, so a focused query's SSA trace lands on
    /// the batch's sites: the assignments before the target are guarded with
    /// the batch constants and in scope; the switch reconciliation precedes
    /// the target and is in scope too.
    #[test]
    fn focused_queries_share_the_batch_ssa_sites() {
        let instrumented = instrument_query(5, &mutation_query());
        let focused = focused_queries(5, &instrumented);
        assert_eq!(focused.len(), 1);
        let fq = &focused[0];
        assert_eq!(fq.ssa_plan.len(), 3);
        assert!(fq.ssa_plan.iter().all(|s| s.z.is_some()), "{:?}", fq.ssa_plan);
        for site in instrumented.site_tokens.keys() {
            if matches!(site, QuerySiteId::Reconciliation { .. }) {
                assert!(
                    fq.available.contains(&instrumented.site_tokens[site].as_str().to_string())
                );
            }
        }
    }

    /// A reconciliation of a join that encloses the target lies after it: it
    /// stays unguarded in the focused query and out of its scope.
    #[test]
    fn enclosing_join_reconciliation_is_out_of_scope() {
        let x = Arc::new("x".to_string());
        // Block[ Assign x=1; Switch[ Block[Assign x=2; Assert x>0] ; Assume true ] ]
        let assertion = Arc::new(StmtX::Block(Arc::new(vec![
            Arc::new(StmtX::Assign(x.clone(), int(1))),
            Arc::new(StmtX::Switch(Arc::new(vec![
                Arc::new(StmtX::Block(Arc::new(vec![
                    Arc::new(StmtX::Assign(x.clone(), int(2))),
                    Arc::new(StmtX::Assert(
                        None,
                        Arc::new(()),
                        None,
                        Arc::new(ExprX::Binary(BinaryOp::Gt, var("x"), int(0))),
                    )),
                ]))),
                Arc::new(StmtX::Assume(air::ast_util::mk_true())),
            ]))),
        ])));
        let query = Arc::new(QueryX {
            local: Arc::new(vec![Arc::new(DeclX::Var(x, int_typ()))]),
            assertion,
        });
        let instrumented = instrument_query(6, &query);
        let focused = focused_queries(6, &instrumented);
        let fq = &focused[0];
        let reconciliations: Vec<&SsaStep> =
            fq.ssa_plan.iter().filter(|s| matches!(s.kind, SsaKind::Reconcile { .. })).collect();
        assert_eq!(reconciliations.len(), 1);
        assert_eq!(reconciliations[0].z, None);
        for site in instrumented.site_tokens.keys() {
            if matches!(site, QuerySiteId::Reconciliation { .. }) {
                assert!(
                    !fq.available.contains(&instrumented.site_tokens[site].as_str().to_string())
                );
            }
        }
    }

    #[test]
    #[should_panic(expected = "focused-query construction lost batch obligation")]
    fn focused_query_construction_rejects_a_missing_instrumented_obligation() {
        let assertion = Arc::new(StmtX::Assert(None, Arc::new(()), None, air::ast_util::mk_true()));
        let query = Arc::new(QueryX { local: Arc::new(Vec::new()), assertion });
        let mut instrumented = instrument_query(7, &query);
        assert_eq!(instrumented.obligations.len(), 1);

        instrumented.obligations[0].shadow_assert_id = Arc::new(vec![u64::MAX, 99]);
        let _ = focused_queries(7, &instrumented);
    }
}

/// Does `stmt` mention the variable `name` anywhere in any formula?
/// A structural occurrence test, deliberately shape-agnostic: air's
/// constructors simplify, so an activation can appear as `z => P`, `¬z`, a
/// conjunct, or nested arbitrarily deep.
fn stmt_mentions_var(stmt: &Stmt, name: &str) -> bool {
    match &**stmt {
        StmtX::Assume(expr) => expr_mentions_var(expr, name),
        StmtX::Assert(_, _, _, expr) => expr_mentions_var(expr, name),
        StmtX::Assign(_, expr) => expr_mentions_var(expr, name),
        StmtX::Block(stmts) | StmtX::Switch(stmts) => {
            stmts.iter().any(|s| stmt_mentions_var(s, name))
        }
        StmtX::DeadEnd(s) | StmtX::Breakable(_, s) => stmt_mentions_var(s, name),
        StmtX::Havoc(..) | StmtX::Snapshot(..) | StmtX::Break(..) => false,
    }
}

fn expr_mentions_var(expr: &Expr, name: &str) -> bool {
    match &**expr {
        ExprX::Var(x) | ExprX::Old(_, x) => &**x == name,
        ExprX::Const(_) => false,
        ExprX::Apply(_, args) | ExprX::Array(args) => {
            args.iter().any(|a| expr_mentions_var(a, name))
        }
        ExprX::ApplyFun(_, f, args) => {
            expr_mentions_var(f, name) || args.iter().any(|a| expr_mentions_var(a, name))
        }
        ExprX::Unary(_, e) => expr_mentions_var(e, name),
        ExprX::Binary(_, a, b) => expr_mentions_var(a, name) || expr_mentions_var(b, name),
        ExprX::Multi(_, exprs) => exprs.iter().any(|e| expr_mentions_var(e, name)),
        ExprX::IfElse(a, b, d) => {
            expr_mentions_var(a, name) || expr_mentions_var(b, name) || expr_mentions_var(d, name)
        }
        ExprX::Bind(bind, e) => {
            let in_bind = match &**bind {
                air::ast::BindX::Let(binders) => {
                    binders.iter().any(|b| expr_mentions_var(&b.a, name))
                }
                air::ast::BindX::Choose(_, _, _, cond) => expr_mentions_var(cond, name),
                _ => false,
            };
            in_bind || expr_mentions_var(e, name)
        }
        ExprX::LabeledAxiom(_, _, e) | ExprX::LabeledAssertion(_, _, _, e) => {
            expr_mentions_var(e, name)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use air::ast::{Constant, ExprX};

    fn config(options: &[(&str, &str)]) -> SolverReplayConfig {
        SolverReplayConfig {
            solver: SmtSolver::Z3,
            option_history: options
                .iter()
                .map(|(option, value)| ((*option).to_string(), (*value).to_string()))
                .collect(),
            rlimit: 30_000_000,
            single_check_query: false,
            ignore_unexpected_smt: false,
            debug: false,
            expected_solver_version: Some("4.16.0".to_string()),
        }
    }

    #[test]
    fn replay_configuration_advances_only_by_ordered_prefix() {
        let base = config(&[("air_recommended_options", "true")]);
        let mut replay = ReplayContext::new(&base, false, false, None).unwrap();

        let extended = config(&[("air_recommended_options", "true"), ("smt.arith.solver", "6")]);
        assert!(replay.apply(&extended).is_ok());

        let reordered = config(&[("smt.arith.solver", "6"), ("air_recommended_options", "true")]);
        assert_eq!(replay.apply(&reordered), Err("config_mismatch"));
    }

    #[test]
    fn unsupported_solver_is_never_replayed_as_z3() {
        let mut cvc5 = config(&[]);
        cvc5.solver = SmtSolver::Cvc5;
        assert!(matches!(
            ReplayContext::new(&cvc5, false, false, None),
            Err("unsupported_solver")
        ));
    }

    #[test]
    fn instrumentation_joins_tokens_to_typed_structural_sites() {
        let truth = Arc::new(ExprX::Const(Constant::Bool(true)));
        let query = Arc::new(QueryX {
            local: Arc::new(vec![
                Arc::new(DeclX::Axiom(Axiom { named: None, expr: truth.clone() })),
                Arc::new(DeclX::Axiom(Axiom {
                    named: Some(Arc::new("existing-local".to_string())),
                    expr: truth.clone(),
                })),
            ]),
            assertion: Arc::new(StmtX::Block(Arc::new(vec![
                Arc::new(StmtX::Assume(truth.clone())),
                Arc::new(StmtX::Switch(Arc::new(vec![
                    Arc::new(StmtX::Assume(truth.clone())),
                    Arc::new(StmtX::Block(Arc::new(vec![Arc::new(StmtX::Assume(truth.clone()))]))),
                ]))),
            ]))),
        });

        let instrumented = instrument_query(9, &query);
        assert_eq!(instrumented.identity_error, None);
        assert_eq!(
            instrumented.site_tokens[&QuerySiteId::Statement("b0".to_string())].as_str(),
            "pc%9%0"
        );
        assert_eq!(
            instrumented.site_tokens[&QuerySiteId::Statement("b1.s0".to_string())].as_str(),
            "pc%9%1"
        );
        assert_eq!(
            instrumented.site_tokens[&QuerySiteId::Statement("b1.s1.b0".to_string())].as_str(),
            "pc%9%2"
        );
        assert_eq!(instrumented.site_tokens[&QuerySiteId::LocalAxiom(0)].as_str(), "pc%9%local%0");
        assert_eq!(
            instrumented.site_tokens[&QuerySiteId::LocalAxiom(1)].as_str(),
            "existing-local"
        );
    }
}
