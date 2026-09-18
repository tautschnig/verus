use crate::ast::{
    AssertId, AxiomInfoFilter, Command, CommandX, Decl, Ident, Query, Typ, TypeError, Typs,
};
use crate::closure::ClosureTerm;
use crate::emitter::Emitter;
use crate::messages::{ArcDynMessage, Diagnostics};
use crate::model::Model;
use crate::node;
use crate::printer::{macro_push_node, str_to_node};

use crate::scope_map::ScopeMap;
use crate::smt_process::SmtProcess;
use crate::smt_verify::ReportLongRunning;
use crate::solver_set::{CrossCheckPolicy, SecondaryChannel, SecondaryRegistry, SolverVerdict};
use crate::typecheck::Typing;
use sise::TreeNode as Node;
use std::any::Any;
use std::collections::HashSet;
use std::sync::Arc;
use std::time::Duration;

#[derive(Clone, Debug)]
pub(crate) struct AssertionInfo {
    pub(crate) assert_id: Option<crate::ast::AssertId>,
    pub(crate) error: ArcDynMessage,
    pub(crate) label: Ident,
    pub(crate) filter: AxiomInfoFilter,
    pub(crate) decl: Decl,
    pub(crate) disabled: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct AxiomInfo {
    pub(crate) labels: Vec<Arc<dyn Any + Send + Sync>>,
    pub(crate) label: Ident,
    pub(crate) filter: AxiomInfoFilter,
    pub(crate) decl: Decl,
}

#[derive(Debug)]
pub enum UsageInfo {
    None,
    UsedAxioms(Vec<Ident>),
}

#[derive(Debug)]
pub enum ValidityResult {
    Valid(UsageInfo),
    Invalid(Option<Model>, Option<ArcDynMessage>, Option<AssertId>),
    Canceled,
    TypeError(TypeError),
    UnexpectedOutput(String),
}

#[derive(Clone, Debug)]
pub(crate) enum ContextState {
    NotStarted,
    ReadyForQuery,
    FoundResult,
    FoundInvalid(Vec<AssertionInfo>, Option<Model>),
    Canceled,
    NoMoreQueriesAllowed,
}

pub struct QueryContext<'a, 'b: 'a> {
    pub report_long_running: Option<&'a mut ReportLongRunning<'b>>,
}

impl<'a, 'b: 'a> Default for QueryContext<'a, 'b> {
    fn default() -> Self {
        QueryContext { report_long_running: None }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum SmtSolver {
    Z3,
    Cvc5,
}

impl Default for SmtSolver {
    fn default() -> Self {
        SmtSolver::Z3
    }
}

impl SmtSolver {
    /// Name of the solver, for use in user-facing diagnostics.
    pub fn name(&self) -> &'static str {
        match self {
            SmtSolver::Z3 => "z3",
            SmtSolver::Cvc5 => "cvc5",
        }
    }
}

pub struct Context {
    pub(crate) message_interface: Arc<dyn crate::messages::MessageInterface>,
    smt_process: Option<SmtProcess>,
    pub(crate) axiom_infos: ScopeMap<Ident, Arc<AxiomInfo>>,
    pub(crate) axiom_infos_count: u64,
    pub(crate) array_map: ScopeMap<ClosureTerm, Ident>,
    pub(crate) array_count: u64,
    pub(crate) lambda_map: ScopeMap<ClosureTerm, Ident>,
    pub(crate) lambda_count: u64,
    pub(crate) choose_map: ScopeMap<ClosureTerm, Ident>,
    pub(crate) choose_count: u64,
    pub(crate) apply_map: ScopeMap<(Typs, Typ), Ident>,
    pub(crate) apply_count: u64,
    pub(crate) typing: Typing,
    pub(crate) debug: bool,
    pub(crate) ignore_unexpected_smt: bool,
    pub(crate) rlimit: u32,
    pub(crate) air_initial_log: Emitter,
    pub(crate) air_middle_log: Emitter,
    pub(crate) air_final_log: Emitter,
    pub(crate) smt_log: Emitter,
    pub(crate) smt_transcript_log: Option<Box<dyn std::io::Write>>,
    pub(crate) time_smt_init: Duration,
    pub(crate) time_smt_run: Duration,
    pub(crate) rlimit_count: Option<(u64, u64)>,
    pub(crate) state: ContextState,
    pub(crate) expected_solver_version: Option<String>,
    pub(crate) profile_logfile_name: Option<String>,
    pub(crate) single_check_query: bool,
    pub(crate) usage_info_enabled: bool,
    pub(crate) check_valid_used: bool,
    pub(crate) solver: SmtSolver,
    // Cross-checking (design 05 §2): a cvc5 secondary running the identical solver-neutral
    // stream alongside the Z3 primary. The secondary now runs DETACHED on a background worker
    // thread (see solver_set::SecondaryRegistry) so the slower cvc5 solve is off the critical
    // path; the primary's verdict is reported immediately and reconciliation happens when the
    // secondary answers, joined at crate end.
    pub(crate) cross_check: CrossCheckPolicy,
    /// Shared crate-level coordinator for all detached secondary workers (permit semaphore,
    /// outstanding-job accounting, collected outcomes). `None` when cross-check is off.
    cross_check_registry: Option<Arc<SecondaryRegistry>>,
    /// This context's handle to its own detached secondary worker (lazily created on the
    /// first fanned command). Dropping it lets the worker drain and exit.
    secondary: Option<SecondaryChannel>,
    /// Z3-specific options that must reach the primary process but never the shared stream.
    cross_check_primary_startup: Vec<u8>,
    /// cvc5-specific options (logic, incremental) that must reach the secondary process only.
    cross_check_secondary_startup: Vec<u8>,
    /// Friendly name of the function whose queries are currently running, for diagnostics.
    cross_check_function: Option<String>,
    /// Per-context monotonic query id, tagged onto each secondary check-sat job.
    cross_check_query_counter: u64,
}

impl Context {
    pub fn new(
        message_interface: Arc<dyn crate::messages::MessageInterface>,
        solver: SmtSolver,
    ) -> Self {
        let mut context = Context {
            message_interface: message_interface.clone(),
            smt_process: None,
            axiom_infos: ScopeMap::new(),
            axiom_infos_count: 0,
            array_map: ScopeMap::new(),
            array_count: 0,
            lambda_map: ScopeMap::new(),
            lambda_count: 0,
            choose_map: ScopeMap::new(),
            choose_count: 0,
            apply_map: ScopeMap::new(),
            apply_count: 0,
            typing: Typing {
                message_interface: message_interface.clone(),
                decls: crate::scope_map::ScopeMap::new(),
                snapshots: HashSet::new(),
                break_labels_local: HashSet::new(),
                break_labels_in_scope: crate::scope_map::ScopeMap::new(),
                solver: solver.clone(),
            },
            debug: false,
            ignore_unexpected_smt: false,
            rlimit: 0,
            air_initial_log: Emitter::new(
                message_interface.clone(),
                false,
                false,
                None,
                solver.clone(),
            ),
            air_middle_log: Emitter::new(
                message_interface.clone(),
                false,
                false,
                None,
                solver.clone(),
            ),
            air_final_log: Emitter::new(
                message_interface.clone(),
                false,
                false,
                None,
                solver.clone(),
            ),
            smt_log: Emitter::new(message_interface.clone(), true, true, None, solver.clone()),
            smt_transcript_log: None,
            time_smt_init: Duration::new(0, 0),
            time_smt_run: Duration::new(0, 0),
            rlimit_count: match solver {
                SmtSolver::Z3 => Some((0, 0)),
                SmtSolver::Cvc5 => None,
            },
            state: ContextState::NotStarted,
            expected_solver_version: None,
            profile_logfile_name: None,
            single_check_query: false,
            usage_info_enabled: false,
            check_valid_used: false,
            solver,
            cross_check: CrossCheckPolicy::Off,
            cross_check_registry: None,
            secondary: None,
            cross_check_primary_startup: Vec::new(),
            cross_check_secondary_startup: Vec::new(),
            cross_check_function: None,
            cross_check_query_counter: 0,
        };
        context.axiom_infos.push_scope(false);
        context.array_map.push_scope(false);
        context.lambda_map.push_scope(false);
        context.choose_map.push_scope(false);
        context.apply_map.push_scope(false);
        context.typing.decls.push_scope(false);
        context.typing.break_labels_in_scope.push_scope(false);
        context
    }

    pub fn get_smt_process(&mut self) -> &mut SmtProcess {
        // Only start the smt process if there are queries to run
        if self.smt_process.is_none() {
            let transcript_log = self.smt_transcript_log.take();
            let mut process = SmtProcess::launch(&self.solver, transcript_log);
            // Under cross-check the shared stream is solver-neutral, so the Z3-specific
            // options (recommended tuning) are injected into the primary process directly.
            if self.cross_check != CrossCheckPolicy::Off
                && !self.cross_check_primary_startup.is_empty()
            {
                let startup = std::mem::take(&mut self.cross_check_primary_startup);
                let _ = process.send_commands(startup);
            }
            self.smt_process = Some(process);
        }
        self.smt_process.as_mut().unwrap()
    }

    /// Enable dual-solver cross-checking for this context (design 05 §2, async variant):
    /// register a DETACHED cvc5 secondary (via the shared [`SecondaryRegistry`]) that runs
    /// the identical solver-neutral stream on a background worker. Must be called before the
    /// prelude is emitted so the shared stream is neutral (no `:skolemid`, axiomatised height
    /// prelude via `PreludeConfig`). The worker itself is created lazily on the first fanned
    /// command, once the cvc5-only startup has been accumulated.
    pub fn enable_cross_check(
        &mut self,
        policy: CrossCheckPolicy,
        registry: Arc<SecondaryRegistry>,
    ) {
        self.cross_check = policy;
        self.cross_check_registry = Some(registry);
        // The shared stream fed to both solvers must carry no Z3-only annotations.
        self.smt_log.set_neutral(true);
    }

    pub fn cross_check_enabled(&self) -> bool {
        self.cross_check != CrossCheckPolicy::Off
    }

    /// Record the friendly name of the function whose queries are running, so cross-check
    /// diagnostics can name it.
    pub fn set_cross_check_function(&mut self, name: String) {
        self.cross_check_function = Some(name);
    }

    /// Create this context's detached secondary worker if needed. The worker owns the cvc5
    /// process and services an ordered job queue; the cvc5-only startup (logic, incremental)
    /// accumulated so far is handed to it, and it appends the rlimit-per budget itself.
    fn ensure_secondary(&mut self) {
        if self.cross_check == CrossCheckPolicy::Off || self.secondary.is_some() {
            return;
        }
        let Some(registry) = &self.cross_check_registry else {
            return;
        };
        let startup = self.cross_check_secondary_startup.clone();
        self.secondary = Some(registry.spawn_secondary(startup));
    }

    /// Send a solver-neutral command chunk to the primary and, under cross-check, ENQUEUE it
    /// to the detached secondary worker (which applies it in order to keep incremental state
    /// in lockstep). Returns the primary's lines. Used for stateful flushes (declarations,
    /// the version query); the secondary's response is not a verdict and is ignored.
    pub(crate) fn send_fanned(&mut self, commands: Vec<u8>) -> Vec<String> {
        if self.cross_check == CrossCheckPolicy::Off {
            return self.get_smt_process().send_commands(commands);
        }
        self.get_smt_process();
        self.ensure_secondary();
        if let Some(secondary) = &self.secondary {
            secondary.send_commands(commands.clone());
        }
        self.smt_process.as_mut().unwrap().send_commands(commands)
    }

    /// Run a check-sat on the primary and return its lines IMMEDIATELY, injecting the Z3-only
    /// `primary_prefix` (rlimit) into the primary stream only. Under cross-check the identical
    /// solver-neutral text is ENQUEUED to the detached secondary worker together with the
    /// primary's verdict; reconciliation happens on the worker and is joined at crate end, so
    /// the slower cvc5 solve is off the critical path (design 05 §2.3, async variant).
    pub(crate) fn check_sat_fanned(
        &mut self,
        neutral_commands: Vec<u8>,
        primary_prefix: Vec<u8>,
        report_long_running: Option<&mut ReportLongRunning>,
    ) -> Vec<String> {
        self.get_smt_process();
        self.ensure_secondary();
        let mut primary_data = primary_prefix;
        primary_data.extend_from_slice(&neutral_commands);

        let primary = self.smt_process.as_mut().unwrap();
        let prim_handle = primary.send_commands_async(primary_data);
        let primary_lines = if let Some((report_threshold, report_fn)) = report_long_running {
            let start = std::time::Instant::now();
            match prim_handle.wait_timeout(*report_threshold) {
                Ok(lines) => lines,
                Err(handle) => {
                    report_fn(start.elapsed(), false);
                    let lines = handle.wait();
                    report_fn(start.elapsed(), true);
                    lines
                }
            }
        } else {
            prim_handle.wait()
        };

        if self.secondary.is_some() {
            let query_id = self.cross_check_query_counter;
            self.cross_check_query_counter += 1;
            let verdict = SolverVerdict::from_lines(&primary_lines);
            let func =
                self.cross_check_function.clone().unwrap_or_else(|| "this query".to_string());
            self.secondary.as_ref().unwrap().send_check_sat(
                neutral_commands,
                primary_lines.clone(),
                verdict,
                func,
                query_id,
            );
        }
        primary_lines
    }

    /// Append a raw Z3-only startup option to the primary process's private prefix.
    pub(crate) fn push_primary_startup(&mut self, text: &str) {
        self.cross_check_primary_startup.extend_from_slice(text.as_bytes());
    }

    /// Append a raw cvc5-only startup option to the secondary process's private prefix.
    pub(crate) fn push_secondary_startup(&mut self, text: &str) {
        self.cross_check_secondary_startup.extend_from_slice(text.as_bytes());
    }

    /// Under cross-check, flush any pending shared declarations to the secondary worker, so a
    /// subsequent Z3-only primary-only command (e.g. the `(get-info :all-statistics)`
    /// rlimit-count probe) does not strand the secondary without the declarations the next
    /// check-sat depends on.
    pub(crate) fn flush_shared_pending(&mut self) {
        if self.cross_check == CrossCheckPolicy::Off {
            return;
        }
        let pending = self.smt_log.take_pipe_data();
        if pending.is_empty() {
            return;
        }
        let _ = self.send_fanned(pending);
    }

    pub fn set_air_initial_log(&mut self, writer: Box<dyn std::io::Write>) {
        self.air_initial_log.set_log(Some(writer));
    }

    pub fn set_air_middle_log(&mut self, writer: Box<dyn std::io::Write>) {
        self.air_middle_log.set_log(Some(writer));
    }

    pub fn set_air_final_log(&mut self, writer: Box<dyn std::io::Write>) {
        self.air_final_log.set_log(Some(writer));
    }

    pub fn set_smt_log(&mut self, writer: Box<dyn std::io::Write>) {
        self.smt_log.set_log(Some(writer));
    }

    pub fn set_smt_transcript_log(&mut self, writer: Box<dyn std::io::Write>) {
        if let Some(smt_process) = &mut self.smt_process {
            smt_process.set_transcript_log(writer);
        } else {
            self.smt_transcript_log = Some(writer);
        }
    }

    pub fn set_debug(&mut self, debug: bool) {
        self.debug = debug;
    }

    pub fn get_debug(&self) -> bool {
        self.debug
    }

    pub fn get_solver(&self) -> &SmtSolver {
        &self.solver
    }

    pub fn set_ignore_unexpected_smt(&mut self, ignore_unexpected_smt: bool) {
        self.ignore_unexpected_smt = ignore_unexpected_smt;
    }

    pub fn get_time(&self) -> (Duration, Duration) {
        (self.time_smt_init, self.time_smt_run)
    }

    pub fn get_rlimit_count(&self) -> Option<(u64, u64)> {
        self.rlimit_count
    }

    pub fn set_expected_solver_version(&mut self, version: String) {
        self.expected_solver_version = Some(version);
    }

    pub fn set_profile_with_logfile_name(&mut self, file_name: String) {
        assert!(matches!(self.state, ContextState::NotStarted));
        self.profile_logfile_name = Some(file_name);
    }

    pub fn set_rlimit(&mut self, rlimit: u32) {
        self.rlimit = rlimit;
        self.air_initial_log.log_set_option("rlimit", &rlimit.to_string());
        self.air_middle_log.log_set_option("rlimit", &rlimit.to_string());
        self.air_final_log.log_set_option("rlimit", &rlimit.to_string());
        if matches!(self.solver, SmtSolver::Cvc5) {
            if matches!(self.state, ContextState::NotStarted) {
                // cvc5 only allows a single upfront rlimit declaration;
                // Using rlimit-per configures a fixed budget for each check-sat query,
                // rather than for the entire session's worth of queries.
                self.smt_log.log_set_option("rlimit-per", &rlimit.to_string());
            }
        }
    }

    /// Can the rlimit be adjusted for each check-sat query?
    pub fn rlimit_is_mutable(&self) -> bool {
        match self.solver {
            SmtSolver::Z3 => true,
            SmtSolver::Cvc5 => matches!(self.state, ContextState::NotStarted),
        }
    }

    pub fn set_single_check_query(&mut self) {
        self.single_check_query = true;
        self.air_initial_log.log_set_option("single_check_query", "true");
        self.air_middle_log.log_set_option("single_check_query", "true");
        self.air_final_log.log_set_option("single_check_query", "true");
    }

    pub fn enable_usage_info(&mut self) {
        assert!(matches!(self.state, ContextState::NotStarted));
        self.usage_info_enabled = true;
        self.set_solver_option_bool("produce-unsat-cores", true, true);
    }

    // emit blank line into log files
    pub fn blank_line(&mut self) {
        self.air_initial_log.blank_line();
        self.air_middle_log.blank_line();
        self.air_final_log.blank_line();
        self.smt_log.blank_line();
    }

    // Single-line comment, emitted with ";;" into log files
    pub fn comment(&mut self, s: &str) {
        self.air_initial_log.comment(s);
        self.air_middle_log.comment(s);
        self.air_final_log.comment(s);
        self.smt_log.comment(s);
    }

    fn log_set_solver_option(&mut self, option: &str, value: &str) {
        self.air_initial_log.log_set_option(option, value);
        self.air_middle_log.log_set_option(option, value);
        self.air_final_log.log_set_option(option, value);
        self.smt_log.log_set_option(option, value);
    }

    /// cvc5 needs a logic declaration before any command (otherwise it warns on stderr
    /// and falls back to ALL anyway); it must also be told to run incrementally.
    fn set_cvc5_logic(&mut self) {
        self.smt_log.log_node(&node!((set-logic {str_to_node("ALL")})));
        self.set_solver_option_bool("incremental", true, true);
    }

    pub(crate) fn set_solver_option_bool(
        &mut self,
        option: &str,
        value: bool,
        write_to_logs: bool,
    ) {
        if option == "air_recommended_options" && value {
            if self.cross_check != CrossCheckPolicy::Off {
                // The shared stream is solver-neutral: Z3 tuning goes to the primary process
                // only, and the cvc5 logic/incremental setup to the secondary only. Neither
                // touches smt_log (design 05 §2.1, requirement 2).
                for (k, v) in [
                    ("auto_config", "false"),
                    ("smt.mbqi", "false"),
                    ("smt.case_split", "3"),
                    ("smt.qi.eager_threshold", "100.0"),
                    ("smt.delay_units", "true"),
                    ("smt.arith.solver", "2"),
                    ("smt.arith.nl", "false"),
                    ("pi.enabled", "false"),
                    ("rewriter.sort_disjunctions", "false"),
                ] {
                    self.push_primary_startup(&format!("(set-option :{} {})\n", k, v));
                }
                self.push_secondary_startup("(set-logic ALL)\n(set-option :incremental true)\n");
                return;
            }
            match self.solver {
                SmtSolver::Z3 => {
                    self.set_solver_option_bool("auto_config", false, true);
                    self.set_solver_option_bool("smt.mbqi", false, true);
                    self.set_solver_option_u32("smt.case_split", 3, true);
                    self.set_solver_option_f64("smt.qi.eager_threshold", 100.0, true);
                    self.set_solver_option_bool("smt.delay_units", true, true);
                    self.set_solver_option_u32("smt.arith.solver", 2, true);
                    self.set_solver_option_bool("smt.arith.nl", false, true);
                    self.set_solver_option_bool("pi.enabled", false, true);
                    self.set_solver_option_bool("rewriter.sort_disjunctions", false, true);
                }
                SmtSolver::Cvc5 => {
                    self.set_cvc5_logic();
                }
            }
        } else if option == "cvc5_logic_only" && value {
            // Logic declaration without the Z3-oriented tuning preset; a no-op for Z3.
            if matches!(self.solver, SmtSolver::Cvc5) {
                self.set_cvc5_logic();
            }
        } else if option == "single_check_query" && value {
            self.single_check_query = true;
            if write_to_logs {
                self.set_single_check_query();
            }
        } else {
            if write_to_logs {
                self.log_set_solver_option(option, &value.to_string());
            }
        }
    }

    pub(crate) fn set_solver_option_u32(&mut self, option: &str, value: u32, write_to_logs: bool) {
        if option == "rlimit" && write_to_logs && matches!(self.solver, SmtSolver::Z3) {
            self.set_rlimit(value);
        } else {
            if write_to_logs {
                self.log_set_solver_option(option, &value.to_string());
            }
        }
    }

    pub(crate) fn set_solver_option_f64(&mut self, option: &str, value: f64, write_to_logs: bool) {
        if write_to_logs {
            let mut s = value.to_string();
            if !s.contains(".") {
                s += ".0";
            }
            self.log_set_solver_option(option, &s);
        }
    }

    pub(crate) fn set_solver_option_str(&mut self, option: &str, value: &str, write_to_logs: bool) {
        if write_to_logs {
            self.log_set_solver_option(option, value);
        }
    }

    pub fn set_solver_option(&mut self, option: &str, value: &str) {
        if value == "true" {
            self.set_solver_option_bool(option, true, true);
        } else if value == "false" {
            self.set_solver_option_bool(option, false, true);
        } else if let Ok(v) = value.parse::<u32>() {
            self.set_solver_option_u32(option, v, true);
        } else if let Ok(v) = value.parse::<f64>() {
            self.set_solver_option_f64(option, v, true);
        } else if value.is_ascii() {
            self.set_solver_option_str(option, value, true);
        } else {
            panic!("unexpected solver option value {}", value);
        }
    }

    pub(crate) fn push_name_scope(&mut self) {
        self.axiom_infos.push_scope(false);
        self.array_map.push_scope(false);
        self.lambda_map.push_scope(false);
        self.choose_map.push_scope(false);
        self.apply_map.push_scope(false);
        self.typing.decls.push_scope(false);
    }

    pub(crate) fn pop_name_scope(&mut self) {
        self.axiom_infos.pop_scope();
        self.array_map.pop_scope();
        self.lambda_map.pop_scope();
        self.choose_map.pop_scope();
        self.apply_map.pop_scope();
        self.typing.decls.pop_scope();
    }

    fn ensure_started(&mut self) {
        match self.state {
            ContextState::NotStarted => {
                let profile_logfile_name = self.profile_logfile_name.clone();
                if let Some(profile_logfile_name) = profile_logfile_name {
                    self.set_solver_option("trace", "true");
                    // Very expensive.  May be needed to support more detailed log analysis.
                    // self.set_solver_option("proof", "true");

                    // sise does not support backslashes in atoms, which appear in Windows paths
                    let profile_logfile_name = profile_logfile_name.replace("\\", "/");
                    self.log_set_solver_option("trace_file_name", &profile_logfile_name);
                }
                self.blank_line();
                self.comment("AIR prelude");
                self.smt_log.log_node(&node!((declare-sort {str_to_node(crate::def::FUNCTION)} 0)));
                self.blank_line();
                self.state = ContextState::ReadyForQuery;
            }
            ContextState::ReadyForQuery => {}
            ContextState::NoMoreQueriesAllowed => {
                panic!("no more queries allowed after disabling incremental solving");
            }
            _ => {
                panic!("expected call to finish_query before next command");
            }
        }
    }

    pub fn push(&mut self) {
        self.ensure_started();
        self.air_initial_log.log_push();
        self.air_middle_log.log_push();
        self.air_final_log.log_push();
        self.smt_log.log_push();
        self.push_name_scope();
    }

    pub fn pop(&mut self) {
        self.air_initial_log.log_pop();
        self.air_middle_log.log_pop();
        self.air_final_log.log_pop();
        self.smt_log.log_pop();
        self.pop_name_scope();
    }

    pub fn global(&mut self, decl: &Decl) -> Result<(), TypeError> {
        self.ensure_started();
        self.air_initial_log.log_decl(decl);
        self.air_middle_log.log_decl(decl);
        self.air_final_log.log_decl(decl);
        let (gen_decls, decl) = crate::typecheck::check_decl(self, decl)?;
        for gen_decl in gen_decls.iter() {
            crate::smt_verify::smt_add_decl(self, gen_decl);
        }
        crate::typecheck::add_decl(self, &decl, true)?;
        crate::smt_verify::smt_add_decl(self, &decl);
        Ok(())
    }

    pub fn check_valid(
        &mut self,
        message_interface: &dyn crate::messages::MessageInterface,
        diagnostics: &impl Diagnostics,
        query: &Query,
        query_context: QueryContext<'_, '_>,
    ) -> ValidityResult {
        self.ensure_started();

        self.air_initial_log.log_query(query);
        let query = match crate::typecheck::check_query(self, query) {
            Ok(query) => query,
            Err(err) => return ValidityResult::TypeError(err),
        };
        let (query, snapshots, local_vars) = crate::var_to_const::lower_query(&query);
        self.air_middle_log.log_query(&query);
        let query = crate::block_to_assert::lower_query(message_interface, &query);
        self.air_final_log.log_query(&query);

        let model = Model::new(snapshots, local_vars);
        let validity = crate::smt_verify::smt_check_query(
            self,
            diagnostics,
            &query,
            model,
            query_context.report_long_running,
        );
        self.check_valid_used = true;

        validity
    }

    pub fn check_valid_used(&self) -> bool {
        self.check_valid_used
    }

    /// After receiving ValidityResult::Invalid, try to find another error.
    /// only_check_earlier == true means to only look for errors preceding all the previous
    /// errors, with the goal of making sure that the earliest error gets reported.
    /// Once only_check_earlier is set, it remains set until finish_query is called.
    pub fn check_valid_again(
        &mut self,
        diagnostics: &impl Diagnostics,
        only_check_earlier: bool,
        query_context: QueryContext<'_, '_>,
    ) -> ValidityResult {
        if let ContextState::FoundInvalid(infos, Some(air_model)) = self.state.clone() {
            let res = crate::smt_verify::smt_check_assertion(
                self,
                diagnostics,
                infos,
                air_model,
                only_check_earlier,
                query_context.report_long_running,
            );
            self.check_valid_used = true;
            res
        } else {
            panic!("check_valid_again expected query to be ValidityResult::Invalid(_, Some(_))");
        }
    }

    pub fn finish_query(&mut self) {
        if self.single_check_query {
            self.state = ContextState::NoMoreQueriesAllowed;
        } else {
            self.pop_name_scope();
            self.smt_log.log_pop();
            self.state = ContextState::ReadyForQuery;
        }
    }

    pub fn eval_expr(&mut self, expr: sise::TreeNode) -> String {
        self.smt_log.log_eval(expr);
        let smt_data = self.smt_log.take_pipe_data();
        let smt_output = self.get_smt_process().send_commands(smt_data);
        if smt_output.len() != 1 {
            panic!("unexpected output from SMT eval {:?}", smt_output);
        }
        smt_output[0].clone()
    }

    pub fn command(
        &mut self,
        message_interface: &dyn crate::messages::MessageInterface,
        diagnostics: &impl Diagnostics,
        command: &Command,
        query_context: QueryContext<'_, '_>,
    ) -> ValidityResult {
        match &**command {
            CommandX::Push => {
                self.push();
                ValidityResult::Valid(UsageInfo::None)
            }
            CommandX::Pop => {
                self.pop();
                ValidityResult::Valid(UsageInfo::None)
            }
            CommandX::SetOption(option, value) => {
                self.set_solver_option(option, value);
                ValidityResult::Valid(UsageInfo::None)
            }
            CommandX::Global(decl) => {
                if let Err(err) = self.global(&decl) {
                    ValidityResult::TypeError(err)
                } else {
                    ValidityResult::Valid(UsageInfo::None)
                }
            }
            CommandX::CheckValid(query) => {
                self.check_valid(message_interface, diagnostics, &query, query_context)
            }
            #[cfg(feature = "singular")]
            CommandX::CheckSingular(_) => {
                panic!("CheckSingular not supported in this context");
            }
        }
    }
}
