//! Dual-solver cross-checking skeleton (design: `plan/05-dual-solver-design.md` §2).
//!
//! The idea: emit ONE solver-neutral SMT-LIB command stream and feed the identical text
//! to two independent solver processes (e.g. cvc5 as primary, Z3 as secondary). Because a
//! single-solver soundness bug that produces a wrong `unsat` is only dangerous if *both*
//! solvers share it, an `unsat`/`sat` disagreement on the same query is a strong soundness
//! signal and is worth a hard stop.
//!
//! This module is a self-contained skeleton: [`SolverSet`] fans a command stream to both
//! children in parallel and [`reconcile`] implements the full verdict-reconciliation table
//! from the design doc. It is deliberately NOT yet wired into
//! [`crate::context::Context`]/[`crate::smt_verify`]; doing so requires the neutral-dialect
//! `Printer` split (design §2.1, risk 1) and per-solver option injection, which are larger
//! changes. Keeping the reconciliation logic here, with unit tests, lets it be exercised
//! and reviewed independently of that refactor.

use crate::context::SmtSolver;
use crate::smt_process::SmtProcess;

/// The three verdicts a solver can report for a `check-sat`, normalised away from
/// solver-specific spellings (e.g. cvc5's "cvc5 interrupted by timeout." is `Unknown`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverVerdict {
    Unsat,
    Sat,
    Unknown,
}

impl SolverVerdict {
    /// Human-readable verdict name for diagnostics.
    pub fn name(&self) -> &'static str {
        match self {
            SolverVerdict::Unsat => "unsat",
            SolverVerdict::Sat => "sat",
            SolverVerdict::Unknown => "unknown",
        }
    }

    /// Extract the verdict from a solver's response lines. The last recognised verdict
    /// wins (a query ends in exactly one `check-sat` result once acknowledgements are
    /// stripped); anything unrecognised is treated as `Unknown`, never as a proof.
    pub fn from_lines(lines: &[String]) -> SolverVerdict {
        let mut verdict = SolverVerdict::Unknown;
        for line in lines {
            let line = line.trim();
            if line == "unsat" {
                verdict = SolverVerdict::Unsat;
            } else if line == "sat" {
                verdict = SolverVerdict::Sat;
            } else if line == "unknown"
                || line == "timeout"
                || line.contains("interrupted by timeout")
                || line.contains("resource limit")
            {
                verdict = SolverVerdict::Unknown;
            }
        }
        verdict
    }
}

/// How aggressively to act on what the secondary solver says.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CrossCheckPolicy {
    /// Only the primary solver's verdict is used (cross-check disabled).
    Off,
    /// Use the primary verdict, but emit a warning when the secondary cannot confirm a
    /// proof; still hard-error on an `unsat`/`sat` disagreement.
    Warn,
    /// Additionally treat a proof the secondary could not independently confirm
    /// (`unsat` vs `unknown`) as a hard error.
    Strict,
}

impl Default for CrossCheckPolicy {
    fn default() -> Self {
        CrossCheckPolicy::Off
    }
}

/// What the caller should do after reconciling the two verdicts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CrossCheckAction {
    /// Proceed using the primary solver's verdict/result unchanged.
    UsePrimary,
    /// Proceed using the primary verdict, but surface `message` as a warning.
    UsePrimaryWithWarning(String),
    /// Stop: the two solvers disagree in a way that signals a soundness problem or (under
    /// `Strict`) an unconfirmed proof. `message` describes the disagreement; the caller is
    /// expected to dump both transcripts and the query for offline inspection.
    HardError(String),
}

/// Reconcile the primary and secondary verdicts per the design-doc table (§2.2).
///
/// `primary` is the solver whose verdict is authoritative for the returned result;
/// `secondary` is `None` when no cross-check ran. The interesting rows are the
/// `unsat`/`sat` cross pairs — those are genuine soundness signals (either a solver bug or
/// an encoding that is not actually solver-neutral) and become a hard error under both
/// `Warn` and `Strict`.
pub fn reconcile(
    policy: CrossCheckPolicy,
    primary: SolverVerdict,
    secondary: Option<SolverVerdict>,
) -> CrossCheckAction {
    use CrossCheckPolicy::*;
    use SolverVerdict::*;

    let Some(secondary) = secondary else {
        return CrossCheckAction::UsePrimary;
    };
    if policy == Off {
        // Cross-check disabled: the primary verdict stands regardless of the secondary.
        return CrossCheckAction::UsePrimary;
    }

    match (primary, secondary) {
        // Both proved it: independently confirmed.
        (Unsat, Unsat) => CrossCheckAction::UsePrimary,
        // Primary proved it, secondary could not confirm.
        (Unsat, Unknown) => match policy {
            Off => unreachable!(),
            Warn => CrossCheckAction::UsePrimaryWithWarning(
                "secondary solver could not independently confirm this proof".to_string(),
            ),
            Strict => CrossCheckAction::HardError(
                "cross-check failed: proof not independently confirmed by the secondary solver"
                    .to_string(),
            ),
        },
        // Soundness signal: one solver proves it, the other refutes it.
        (Unsat, Sat) | (Sat, Unsat) => CrossCheckAction::HardError(
            "cross-check disagreement: one solver reported unsat and the other sat on the \
             identical query (possible solver soundness bug or non-neutral encoding)"
                .to_string(),
        ),
        // Primary found a counterexample; secondary agrees or is inconclusive.
        (Sat, Sat) | (Sat, Unknown) => CrossCheckAction::UsePrimary,
        // Primary inconclusive; secondary proved it. Keep the primary (unknown) verdict but
        // note that switching primaries would discharge the goal.
        (Unknown, Unsat) => match policy {
            Off => unreachable!(),
            Warn | Strict => CrossCheckAction::UsePrimaryWithWarning(
                "secondary solver proved this goal that the primary left unknown; \
                 consider making it the primary solver"
                    .to_string(),
            ),
        },
        // Both inconclusive, or primary inconclusive and secondary refuted: nothing the
        // cross-check can add; keep the primary's (non-proof) verdict.
        (Unknown, Unknown) | (Unknown, Sat) => CrossCheckAction::UsePrimary,
    }
}

/// A primary solver process with an optional secondary for cross-checking. The same
/// command text is sent to both; verdicts are reconciled with [`reconcile`].
///
/// Skeleton: launched and driven explicitly by tests / future call sites. Wiring it into
/// `Context` (so the whole pipeline fans out) is future work (design §2.1).
pub struct SolverSet {
    pub primary_solver: SmtSolver,
    pub secondary_solver: Option<SmtSolver>,
    pub policy: CrossCheckPolicy,
    primary: SmtProcess,
    secondary: Option<SmtProcess>,
}

/// The outcome of sending a query to a [`SolverSet`]: the primary's raw response lines
/// (from which the caller builds the real result) plus the reconciliation action.
pub struct SolverSetResponse {
    pub primary_lines: Vec<String>,
    pub secondary_lines: Option<Vec<String>>,
    pub primary_verdict: SolverVerdict,
    pub secondary_verdict: Option<SolverVerdict>,
    pub action: CrossCheckAction,
}

impl SolverSet {
    /// Launch the primary and (if cross-checking) secondary solver processes.
    pub fn launch(
        primary_solver: SmtSolver,
        secondary_solver: Option<SmtSolver>,
        policy: CrossCheckPolicy,
    ) -> Self {
        let primary = SmtProcess::launch(&primary_solver, None);
        let secondary = match (secondary_solver, policy) {
            (Some(s), CrossCheckPolicy::Warn) | (Some(s), CrossCheckPolicy::Strict) => {
                Some(SmtProcess::launch(&s, None))
            }
            _ => None,
        };
        SolverSet { primary_solver, secondary_solver, policy, primary, secondary }
    }

    /// Fan the identical command stream to both solvers in parallel, wait for both, and
    /// reconcile their verdicts. The primary's lines are always returned so the caller can
    /// build its normal `ValidityResult`; `action` says whether to warn or hard-stop.
    pub fn send_commands(&mut self, commands: Vec<u8>) -> SolverSetResponse {
        // Start the secondary first so both run concurrently while we wait.
        let (secondary_lines, secondary_verdict) = if let Some(secondary) = &mut self.secondary {
            // send_commands here is a simple synchronous fan-out; a fully wired version
            // would use send_commands_async on both and join the handles (design §2.1).
            let lines = secondary.send_commands(commands.clone());
            let verdict = SolverVerdict::from_lines(&lines);
            (Some(lines), Some(verdict))
        } else {
            (None, None)
        };
        let primary_lines = self.primary.send_commands(commands);
        let primary_verdict = SolverVerdict::from_lines(&primary_lines);
        let action = reconcile(self.policy, primary_verdict, secondary_verdict);
        SolverSetResponse {
            primary_lines,
            secondary_lines,
            primary_verdict,
            secondary_verdict,
            action,
        }
    }
}

// ============================================================================
// Detached (asynchronous) secondary cross-checking (design 05 §2, async variant)
// ============================================================================
//
// The synchronous cross-check (Context::check_sat_fanned as originally written) put the
// slower cvc5 solve on the critical path: the primary's verdict could not be interpreted
// until the secondary had also answered, which cost ~3.1x wall on vstd. Profiling showed
// ~92% of cvc5's time is the check-sat solve itself, so the only way to recover the wall
// time is to take the secondary off the critical path entirely.
//
// This module does that. Each module bucket keeps its own cvc5 process (as before, so the
// incremental declaration/push-pop state stays in lockstep), but that process is now driven
// by a dedicated background worker thread. The primary thread reports its verdict
// immediately and hands the worker a queue of jobs: solver-neutral declaration chunks
// (`Commands`) and check-sat requests carrying the already-known primary verdict
// (`CheckSat`). The worker runs cvc5 and reconciles when the answer comes back.
//
// Soundness is preserved by a MANDATORY crate-end join (`SecondaryRegistry::join_all`):
// verification cannot report success until every queued secondary check-sat has been
// answered or the join times out (a timed-out secondary counts as `unknown`, never a
// confirmation). An `unsat`/`sat` disagreement is recorded as a hard error surfaced at
// crate end, which forces a non-zero exit and an `error:` diagnostic naming the function.
//
// Resource use is bounded on two axes (design constraint 5): a process-permit semaphore
// caps the number of concurrent cvc5 processes to a small K (2-4), and each worker's job
// channel is a bounded `sync_channel`, so a primary that races ahead of a lagging secondary
// blocks on `send` (backpressure) rather than letting the queue — and memory — grow without
// limit.

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{Receiver, SyncSender, sync_channel};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

/// Process-global count of warn-level cross-check non-confirmations (the secondary solver
/// could not independently confirm a proof the primary discharged). Reported at crate end.
static CROSS_CHECK_WARN_COUNT: AtomicU64 = AtomicU64::new(0);
/// Process-global count of disagreement dumps written, so each disagreement gets a unique
/// `.verus-solver-log/disagreement-<n>.smt2` filename across all workers.
static DISAGREEMENT_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Total number of warn-level cross-check non-confirmations emitted so far.
pub fn cross_check_warn_count() -> u64 {
    CROSS_CHECK_WARN_COUNT.load(Ordering::Relaxed)
}

/// A reconciliation result discovered asynchronously by a secondary worker, to be surfaced
/// on the main thread at crate end. Carries only owned strings so it is trivially `Send`.
#[derive(Debug, Clone)]
pub enum CrossCheckOutcome {
    /// The secondary could not confirm a proof (or proved a goal the primary left unknown):
    /// a warning under `Warn`. Reported at crate end (may trail the verdict line).
    Warning(String),
    /// An `unsat`/`sat` disagreement, or (under `Strict`) an unconfirmed proof: a hard error
    /// that must fail the build.
    HardError(String),
}

/// A single ordered unit of work for a secondary worker. Sent in the exact order the primary
/// emitted the corresponding solver-neutral text, so the secondary's incremental state stays
/// in lockstep with the primary's.
enum SecondaryJob {
    /// Solver-neutral declarations / push / pop. The response is ignored; this only keeps the
    /// secondary process's state consistent for the next check-sat.
    Commands(Vec<u8>),
    /// A check-sat whose primary verdict is already known. The worker runs cvc5 on the
    /// identical neutral text and reconciles the two verdicts.
    CheckSat {
        neutral_commands: Vec<u8>,
        primary_verdict: SolverVerdict,
        primary_lines: Vec<String>,
        function: String,
        query_id: u64,
    },
}

/// Crate-level coordinator for all detached secondary (cvc5) workers.
///
/// One is created per crate (when cross-check is enabled) and shared, via `Arc`, with every
/// `Context`. It owns the process-permit semaphore, the outstanding-job accounting used by
/// the mandatory crate-end join, and the collected outcomes.
pub struct SecondaryRegistry {
    policy: CrossCheckPolicy,
    dump_dir: PathBuf,
    /// The secondary (cvc5) per-check resource budget, in cvc5 rlimit units (0 = infinity).
    secondary_rlimit: u32,
    /// Test-only: force every secondary to report `sat` on a primary `unsat`.
    inject_disagreement: bool,
    /// Bound on each worker's job channel (backpressure).
    queue_bound: usize,
    /// Available cvc5 process permits; workers block until one is free before launching.
    permits: Mutex<usize>,
    permits_cv: Condvar,
    /// Number of enqueued check-sat jobs not yet reconciled; the crate-end join waits on this.
    outstanding: Mutex<usize>,
    outstanding_cv: Condvar,
    outcomes: Mutex<Vec<CrossCheckOutcome>>,
    handles: Mutex<Vec<JoinHandle<()>>>,
}

impl SecondaryRegistry {
    pub fn new(
        policy: CrossCheckPolicy,
        dump_dir: PathBuf,
        secondary_rlimit: u32,
        inject_disagreement: bool,
        max_processes: usize,
        queue_bound: usize,
    ) -> Arc<Self> {
        Arc::new(SecondaryRegistry {
            policy,
            dump_dir,
            secondary_rlimit,
            inject_disagreement,
            queue_bound: queue_bound.max(1),
            permits: Mutex::new(max_processes.max(1)),
            permits_cv: Condvar::new(),
            outstanding: Mutex::new(0),
            outstanding_cv: Condvar::new(),
            outcomes: Mutex::new(Vec::new()),
            handles: Mutex::new(Vec::new()),
        })
    }

    /// Spawn a background worker owning one cvc5 process for a single bucket's `Context`.
    /// `startup` is the cvc5-only startup text (logic + incremental) accumulated by the
    /// context; the worker appends the rlimit-per budget before any declarations.
    pub fn spawn_secondary(self: &Arc<Self>, startup: Vec<u8>) -> SecondaryChannel {
        let (tx, rx) = sync_channel::<SecondaryJob>(self.queue_bound);
        let registry = Arc::clone(self);
        let handle = std::thread::spawn(move || secondary_worker(registry, startup, rx));
        self.handles.lock().unwrap().push(handle);
        SecondaryChannel { tx, registry: Arc::clone(self) }
    }

    fn acquire_permit(&self) {
        let mut n = self.permits.lock().unwrap();
        while *n == 0 {
            n = self.permits_cv.wait(n).unwrap();
        }
        *n -= 1;
    }

    fn release_permit(&self) {
        let mut n = self.permits.lock().unwrap();
        *n += 1;
        self.permits_cv.notify_one();
    }

    fn job_enqueued(&self) {
        let mut n = self.outstanding.lock().unwrap();
        *n += 1;
    }

    fn job_reconciled(&self) {
        let mut n = self.outstanding.lock().unwrap();
        *n -= 1;
        if *n == 0 {
            self.outstanding_cv.notify_all();
        }
    }

    fn record(&self, outcome: CrossCheckOutcome) {
        self.outcomes.lock().unwrap().push(outcome);
    }

    /// Reconcile one check-sat's verdicts and record any resulting outcome.
    fn reconcile_and_record(
        &self,
        primary: SolverVerdict,
        secondary: SolverVerdict,
        function: &str,
        query_id: u64,
        transcript: &[u8],
        primary_lines: &[String],
        secondary_lines: &[String],
    ) {
        use SolverVerdict::*;
        match reconcile(self.policy, primary, Some(secondary)) {
            CrossCheckAction::UsePrimary => {}
            CrossCheckAction::UsePrimaryWithWarning(_) => {
                CROSS_CHECK_WARN_COUNT.fetch_add(1, Ordering::Relaxed);
                let msg = match (primary, secondary) {
                    (Unsat, _) => format!(
                        "cross-check: cvc5 could not independently confirm the proof of {}",
                        function
                    ),
                    (Unknown, Unsat) => format!(
                        "cross-check: z3 left {} unknown but cvc5 proved it (consider making cvc5 the primary solver)",
                        function
                    ),
                    _ => {
                        format!("cross-check: the secondary solver could not confirm {}", function)
                    }
                };
                self.record(CrossCheckOutcome::Warning(msg));
            }
            CrossCheckAction::HardError(reason) => {
                let dumped = self
                    .dump(
                        function,
                        query_id,
                        transcript,
                        primary_lines,
                        secondary_lines,
                        primary,
                        secondary,
                    )
                    .map(|p| format!("; query and both transcripts dumped to {}", p.display()))
                    .unwrap_or_default();
                let msg = format!(
                    "cross-check disagreement in {}: z3 reported {} but cvc5 reported {} on the \
                     identical query{} ({})",
                    function,
                    primary.name(),
                    secondary.name(),
                    dumped,
                    reason,
                );
                self.record(CrossCheckOutcome::HardError(msg));
            }
        }
    }

    /// Write the accumulated solver-neutral query plus both solvers' response transcripts to
    /// `.verus-solver-log/disagreement-<n>.smt2`.
    fn dump(
        &self,
        function: &str,
        _query_id: u64,
        transcript: &[u8],
        primary_lines: &[String],
        secondary_lines: &[String],
        primary_verdict: SolverVerdict,
        secondary_verdict: SolverVerdict,
    ) -> Option<PathBuf> {
        std::fs::create_dir_all(&self.dump_dir).ok()?;
        let n = DISAGREEMENT_COUNTER.fetch_add(1, Ordering::Relaxed);
        let path = self.dump_dir.join(format!("disagreement-{}.smt2", n));
        let mut out = String::new();
        out += &format!(";; cross-check disagreement for {}\n", function);
        out += &format!(
            ";; z3 (primary) = {}, cvc5 (secondary) = {}\n",
            primary_verdict.name(),
            secondary_verdict.name(),
        );
        out += ";; ======== solver-neutral query (identical text sent to both) ========\n";
        out += &String::from_utf8_lossy(transcript);
        out += "\n;; ======== z3 (primary) response transcript ========\n";
        for line in primary_lines {
            out += ";; ";
            out += line;
            out += "\n";
        }
        out += ";; ======== cvc5 (secondary) response transcript ========\n";
        for line in secondary_lines {
            out += ";; ";
            out += line;
            out += "\n";
        }
        std::fs::write(&path, out).ok()?;
        Some(path)
    }

    /// MANDATORY crate-end join (design constraint 4). Block until every enqueued secondary
    /// check-sat has been reconciled, or `timeout` elapses (a still-outstanding secondary is
    /// then treated as `unknown`, so it never turns into a spurious error). Returns all
    /// accumulated outcomes for the caller to surface as diagnostics.
    ///
    /// Returns `(outcomes, timed_out)`: when `timed_out` is true, some secondary queries were
    /// still in flight at the deadline and were left un-reconciled (counted as `unknown`).
    pub fn join_all(&self, timeout: Duration) -> (Vec<CrossCheckOutcome>, bool) {
        let mut timed_out = false;
        {
            let mut n = self.outstanding.lock().unwrap();
            let deadline = Instant::now() + timeout;
            while *n > 0 {
                let now = Instant::now();
                if now >= deadline {
                    timed_out = true;
                    break;
                }
                let (guard, res) = self.outstanding_cv.wait_timeout(n, deadline - now).unwrap();
                n = guard;
                if res.timed_out() && *n > 0 {
                    timed_out = true;
                    break;
                }
            }
        }
        let handles = std::mem::take(&mut *self.handles.lock().unwrap());
        if timed_out {
            // Honour the timeout: do not block on workers still solving. Contexts (senders)
            // are dropped, so each worker terminates once its rlimit-bounded queue drains;
            // we simply do not wait for it. Any process still alive is reaped at process exit.
            for handle in handles {
                if handle.is_finished() {
                    let _ = handle.join();
                }
            }
        } else {
            // All queued check-sats reconciled; workers are draining their tails and will
            // exit promptly (each cvc5 solve is rlimit-bounded), so joining cannot hang.
            for handle in handles {
                let _ = handle.join();
            }
        }
        (std::mem::take(&mut *self.outcomes.lock().unwrap()), timed_out)
    }
}

/// The primary-thread handle to one bucket's detached secondary worker. Dropping it closes
/// the channel, which lets the worker drain and exit.
pub struct SecondaryChannel {
    tx: SyncSender<SecondaryJob>,
    registry: Arc<SecondaryRegistry>,
}

impl SecondaryChannel {
    /// Enqueue solver-neutral declarations / push / pop for the secondary (ordered).
    pub fn send_commands(&self, commands: Vec<u8>) {
        let _ = self.tx.send(SecondaryJob::Commands(commands));
    }

    /// Enqueue a check-sat with its already-known primary verdict. Accounts the job as
    /// outstanding so the crate-end join waits for its reconciliation.
    pub fn send_check_sat(
        &self,
        neutral_commands: Vec<u8>,
        primary_lines: Vec<String>,
        primary_verdict: SolverVerdict,
        function: String,
        query_id: u64,
    ) {
        self.registry.job_enqueued();
        let job = SecondaryJob::CheckSat {
            neutral_commands,
            primary_verdict,
            primary_lines,
            function,
            query_id,
        };
        if self.tx.send(job).is_err() {
            // The worker is gone (should not happen before crate end); un-account the job so
            // the join does not wait forever.
            self.registry.job_reconciled();
        }
    }
}

/// Body of a secondary worker thread: own one cvc5 process and service its ordered job queue.
fn secondary_worker(
    registry: Arc<SecondaryRegistry>,
    startup: Vec<u8>,
    rx: Receiver<SecondaryJob>,
) {
    let mut process: Option<SmtProcess> = None;
    let mut have_permit = false;
    // The solver-neutral text seen so far, for the disagreement dump.
    let mut transcript: Vec<u8> = Vec::new();

    while let Ok(job) = rx.recv() {
        // Launch cvc5 lazily on the first job, so a context that never issues a default-prover
        // query neither spawns a process nor holds a permit.
        if process.is_none() {
            registry.acquire_permit();
            have_permit = true;
            let mut proc = SmtProcess::launch(&SmtSolver::Cvc5, None);
            let mut s = startup.clone();
            if registry.secondary_rlimit > 0 {
                s.extend_from_slice(
                    format!("(set-option :rlimit-per {})\n", registry.secondary_rlimit).as_bytes(),
                );
            }
            if !s.is_empty() {
                let _ = proc.send_commands(s);
            }
            process = Some(proc);
        }
        let proc = process.as_mut().unwrap();
        match job {
            SecondaryJob::Commands(commands) => {
                transcript.extend_from_slice(&commands);
                let _ = proc.send_commands(commands);
            }
            SecondaryJob::CheckSat {
                neutral_commands,
                primary_verdict,
                primary_lines,
                function,
                query_id,
            } => {
                transcript.extend_from_slice(&neutral_commands);
                let secondary_lines = proc.send_commands(neutral_commands);
                let mut secondary_verdict = SolverVerdict::from_lines(&secondary_lines);
                if registry.inject_disagreement && primary_verdict == SolverVerdict::Unsat {
                    secondary_verdict = SolverVerdict::Sat;
                }
                registry.reconcile_and_record(
                    primary_verdict,
                    secondary_verdict,
                    &function,
                    query_id,
                    &transcript,
                    &primary_lines,
                    &secondary_lines,
                );
                registry.job_reconciled();
            }
        }
    }

    if have_permit {
        registry.release_permit();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use CrossCheckPolicy::*;
    use SolverVerdict::*;

    #[test]
    fn verdict_parsing() {
        assert_eq!(SolverVerdict::from_lines(&["unsat".to_string()]), Unsat);
        assert_eq!(SolverVerdict::from_lines(&["sat".to_string()]), Sat);
        assert_eq!(SolverVerdict::from_lines(&["unknown".to_string()]), Unknown);
        assert_eq!(
            SolverVerdict::from_lines(&["cvc5 interrupted by timeout.".to_string()]),
            Unknown
        );
        // No recognised verdict is never mistaken for a proof.
        assert_eq!(SolverVerdict::from_lines(&["(error \"boom\")".to_string()]), Unknown);
        // Last verdict wins (e.g. push/pop bookkeeping before the real answer).
        assert_eq!(SolverVerdict::from_lines(&["sat".to_string(), "unsat".to_string()]), Unsat);
    }

    #[test]
    fn no_secondary_is_always_use_primary() {
        for policy in [Off, Warn, Strict] {
            for v in [Unsat, Sat, Unknown] {
                assert_eq!(reconcile(policy, v, None), CrossCheckAction::UsePrimary);
            }
        }
    }

    #[test]
    fn off_ignores_secondary() {
        for p in [Unsat, Sat, Unknown] {
            for s in [Unsat, Sat, Unknown] {
                assert_eq!(reconcile(Off, p, Some(s)), CrossCheckAction::UsePrimary);
            }
        }
    }

    #[test]
    fn agreement_uses_primary() {
        assert_eq!(reconcile(Warn, Unsat, Some(Unsat)), CrossCheckAction::UsePrimary);
        assert_eq!(reconcile(Strict, Unsat, Some(Unsat)), CrossCheckAction::UsePrimary);
        assert_eq!(reconcile(Warn, Sat, Some(Sat)), CrossCheckAction::UsePrimary);
        assert_eq!(reconcile(Strict, Sat, Some(Sat)), CrossCheckAction::UsePrimary);
        assert_eq!(reconcile(Warn, Unknown, Some(Unknown)), CrossCheckAction::UsePrimary);
    }

    #[test]
    fn unconfirmed_proof_warns_or_errors() {
        assert!(matches!(
            reconcile(Warn, Unsat, Some(Unknown)),
            CrossCheckAction::UsePrimaryWithWarning(_)
        ));
        assert!(matches!(reconcile(Strict, Unsat, Some(Unknown)), CrossCheckAction::HardError(_)));
    }

    #[test]
    fn unsat_vs_sat_is_a_hard_error_both_directions() {
        for policy in [Warn, Strict] {
            assert!(matches!(reconcile(policy, Unsat, Some(Sat)), CrossCheckAction::HardError(_)));
            assert!(matches!(reconcile(policy, Sat, Some(Unsat)), CrossCheckAction::HardError(_)));
        }
        // With cross-checking Off, even a disagreement defers to the primary.
        assert_eq!(reconcile(Off, Unsat, Some(Sat)), CrossCheckAction::UsePrimary);
    }

    #[test]
    fn counterexample_keeps_primary() {
        assert_eq!(reconcile(Warn, Sat, Some(Unknown)), CrossCheckAction::UsePrimary);
        assert_eq!(reconcile(Strict, Sat, Some(Unknown)), CrossCheckAction::UsePrimary);
    }

    #[test]
    fn secondary_proves_what_primary_could_not() {
        assert!(matches!(
            reconcile(Warn, Unknown, Some(Unsat)),
            CrossCheckAction::UsePrimaryWithWarning(_)
        ));
        assert!(matches!(
            reconcile(Strict, Unknown, Some(Unsat)),
            CrossCheckAction::UsePrimaryWithWarning(_)
        ));
        // Primary unknown, secondary inconclusive/refuting: nothing to add.
        assert_eq!(reconcile(Warn, Unknown, Some(Unknown)), CrossCheckAction::UsePrimary);
        assert_eq!(reconcile(Warn, Unknown, Some(Sat)), CrossCheckAction::UsePrimary);
    }
}
