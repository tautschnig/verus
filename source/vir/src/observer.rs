//! Passive verification observer: the proof-coverage tap layer.
//!
//! See `PROOF_COVERAGE.md` §3. The verifier exposes facts at the
//! points the pipeline already funnels everything through; all semantics
//! (classification, provenance tables, instrumentation, evidence) live in an
//! external consumer. Callbacks are passive: they borrow data and return
//! nothing, and cannot alter queries, diagnostics, or verdicts.
//!
//! Threading: buckets verify on worker threads, so one shared observer object
//! is used behind `Arc<Mutex<..>>` and must be `Send`. Callbacks fire under
//! the lock; observers should record and return, not compute.

use crate::ast::Krate;
use crate::def::CommandContext;
use crate::sst::{AssumeIntent, FuncCheckSst, FunctionSst};
use air::ast::Commands;
use air::context::ValidityResult;
use std::any::Any;
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

/// Identifies which solver context a command was installed in or checked
/// against. Spinoff queries (nonlinear, bitvector, profile reruns) replay the
/// ambient context into a fresh solver, so per-query availability must be
/// tracked per solver context, not globally.
pub type SolverContextId = u64;

/// Process-local identity of one verifier query operation and its exact SST
/// payload. Consumers may use this only to correlate callbacks from the same
/// operation; emitted artifacts must derive their own deterministic identity.
pub type QueryInstanceId = usize;

/// The SST construction being lowered when an AIR statement was created.
///
/// This is deliberately construction-site identity rather than proof-coverage
/// policy. Consumers decide whether (for example) a loop-produced assumption
/// is a source fact, a derived control fact, or a generated protocol fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoweringSite {
    Assume(AssumeIntent),
    Assert,
    AssertBitVector,
    AssertQuery,
    AssertCompute,
    AssignInit,
    AssignUpdate,
    Call,
    Return,
    BreakOrContinue,
    If,
    Loop,
    OpenInvariant,
    ClosureInner,
    Fuel,
    RevealString,
    RevealByteString,
    DeadEnd,
    Air,
    Block,
    QueryAssembly,
}

/// One frame in the recursive SST-to-AIR lowering stack.
///
/// `statement` is process-local pointer identity. It is only a correlation key
/// between callbacks for the same `QueryInstanceId`; consumers must resolve it
/// to a deterministic SST/CFG identity before serialization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoweringFrame {
    pub statement: usize,
    pub site: LoweringSite,
}

/// The named slot of a lowering template that emitted an AIR statement.
///
/// `LoweringSite` records *which template* ran; this records *which slot of
/// it*. The distinction only matters for templates that emit more than one
/// kind of statement: a loop emits the same invariant expression into six
/// different slots, and the proof meaning of each is different (establishing
/// an invariant is an obligation on the code before the loop; assuming it at
/// body entry is a premise for the body). Without the slot a consumer has to
/// recover it from statement order and shape.
///
/// This is construction-site identity, not proof-coverage policy: it says
/// where in the template the statement came from, not what it means.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EmissionSlot {
    /// Assert the entry invariants before the loop is first entered.
    LoopEstablish,
    /// Assume the entry invariants at the top of the loop body.
    LoopBodyEntry,
    /// Assert the entry invariants at the end of the loop body.
    LoopMaintain,
    /// Assume the exit invariants after the loop.
    LoopExit,
    /// Assert the exit invariants at a `break`.
    LoopAtBreak,
    /// Assert the entry invariants at a `continue`.
    LoopAtContinue,
    /// Assume the loop condition at the top of the body.
    LoopEntryCondition,
    /// Assume the negated loop condition after the loop.
    LoopExitCondition,
    /// Assume the branch condition in an `if` then-arm.
    BranchThen,
    /// Assume the negated branch condition in an `if` else-arm.
    BranchElse,
    /// Assert the `clause`-th ensures of a `by(bit_vector)` function body.
    BitVectorFunctionEnsures,
    /// Assert the `clause`-th ensures of an `assert ... by(bit_vector)`.
    BitVectorAssertQueryEnsures,
}

/// Exact identity of the source clause an AIR statement was emitted from.
///
/// `clause` indexes the *declaring* list — the SST `invs` vector as written in
/// the source — and never a projection of it. Loop lowering splits the
/// declared invariants into separate entry and exit vectors, and a plain
/// `invariant` (`at_entry && at_exit`) is pushed into both, so an index into
/// either projection would give one source clause two identities and make two
/// different clauses collide on index 0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EmittedClause {
    pub slot: EmissionSlot,
    pub clause: Option<usize>,
    /// The SST loop id owning the clause, for loop slots.
    ///
    /// Recorded so a consumer can tell clause 0 of one loop from clause 0 of
    /// another without parsing the AIR `break_label%<id>` name, and so it
    /// works when `loop_isolation` is off and no break label is present.
    pub loop_id: Option<u64>,
}

/// Exact passive provenance for one structured AIR statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoweredStatement {
    /// Outer-to-inner SST lowering stack at the point this AIR statement was
    /// first produced. Synthetic helper SST nodes may appear at the end; a
    /// consumer can select the nearest frame present in the observed SST tree.
    pub source_chain: Vec<LoweringFrame>,
    /// The construction site that first emitted this AIR statement.
    pub emitted_at: LoweringSite,
}

/// Process-local AIR statement pointer -> exact lowering provenance.
///
/// The map is metadata only. It is never read by canonical verification and is
/// passed to passive observers alongside the unchanged structured AIR query.
pub type LoweringProvenanceMap = BTreeMap<usize, LoweredStatement>;

/// Process-local AIR statement pointer -> emitting template slot and clause.
///
/// Sparse: only statements emitted by a multi-slot template appear. Absence
/// means the template had a single slot, so `LoweringSite` already determines
/// it.
pub type EmissionSlotMap = BTreeMap<usize, EmittedClause>;

/// The construction that emitted a query-local axiom.
///
/// A query-local axiom is a `Decl` in `QueryX.local`, not a statement in the
/// assertion tree, so the statement-keyed maps above cannot reach it. These
/// declarations are built at a handful of fixed points in `sst_to_air`, each
/// with its subject in the loop variable; this records that subject.
///
/// Construction-site identity, not proof-coverage policy: it says which
/// emission point produced the axiom and which declared item it came from,
/// not what the axiom means to a coverage analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LocalAxiomSite {
    /// Type invariant of the function's `param`-th parameter, in declaring
    /// order, assumed for the whole function body.
    ParamTypeInvariant { param: usize },
    /// The function's `clause`-th `requires` clause, in declaring order.
    Requires { clause: usize },
    /// The `index`-th trait bound on the function's type parameters, as
    /// lowered by `traits::trait_bounds_to_air`.
    TraitBound { index: usize },
    /// The function's fuel setting (default, or the non-default hidden set).
    Fuel,
    /// Type invariant of a variable re-assumed in an isolated loop-body
    /// query, for the SST loop `loop_id`.
    LoopTypeInvariant { loop_id: u64 },
    /// Type invariant of a variable assumed in an `assert ... by` query.
    AssertQueryTypeInvariant,
    /// The `clause`-th `requires` of an `assert ... by(bit_vector)`, which
    /// the bit-vector lowering installs as a query-local axiom.
    AssertQueryRequires { clause: usize },
}

/// Process-local AIR `Decl` pointer -> emitting construction.
///
/// The declarations shared by every query of one function (`local_shared`)
/// are cloned by `Arc`, so one entry covers the same axiom in every query it
/// appears in.
pub type LocalAxiomMap = BTreeMap<usize, LocalAxiomSite>;

/// Passive sidecar for one family of commands produced from an SST body.
#[derive(Debug, Clone)]
pub struct LoweringProvenance {
    /// Exact post-`compute_assign_info` SST root consumed by `sst_to_air`.
    /// Process-local only; consumers resolve its pointer identities to stable
    /// structural CFG paths before serialization.
    pub lowered_body: Option<crate::sst::Stm>,
    pub statements: LoweringProvenanceMap,
    pub slots: EmissionSlotMap,
    pub local_axioms: LocalAxiomMap,
}

impl LoweringProvenance {
    pub fn empty() -> Self {
        Self {
            lowered_body: None,
            statements: LoweringProvenanceMap::new(),
            slots: EmissionSlotMap::new(),
            local_axioms: LocalAxiomMap::new(),
        }
    }
}

/// Why a batch of ambient commands is being installed.
#[derive(Debug, Clone)]
pub enum ContextInstallReason {
    /// The AIR/SMT prelude and other bucket-setup batches (fuel, trait decls,
    /// datatype axioms, ...): the `β` background of every query in this
    /// context. The string is the batch title.
    Setup(String),
    /// Axioms owned by a function processed earlier in the SCC schedule.
    FunctionContext {
        /// Which kind of context op installed them (Debug of the verifier's
        /// typed `ContextOp`: SpecDefinition, ReqEns, Broadcast, TraitImpl).
        op: String,
        /// Friendly name of the owning function/lemma; empty for ops with no
        /// single owner (trait impl axioms).
        owner: String,
    },
}

/// Passive observer for the verification pipeline. All methods default to
/// no-ops; a consumer implements only what it needs.
pub trait VerificationObserver: Any + Send {
    /// The crate about to be verified, delivered *before* AST simplification
    /// (which rewrites constructs like `returns` into ensures clauses, erasing
    /// contract layout). `crate_id` names the crate being verified: the
    /// merged `Krate` also carries the functions of every imported crate, and
    /// nothing inside it says which are local.
    fn on_krate_pre_simplify(&mut self, _krate: &Krate, _crate_id: &crate::ast::CrateId) {}

    /// The crate after simplification, with the `NameCtxt` used by lowering,
    /// so AIR names computed by the consumer agree with lowering.
    fn on_krate(&mut self, _krate: &Krate, _name_ctxt: &crate::def::NameCtxt) {}

    /// A function's SST is about to be lowered for a query op. This is the
    /// tree `sst_to_air` will consume: post-`compute_assign_info`, loops still
    /// structured. Fires once per query op that carries a body check.
    fn on_function_sst(
        &mut self,
        _query_instance: QueryInstanceId,
        _function: &FunctionSst,
        _check: &Arc<FuncCheckSst>,
    ) {
    }

    /// Ambient commands installed into a solver context (global declarations
    /// and axioms). Together with `on_query`, this determines per-query
    /// availability: everything installed in `solver` before a query is
    /// available to it.
    fn on_context_installed(
        &mut self,
        _solver: SolverContextId,
        _solver_config: &air::context::SolverReplayConfig,
        _reason: &ContextInstallReason,
        _commands: &Commands,
    ) {
    }

    /// A query command is about to be checked: structured AIR, pre
    /// `var_to_const`, tree shape intact. `context` carries the function,
    /// span, and description.
    fn on_query(
        &mut self,
        _query_instance: Option<QueryInstanceId>,
        _solver: SolverContextId,
        _context: &CommandContext,
        _solver_config: &air::context::SolverReplayConfig,
        _lowering_provenance: &LoweringProvenance,
        _command: &air::ast::Command,
    ) {
    }

    /// The result of checking a query command. Fires once per solver
    /// interaction, including the re-checks the multiple-errors loop issues.
    /// `used_axioms` carries the UNSAT-core axiom names when the solver was
    /// asked for them (`--axiom-usage-info`); the shadow instrumenter obtains
    /// its own cores and does not depend on this.
    fn on_query_result(
        &mut self,
        _query_instance: Option<QueryInstanceId>,
        _solver: SolverContextId,
        _context: &CommandContext,
        _result: &ValidityResult,
    ) {
    }

    /// Verification of the crate is complete; emit any output now.
    fn on_finish(&mut self) {}

    fn as_any(&self) -> &dyn Any;
    fn as_any_mut(&mut self) -> &mut dyn Any;
}

/// Shared handle to the (at most one) registered observer.
///
/// `None` when the feature is off: every tap site reduces to a presence
/// check. The handle is cloned into worker threads and spinoff contexts;
/// all clones point at one object.
pub type ObserverHandle = Option<Arc<Mutex<dyn VerificationObserver>>>;

/// Whether SST-to-AIR lowering should collect passive provenance metadata.
///
/// This mode is derived once from observer registration and passed through the
/// lowering API. It keeps the verifier's normal path free of provenance tree
/// traversal while avoiding any dependency on a particular observer consumer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoweringProvenanceMode {
    Disabled,
    Enabled,
}

impl LoweringProvenanceMode {
    #[inline]
    pub fn for_observer(observer: &ObserverHandle) -> Self {
        if observer.is_some() { Self::Enabled } else { Self::Disabled }
    }

    #[inline]
    pub(crate) fn is_enabled(self) -> bool {
        matches!(self, Self::Enabled)
    }
}

/// Fire a callback on the observer if one is registered.
///
/// Failure isolation is intrinsic to this boundary: the lock is acquired
/// *inside* the unwind guard, so a panicking observer poisons its own mutex;
/// every subsequent callback sees the poisoned lock and is skipped. The
/// panic never escapes into the verifier — the canonical verification
/// result is unaffected, and the failure is reported once (on the
/// transition).
#[inline]
pub fn notify<F: FnOnce(&mut dyn VerificationObserver)>(observer: &ObserverHandle, f: F) {
    if let Some(obs) = observer {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            // A poisoned lock means the observer already failed: skip.
            if let Ok(mut guard) = obs.lock() {
                f(&mut *guard);
            }
        }));
        if r.is_err() {
            eprintln!(
                "verification observer failed (panicked); observer disabled for \
                 the rest of the run — verification itself is unaffected"
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Panicker {
        calls_started: usize,
    }
    impl VerificationObserver for Panicker {
        fn on_finish(&mut self) {
            self.calls_started += 1;
            panic!("deliberate observer panic");
        }
        fn as_any(&self) -> &dyn Any {
            self
        }
        fn as_any_mut(&mut self) -> &mut dyn Any {
            self
        }
    }

    /// A panicking observer must not unwind into the caller, and must be
    /// disabled (subsequent callbacks skipped) via lock poisoning.
    #[test]
    fn panicking_observer_is_contained_and_disabled() {
        let obs: ObserverHandle = Some(Arc::new(Mutex::new(Panicker { calls_started: 0 })));
        // first call: panic contained
        notify(&obs, |o| o.on_finish());
        // second call: skipped (poisoned lock) — would panic again otherwise
        notify(&obs, |o| o.on_finish());
        // the caller is still alive; the observer ran exactly once
        let arc = obs.unwrap();
        let started = match arc.lock() {
            Ok(g) => g.as_any().downcast_ref::<Panicker>().unwrap().calls_started,
            Err(poisoned) => {
                poisoned.into_inner().as_any().downcast_ref::<Panicker>().unwrap().calls_started
            }
        };
        assert_eq!(started, 1, "observer must be disabled after its first panic");
    }

    #[test]
    fn lowering_provenance_mode_tracks_observer_registration() {
        let absent: ObserverHandle = None;
        assert_eq!(LoweringProvenanceMode::for_observer(&absent), LoweringProvenanceMode::Disabled);

        let present: ObserverHandle = Some(Arc::new(Mutex::new(Panicker { calls_started: 0 })));
        assert_eq!(LoweringProvenanceMode::for_observer(&present), LoweringProvenanceMode::Enabled);
    }
}
