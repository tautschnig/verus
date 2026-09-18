//! The typed verification-argument graph.
//!
//! Vertices are **occurrences** (query-scoped labels), plus artifact ids,
//! ambient labels, and per-query β vertices. Occurrences are never projected
//! to artifacts during construction — an invariant clause's five protocol
//! positions are five distinct vertices, connected by explicit typed edges.
//! Projecting early collapses the positions and can manufacture a false
//! self-loop (a clause's exit assume in its own entry check's tail), so
//! artifact projection is a display operation only.
//!
//! Edge kinds, all hyperarcs `tail (jointly sufficient) → head`:
//!
//! - `SupportedBy` — from a *focused* core: the premises a single terminal's
//!   discharge consumed. The only evidence-bearing dependency edge: a batch
//!   core is a joint witness for the whole batch and cannot say which
//!   obligation consumed which premise.
//! - `TerminalOf` — {terminals} → parent obligation (conjunction).
//! - `CertifiedBy` — checked obligations → exported assumption. The loop
//!   protocol (entry check licenses the induction hypothesis; entry + latch
//!   license the exit export), local lemmas (outer requires-check licenses
//!   the inner hypothesis; the inner goal licenses the outer assumption),
//!   and the callee side of contracts.
//! - `Demand` — a virtual, call-local licensing step. Ordinary calls start
//!   from the callee's ensures aggregate; recursive calls start from their own
//!   decrease guard, so a recursion is licensed per call rather than by a
//!   component-wide certificate. The tail also carries the precondition checks
//!   the caller discharged; restricting those to the clauses the callee's proof
//!   used needs a measurement v0.1 does not take
//!   (`licensing::DemandCall`).
//! - `Aggregates` — {clause artifacts} → aggregate artifact.
//! - `ObservedInBatch` — one joint {core premises} → {core obligations}
//!   batch observation. *Weak*: recorded for coverage and display, excluded
//!   from derivation, ablation, and every dependency finding. Per-obligation
//!   scopes are separate metadata and are inherited by terminal children.
//! - `ElaboratesTo` — artifact → occurrence (either role). Not a derivation
//!   edge at all: it is the deletion/display relation. Ablating an artifact
//!   deletes exactly the occurrences it elaborates to — including its own
//!   generated obligations, which are therefore never reported as broken.
//!
//! Derivation (`forward`): worklist fixpoint over the strong kinds
//! (`SupportedBy`, `TerminalOf`, `CertifiedBy`, `Aggregates`). Roots are β
//! vertices, ambient labels, and premise occurrences with no `CertifiedBy`
//! in-edge (raw facts). Obligations derive only through their evidence.
//! Cycles (loop invariants, recursion) converge in the fixpoint; the loop
//! protocol's licensing order (entry → hypothesis → latch → exit) makes the
//! induction well-founded inside the graph.
//!
//! Construction is layered (`PROOF_COVERAGE_DESIGN.md` §3):
//! [`crate::facts`] is the mechanical, policy-free translation of the record
//! (L2) and the single door for solver evidence; [`crate::licensing`] is the
//! enumerable list of licensing rules (L3). [`build`] composes them. This
//! module owns the graph type, grounding, slicing, and explanation.

use std::collections::{BTreeMap, BTreeSet};

// The analyzer consumes `crate::record` directly rather than a tolerant
// subset, so it cannot invent a spelling the producer never emits, and cannot
// miss one the producer does.

use crate::facts::{self, CallBoundaryInfo, ObligationScope};
use crate::licensing::{self, DemandCall, LicensingRule};
use crate::record::{Carrier, CoverageRecord, EmissionRole, OriginKind, Role};

// ── the typed graph ──────────────────────────────────────────────────────────

/// What relation an arc asserts.
///
/// Whether an arc carries dependency or is display only is the analyzer's own
/// definition of proof dependency, so it belongs in the type rather than in
/// string membership.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArcKind {
    /// From a *focused* core: the premises a single terminal's discharge
    /// consumed. The only evidence-bearing dependency edge.
    SupportedBy,
    /// {terminals} -> parent obligation (conjunction).
    TerminalOf,
    /// Checked obligations -> exported assumption: the loop, lemma and
    /// contract protocols. This is a licensing rule, not an observation.
    CertifiedBy,
    /// {clause artifacts} -> aggregate artifact.
    Aggregates,
    /// One joint {core premises} -> {core obligations} batch observation.
    /// Weak: recorded for coverage and display, excluded from derivation and
    /// every dependency finding.
    ObservedInBatch,
    /// artifact -> occurrence. The deletion/display relation, not a
    /// derivation edge at all.
    ElaboratesTo,
    /// A call-local licensing step. Stored as a typed call relation rather
    /// than a static arc because its tail depends on the call policy (opaque
    /// stops before the callee proof, modular does not).
    Demand,
}

impl ArcKind {
    pub const ALL: &'static [ArcKind] = &[
        ArcKind::SupportedBy,
        ArcKind::TerminalOf,
        ArcKind::CertifiedBy,
        ArcKind::Aggregates,
        ArcKind::ObservedInBatch,
        ArcKind::ElaboratesTo,
        ArcKind::Demand,
    ];

    /// Is this kind used for derivation and ablation, i.e. does it carry
    /// strong dependency evidence?
    ///
    /// Exhaustive by construction: a new arc kind cannot be added without
    /// deciding whether it is load-bearing.
    pub fn is_strong(self) -> bool {
        match self {
            ArcKind::SupportedBy
            | ArcKind::TerminalOf
            | ArcKind::CertifiedBy
            | ArcKind::Aggregates
            | ArcKind::Demand => true,
            ArcKind::ObservedInBatch | ArcKind::ElaboratesTo => false,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            ArcKind::SupportedBy => "SupportedBy",
            ArcKind::TerminalOf => "TerminalOf",
            ArcKind::CertifiedBy => "CertifiedBy",
            ArcKind::Aggregates => "Aggregates",
            ArcKind::ObservedInBatch => "ObservedInBatch",
            ArcKind::ElaboratesTo => "ElaboratesTo",
            ArcKind::Demand => "Demand",
        }
    }
}

impl std::fmt::Display for ArcKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Is this kind used for derivation/ablation (strong dependency evidence)?
///
/// A free function for call-site readability; the decision lives in
/// `ArcKind::is_strong`, where it is exhaustive over the vocabulary.
pub fn strong(kind: ArcKind) -> bool {
    kind.is_strong()
}

#[derive(Clone)]
pub struct Arc {
    pub tail: BTreeSet<String>,
    pub head: BTreeSet<String>,
    pub kind: ArcKind,
    pub query: Option<u64>,
    /// human-auditable justification: which protocol/evidence instance
    pub why: String,
}

#[derive(Default, Clone)]
pub struct VertexInfo {
    pub detail: String,
    /// Record-derived values. `None` means this vertex is not an occurrence
    /// (an artifact or background-axiom vertex), which the previous empty
    /// strings could not distinguish from an unknown value.
    pub origin_kind: Option<OriginKind>,
    pub role: Option<Role>,
    pub carrier: Option<Carrier>,
    pub span: Option<String>,
    pub fun: Option<String>,
    pub node: Option<String>,
    /// Display projection: the artifact this occurrence elaborates from.
    pub artifact: Option<String>,
    /// The typed emission role; `phase` is rendered from it for display.
    pub emission: Option<EmissionRole>,
    pub phase: Option<String>,
    /// origin.kind == "unresolved" — makes any containing derivation Partial
    pub unresolved: bool,
    /// attribution rule id (ledger); provenance citation
    pub rule: Option<String>,
    /// artifact-join rule id; provenance citation
    pub join_rule: Option<String>,
}

/// Whether a backward slice expands a call through the callee's contract
/// proof or treats the call as an intentional modular boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallPolicy {
    Opaque,
    Modular,
}

/// Slice policy. Deliberately without a `Default`: a policy default is how
/// the report and the study text come to disagree quietly. Every call site
/// names the call policy it wants.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SliceOptions {
    pub calls: CallPolicy,
}

/// An intentional or epistemic stopping point in a policy-aware slice.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Boundary {
    Call {
        premise: String,
        caller: String,
        callee: Option<String>,
        cfg_node: Option<String>,
        call_artifact: Option<String>,
    },
    Unmeasured {
        vertex: String,
        solver_context: u64,
        terminal_path: Option<String>,
    },
    Ungrounded {
        vertex: String,
    },
    /// The slice crossed into a contract clause declared on a trait. In the
    /// record it is certified by the refinement checks of the recorded
    /// implementations jointly; implementations in other crates are outside
    /// this record, so the certification is relative to `implementations`.
    TraitContract {
        artifact: String,
        trait_method: String,
        implementations: BTreeSet<String>,
    },
}

/// A policy-aware backward slice.
///
/// `definite` contains vertices reached through productive, grounded strong
/// arcs. `possible` contains only the conservative scope added at opaque
/// measurements (and partial vertices depending on such measurements).
/// Boundaries explain why traversal stopped or abstracted a dependency.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Slice {
    pub target: String,
    pub definite: BTreeSet<String>,
    pub possible: BTreeSet<String>,
    pub boundaries: Vec<Boundary>,
    /// Productive hyperedges traversed by this slice. Each tail remains one
    /// atomic joint dependency; consumers must not flatten it into pairwise
    /// premise-to-head edges.
    pub steps: Vec<SliceStep>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SliceStep {
    pub head: String,
    pub tail: BTreeSet<String>,
    pub kind: ArcKind,
    pub query: Option<u64>,
    pub why: String,
}

pub struct Graph {
    pub arcs: Vec<Arc>,
    pub vertex_info: BTreeMap<String, VertexInfo>,
    pub obligations: BTreeSet<String>,
    pub premises: BTreeSet<String>,
    pub spec_obligations: BTreeSet<String>,
    /// labels seen in any core (batch or focused) — the coverage witness set
    pub covered: BTreeSet<String>,
    /// measured obligations or terminals whose label is absent from their
    /// corresponding evidence core
    pub vacuous: BTreeSet<String>,
    /// obligations with no strong evidence (focused decomposition did not run
    /// or its measurement failed): excluded from ablation deltas —
    /// unmeasured, not broken.
    pub unmeasured: BTreeSet<String>,
    /// ambient vertices (always-available roots)
    pub ambient_roots: BTreeSet<String>,
    /// Per-query aggregates of unnamed background axioms.
    ///
    /// Recorded when the vertex is created, because the analyzer must not
    /// recover a vertex's kind by parsing its transport spelling. The
    /// deleted `is_beta_vertex` did exactly that.
    pub background_roots: BTreeSet<String>,
    /// artifact id → occurrence vertices it elaborates to
    pub elaborates: BTreeMap<String, BTreeSet<String>>,
    /// artifact id → child artifact ids (artifact tree)
    pub artifact_children: BTreeMap<String, BTreeSet<String>>,
    /// every artifact id
    pub artifact_ids: BTreeSet<String>,
    /// per-call demand-refined induction outcomes (human-auditable)
    pub induction_notes: Vec<String>,
    /// ambient vertex → recorded owner (from the tap, never parsed names)
    pub ambient_owner: BTreeMap<String, String>,
    /// ambient vertex → typed installation operation
    pub ambient_op: BTreeMap<String, String>,
    /// per function: unresolved premise rows in its batch queries. Nonzero
    /// means consumption joins may be missing there — absence findings must
    /// be occluded, not asserted.
    pub unresolved_premises_of: BTreeMap<String, u64>,
    /// Premises and ambient facts available at each parent or terminal
    /// obligation. Scope is metadata, not evidence.
    pub obligation_scopes: BTreeMap<String, ObligationScope>,
    /// Exact call-site identity for each call-postcondition premise.
    call_boundaries: BTreeMap<String, CallBoundaryInfo>,
    /// Call-local licensing relations.
    demand_calls: Vec<DemandCall>,
    /// (record index, record-local artifact id) → graph vertex.
    pub artifact_vertex: BTreeMap<(usize, String), String>,
    /// artifact vertex → owning trait method, for clauses declared on a trait.
    pub trait_declared: BTreeMap<String, String>,
    /// occurrence vertex → owning function (namespaced by record when needed).
    pub function_of: BTreeMap<String, String>,
    /// Function identity → display name, and artifact vertex → owning function
    /// identity. Display only: identities stay raw paths everywhere else.
    names: Names,
}

/// Target-independent state for one call policy. Whole-package reports slice
/// thousands of terminals under the same graph and policy; rebuilding these
/// indexes and grounding fixed points per terminal is quadratic in practice.
struct PreparedSlices<'a> {
    options: SliceOptions,
    by_head: BTreeMap<&'a str, Vec<&'a Arc>>,
    demand_by_head: BTreeMap<&'a str, Vec<&'a DemandCall>>,
    definite_ranks: BTreeMap<String, usize>,
    explanation_ranks: BTreeMap<String, usize>,
}

/// Display renderings of raw-path identities.
///
/// Function identities are `FunX.path` (`crate::impl&%0::view`), which is
/// injective but not what a reader recognises. Verus's friendly rendering is
/// recognisable but not injective — it drops the impl disambiguator and the
/// self type's type arguments — so it cannot be an identity. This table keeps
/// both and renders the friendly name, appending the raw path only where the
/// friendly name is shared, so a rendering is always unambiguous.
#[derive(Default, Clone)]
struct Names {
    /// function identity → friendly name, where a friendly name was recorded.
    friendly: BTreeMap<String, String>,
    /// friendly name → how many function identities share it.
    sharers: BTreeMap<String, usize>,
    /// artifact vertex → its rendering, precomputed where it differs from the
    /// vertex. Computed at build time, where both the record-local id and its
    /// recorded owner are in hand, so nothing is recovered by splitting a
    /// namespaced vertex spelling at render time.
    artifact: BTreeMap<String, String>,
    /// record-local artifact id → owning function identity, for consumers that
    /// hold a de-namespaced id (the findings projection).
    artifact_owner: BTreeMap<String, String>,
}

impl Names {
    /// A function identity, rendered for a reader.
    fn function(&self, id: &str) -> String {
        match self.friendly.get(id) {
            // Unshared: the friendly name identifies the function on its own.
            Some(friendly) if self.sharers.get(friendly) == Some(&1) => friendly.clone(),
            Some(friendly) => format!("{friendly} ({id})"),
            None => id.to_string(),
        }
    }

    /// An artifact vertex, rendered for a reader.
    fn artifact(&self, vertex: &str) -> String {
        self.artifact.get(vertex).cloned().unwrap_or_else(|| vertex.to_string())
    }

    /// A record-local artifact id, rendered for a reader.
    fn artifact_id(&self, id: &str) -> String {
        let Some(owner) = self.artifact_owner.get(id) else {
            return id.to_string();
        };
        match id.strip_prefix(owner.as_str()) {
            Some(suffix) => format!("{}{suffix}", self.function(owner)),
            None => id.to_string(),
        }
    }
}

/// Build the verification-argument graph: the L2 fact graph, the static L3
/// licensing rules, and the call-local demand relations.
pub fn build(records: &[CoverageRecord]) -> Graph {
    let f = facts::facts(records);
    let mut licensed: Vec<Arc> = Vec::new();
    let mut demand_calls = Vec::new();
    for rf in &f.records {
        for rule in LicensingRule::ALL {
            licensed.extend(rule.arcs(rf, &f));
        }
        licensed.extend(facts::aggregate_arcs(rf));
        demand_calls.extend(licensing::demand_calls(rf));
    }

    // Display names. Built here, where each record's local artifact ids and
    // its snapshot-1 rows are both available.
    let mut names = Names::default();
    for rf in &f.records {
        for sf in &rf.record.source_functions {
            if names.friendly.insert(sf.fun.clone(), sf.friendly.clone()).is_none() {
                *names.sharers.entry(sf.friendly.clone()).or_default() += 1;
            }
        }
    }
    for rf in &f.records {
        for artifact in &rf.record.artifacts {
            let Some(suffix) = artifact.id.strip_prefix(artifact.owner.as_str()) else {
                continue;
            };
            let rendered = names.function(&artifact.owner);
            if rendered == artifact.owner {
                continue;
            }
            names.artifact_owner.insert(artifact.id.clone(), artifact.owner.clone());
            let vertex = rf.ns_artifact(&artifact.id);
            // Keep any record namespace the vertex carries.
            let prefix = &vertex[..vertex.len() - artifact.id.len()];
            names.artifact.insert(vertex.clone(), format!("{prefix}{rendered}{suffix}"));
        }
    }

    // Unmeasured obligations: no strong evidence chain reached them.
    let unmeasured: BTreeSet<String> =
        f.obligations.iter().filter(|o| !f.supported_heads.contains(*o)).cloned().collect();

    let facts::Facts {
        records: _,
        mut arcs,
        vertex_info,
        obligations,
        premises,
        spec_obligations,
        covered,
        vacuous,
        ambient_roots,
        background_roots,
        elaborates,
        artifact_children,
        artifact_group: _,
        artifact_ids,
        unresolved_premises_of,
        ambient_owner,
        ambient_op,
        obligation_scopes,
        call_boundaries,
        supported_heads: _,
        artifact_vertex,
        trait_declared,
        function_of,
    } = f;
    arcs.extend(licensed);
    // One licensing claim, one arc. Two rules can reach the same conclusion by
    // different routes — a user assert is licensed both through its shared
    // `assertion` artifact (rule 3) and through the recorded checked export
    // (rule 6) — and the same claim twice would show up as two alternative
    // justifications for one head. Keeping the first preserves the earliest
    // rule's wording; the relation is unchanged either way.
    {
        let mut seen: BTreeSet<(ArcKind, Vec<String>, Vec<String>, Option<u64>)> = BTreeSet::new();
        arcs.retain(|arc| {
            seen.insert((
                arc.kind,
                arc.tail.iter().cloned().collect(),
                arc.head.iter().cloned().collect(),
                arc.query,
            ))
        });
    }

    let mut g = Graph {
        arcs,
        vertex_info,
        obligations,
        premises,
        spec_obligations,
        covered,
        vacuous,
        unmeasured,
        ambient_roots,
        background_roots,
        elaborates,
        artifact_children,
        artifact_ids,
        induction_notes: Vec::new(),
        ambient_owner,
        ambient_op,
        unresolved_premises_of,
        obligation_scopes,
        call_boundaries,
        demand_calls,
        artifact_vertex,
        trait_declared,
        function_of,
        names,
    };
    for call in &g.demand_calls {
        if call.recursive {
            g.induction_notes.push(match &call.base {
                Some(guard) => format!(
                    "induction call {} @ {}: demand-refined from guard {}",
                    call.caller,
                    call.node.as_deref().unwrap_or("?"),
                    guard
                ),
                None => format!(
                    "induction call {} @ {}: ungrounded — missing or ambiguous decrease guard",
                    call.caller,
                    call.node.as_deref().unwrap_or("?")
                ),
            });
        }
    }
    g
}

impl Graph {
    /// The graph vertex of a record-local artifact reference.
    pub fn artifact_vertex(&self, record_index: usize, artifact: &str) -> String {
        self.artifact_vertex
            .get(&(record_index, artifact.to_string()))
            .cloned()
            .unwrap_or_else(|| artifact.to_string())
    }

    /// Roots of derivation: β, ambients, and premise occurrences with no
    /// CertifiedBy in-edge (raw facts). Certified assumptions must be
    /// re-derived through their establishment.
    pub fn roots(&self) -> BTreeSet<String> {
        let certified: BTreeSet<&String> = self
            .arcs
            .iter()
            .filter(|a| a.kind == ArcKind::CertifiedBy)
            .flat_map(|a| a.head.iter())
            .chain(self.demand_calls.iter().map(|call| &call.head))
            .collect();
        let mut roots: BTreeSet<String> = self
            .premises
            .iter()
            .filter(|p| {
                !certified.contains(*p)
                    && !self.vertex_info.get(*p).is_some_and(|info| {
                        matches!(info.emission, Some(EmissionRole::CallPostcondition { .. }))
                    })
            })
            .cloned()
            .collect();
        roots.extend(self.ambient_roots.iter().cloned());
        // Artifacts with no establishment inside the record are its axioms:
        // a requires clause of a function nobody (observed) calls is an
        // entry-point assumption; the obligation lives with unobserved
        // clients. Established artifacts (ensures clauses, lemma clauses)
        // have strong in-edges and must be re-derived.
        let established: BTreeSet<&String> =
            self.arcs.iter().filter(|a| strong(a.kind)).flat_map(|a| a.head.iter()).collect();
        for a in &self.artifact_ids {
            if !established.contains(a) {
                roots.insert(a.clone());
            }
        }
        for arc in &self.arcs {
            for t in &arc.tail {
                if self.background_roots.contains(t) {
                    roots.insert(t.clone());
                }
            }
        }
        roots
    }

    /// Strong forward fixpoint from `base`, never deriving anything in
    /// `blocked`. Arcs whose head is blocked are dead; arcs consuming a
    /// blocked vertex never fire (it is not derivable and not in base).
    pub fn forward_blocked(
        &self,
        base: &BTreeSet<String>,
        blocked: &BTreeSet<String>,
    ) -> BTreeSet<String> {
        self.forward_blocked_under(base, blocked, SliceOptions { calls: CallPolicy::Modular })
    }

    fn forward_blocked_under(
        &self,
        base: &BTreeSet<String>,
        blocked: &BTreeSet<String>,
        options: SliceOptions,
    ) -> BTreeSet<String> {
        let mut derived: BTreeSet<String> = base.difference(blocked).cloned().collect();
        loop {
            let mut grew = false;
            for arc in &self.arcs {
                if !strong(arc.kind) {
                    continue;
                }
                if arc.tail.iter().all(|t| derived.contains(t)) {
                    for h in &arc.head {
                        if blocked.contains(h) {
                            continue;
                        }
                        grew |= derived.insert(h.clone());
                    }
                }
            }
            for call in &self.demand_calls {
                if blocked.contains(&call.head) {
                    continue;
                }
                let Some(tail) = self.demand_tail(call, options) else {
                    continue;
                };
                if tail.iter().all(|vertex| derived.contains(vertex)) {
                    grew |= derived.insert(call.head.clone());
                }
            }
            if !grew {
                return derived;
            }
        }
    }

    pub fn forward(&self, base: &BTreeSet<String>) -> BTreeSet<String> {
        self.forward_blocked(base, &BTreeSet::new())
    }

    /// forward with a blocked *set* (alias for clarity at call sites).
    pub fn forward_blocked_set(
        &self,
        base: &BTreeSet<String>,
        blocked: &BTreeSet<String>,
    ) -> BTreeSet<String> {
        self.forward_blocked(base, blocked)
    }

    /// Backward closure over strong static arcs and maximally demanded calls.
    /// This is a diagnostic overapproximation; policy-aware clients should use
    /// [`backward_slice`].
    pub fn backward(&self, start: &str) -> BTreeSet<String> {
        self.candidate_closure(start, SliceOptions { calls: CallPolicy::Modular })
    }

    fn opaque_call(call: &DemandCall) -> bool {
        if !call.recursive {
            return true;
        }
        call.callee.as_deref().is_some_and(|callee| callee != call.caller)
    }

    /// Effective call tail. `None` means the call has no sound licensor (for
    /// example an unguarded recursive call).
    ///
    /// The tail is the call's licensor plus every precondition check the caller
    /// discharged at it. Restricting it to the checks whose callee `requires`
    /// clause the callee's own proof used needs a per-clause measurement of the
    /// aggregate `req%g(args)` assert; see [`DemandCall`].
    fn demand_tail(&self, call: &DemandCall, options: SliceOptions) -> Option<BTreeSet<String>> {
        if call.recursive && call.base.is_none() {
            return None;
        }
        let opaque = options.calls == CallPolicy::Opaque && Self::opaque_call(call);
        let mut tail = BTreeSet::new();
        // Ordinary opaque calls stop before the callee proof. Recursive
        // cross-function calls retain their local well-foundedness guard.
        if !opaque || call.recursive {
            tail.extend(call.base.iter().cloned());
        }
        tail.extend(call.checks.iter().cloned());
        Some(tail)
    }

    /// Maximal backward closure used to discover which demand-dependent tails
    /// may become relevant before productivity removes circular alternatives.
    fn candidate_closure(&self, target: &str, options: SliceOptions) -> BTreeSet<String> {
        let mut closure = BTreeSet::from([target.to_string()]);
        loop {
            let mut grew = false;
            for arc in &self.arcs {
                if !strong(arc.kind)
                    || !arc.head.iter().any(|head| closure.contains(head))
                    || arc.head.iter().any(|head| self.unmeasured.contains(head))
                {
                    continue;
                }
                for tail in &arc.tail {
                    grew |= closure.insert(tail.clone());
                }
            }
            for call in &self.demand_calls {
                if !closure.contains(&call.head) || self.unmeasured.contains(&call.head) {
                    continue;
                }
                if let Some(tail) = self.demand_tail(call, options) {
                    for vertex in tail {
                        grew |= closure.insert(vertex);
                    }
                }
            }
            if !grew {
                return closure;
            }
        }
    }

    /// A `CertifiedBy` arc whose head is a clause declared on a trait: the
    /// tail is the refinement checks of the recorded implementations, and the
    /// certification is relative to that set.
    fn trait_contract_boundary(&self, arc: &Arc) -> Option<Boundary> {
        if arc.kind != ArcKind::CertifiedBy || arc.head.len() != 1 {
            return None;
        }
        let head = arc.head.iter().next().unwrap();
        let trait_method = self.trait_declared.get(head)?;
        let implementations =
            arc.tail.iter().filter_map(|t| self.function_of.get(t).cloned()).collect();
        Some(Boundary::TraitContract {
            artifact: head.clone(),
            trait_method: trait_method.clone(),
            implementations,
        })
    }

    fn opaque_call_boundary(&self, call: &DemandCall, options: SliceOptions) -> Option<Boundary> {
        if options.calls != CallPolicy::Opaque || !Self::opaque_call(call) {
            return None;
        }
        let premise = &call.head;
        let boundary = self.call_boundaries.get(premise);
        Some(Boundary::Call {
            premise: premise.clone(),
            caller: call.caller.clone(),
            callee: call.callee.clone(),
            cfg_node: call.node.clone(),
            call_artifact: boundary.and_then(|boundary| boundary.call_artifact.clone()),
        })
    }

    /// Earliest derivation round for each vertex under a slicing policy.
    ///
    /// Rounds are computed synchronously. A productive justification of a
    /// head may therefore use only vertices from earlier rounds. This
    /// distinguishes a genuine grounding arc from an alternative that becomes
    /// available only by cycling back from the already-grounded head.
    fn slice_ranks(
        &self,
        base: &BTreeSet<String>,
        options: SliceOptions,
    ) -> BTreeMap<String, usize> {
        let mut ranks: BTreeMap<String, usize> =
            base.iter().cloned().map(|vertex| (vertex, 0)).collect();
        let mut round = 1usize;
        loop {
            let mut additions: BTreeSet<String> = BTreeSet::new();
            for arc in &self.arcs {
                if !strong(arc.kind) {
                    continue;
                }
                if arc.tail.iter().all(|vertex| ranks.contains_key(vertex)) {
                    for head in &arc.head {
                        if !ranks.contains_key(head) {
                            additions.insert(head.clone());
                        }
                    }
                }
            }
            for call in &self.demand_calls {
                let Some(tail) = self.demand_tail(call, options) else {
                    continue;
                };
                if tail.iter().all(|vertex| ranks.contains_key(vertex))
                    && !ranks.contains_key(&call.head)
                {
                    additions.insert(call.head.clone());
                }
            }
            if additions.is_empty() {
                return ranks;
            }
            for vertex in additions {
                ranks.insert(vertex, round);
            }
            round += 1;
        }
    }

    fn slice_arc_is_productive(
        &self,
        arc: &Arc,
        head: &str,
        ranks: &BTreeMap<String, usize>,
    ) -> bool {
        let Some(head_rank) = ranks.get(head) else { return false };
        arc.tail
            .iter()
            .all(|vertex| ranks.get(vertex).is_some_and(|tail_rank| tail_rank < head_rank))
    }

    fn demand_is_productive(
        &self,
        call: &DemandCall,
        tail: &BTreeSet<String>,
        ranks: &BTreeMap<String, usize>,
    ) -> bool {
        let Some(head_rank) = ranks.get(&call.head) else { return false };
        tail.iter().all(|vertex| ranks.get(vertex).is_some_and(|tail_rank| tail_rank < head_rank))
    }

    fn prepare_slices(&self, options: SliceOptions) -> PreparedSlices<'_> {
        let mut by_head: BTreeMap<&str, Vec<&Arc>> = BTreeMap::new();
        for arc in &self.arcs {
            if !strong(arc.kind) {
                continue;
            }
            for head in &arc.head {
                by_head.entry(head.as_str()).or_default().push(arc);
            }
        }
        let mut demand_by_head: BTreeMap<&str, Vec<&DemandCall>> = BTreeMap::new();
        for call in &self.demand_calls {
            demand_by_head.entry(call.head.as_str()).or_default().push(call);
        }
        let roots = self.roots();
        let definite_ranks = self.slice_ranks(&roots, options);
        let mut explanation_roots = roots;
        explanation_roots.extend(self.unmeasured.iter().cloned());
        let explanation_ranks = self.slice_ranks(&explanation_roots, options);
        PreparedSlices { options, by_head, demand_by_head, definite_ranks, explanation_ranks }
    }

    fn backward_slice_prepared(&self, target: &str, prepared: &PreparedSlices<'_>) -> Slice {
        // One pass. A call's tail is fixed by the graph, not by the slice under
        // construction, so re-scanning cannot add a vertex. Refining a tail by
        // which callee `requires` hypotheses the slice has reached would make
        // it monotone in the slice and need a fixed point here; that refinement
        // needs a per-clause measurement v0.1 does not take
        // (`licensing::DemandCall`).
        {
            let mut definite = BTreeSet::new();
            let mut possible = BTreeSet::new();
            let mut boundaries: BTreeSet<Boundary> = BTreeSet::new();
            let mut steps: BTreeSet<SliceStep> = BTreeSet::new();
            let mut seen = BTreeSet::new();
            let mut stack = vec![target.to_string()];

            while let Some(vertex) = stack.pop() {
                if !seen.insert(vertex.clone()) {
                    continue;
                }
                if self.unmeasured.contains(&vertex) {
                    possible.insert(vertex.clone());
                    if let Some(scope) = self.obligation_scopes.get(&vertex) {
                        possible.extend(scope.available.iter().cloned());
                        possible.extend(scope.ambients.iter().cloned());
                        boundaries.insert(Boundary::Unmeasured {
                            vertex,
                            solver_context: scope.solver_context,
                            terminal_path: scope.terminal_path.clone(),
                        });
                    } else {
                        boundaries.insert(Boundary::Unmeasured {
                            vertex,
                            solver_context: 0,
                            terminal_path: None,
                        });
                    }
                    continue;
                }

                let ranks = if prepared.definite_ranks.contains_key(&vertex) {
                    definite.insert(vertex.clone());
                    &prepared.definite_ranks
                } else if prepared.explanation_ranks.contains_key(&vertex) {
                    possible.insert(vertex.clone());
                    &prepared.explanation_ranks
                } else {
                    possible.insert(vertex.clone());
                    boundaries.insert(Boundary::Ungrounded { vertex });
                    continue;
                };

                if let Some(arcs) = prepared.by_head.get(vertex.as_str()) {
                    for arc in arcs {
                        if !self.slice_arc_is_productive(arc, &vertex, ranks) {
                            continue;
                        }
                        if let Some(boundary) = self.trait_contract_boundary(arc) {
                            boundaries.insert(boundary);
                        }
                        steps.insert(SliceStep {
                            head: vertex.clone(),
                            tail: arc.tail.clone(),
                            kind: arc.kind,
                            query: arc.query,
                            why: arc.why.clone(),
                        });
                        stack.extend(arc.tail.iter().cloned());
                    }
                }
                if let Some(calls) = prepared.demand_by_head.get(vertex.as_str()) {
                    for call in calls {
                        let Some(tail) = self.demand_tail(call, prepared.options) else {
                            continue;
                        };
                        if !self.demand_is_productive(call, &tail, ranks) {
                            continue;
                        }
                        if let Some(boundary) = self.opaque_call_boundary(call, prepared.options) {
                            boundaries.insert(boundary);
                        }
                        steps.insert(SliceStep {
                            head: vertex.clone(),
                            tail: tail.clone(),
                            kind: ArcKind::Demand,
                            query: call.query,
                            why: if call.recursive {
                                format!(
                                    "call-local induction at {}: decrease guard + precondition checks",
                                    call.node.as_deref().unwrap_or("?")
                                )
                            } else {
                                format!(
                                    "call-local contract at {}: callee proof + precondition checks",
                                    call.node.as_deref().unwrap_or("?")
                                )
                            },
                        });
                        stack.extend(tail);
                    }
                }
            }

            possible.retain(|vertex| !definite.contains(vertex));
            Slice {
                target: target.to_string(),
                definite,
                possible,
                boundaries: boundaries.into_iter().collect(),
                steps: steps.into_iter().collect(),
            }
        }
    }

    /// Compute a policy-aware backward slice.
    ///
    /// Definite traversal follows only productive strong arcs: every tail was
    /// grounded strictly before its head. This excludes closed cyclic
    /// alternatives while preserving all alternatives that participated in
    /// the head's earliest grounding round.
    ///
    /// Unmeasured focused terminals are treated as epistemic boundaries. They
    /// are never added to `definite`; instead their emitted `available` scope
    /// and every ambient installed in the same solver context are added to
    /// `possible`. A partially measured conjunction can therefore retain the
    /// definite slice of its measured terminals while conservatively exposing
    /// the scope of its opaque terminals.
    pub fn backward_slice(&self, target: &str, options: SliceOptions) -> Slice {
        let prepared = self.prepare_slices(options);
        self.backward_slice_prepared(target, &prepared)
    }

    /// Slice many targets under one policy.
    pub fn backward_slices<I>(&self, targets: I, options: SliceOptions) -> BTreeMap<String, Slice>
    where
        I: IntoIterator<Item = String>,
    {
        let prepared = self.prepare_slices(options);
        targets
            .into_iter()
            .map(|target| {
                let slice = self.backward_slice_prepared(&target, &prepared);
                (target, slice)
            })
            .collect()
    }

    /// Forward reach: every vertex that some productive strong arc chain
    /// connects to `seed` under the slicing policy. This is the may-depend
    /// relation — a head is reached when *any* member of an arc's tail is
    /// reached — so it is plain reachability, not the grounding fixed point.
    /// Witness-relative like everything else: it says which heads' observed
    /// arguments mention the seed somewhere in their tails.
    pub fn forward_reach(
        &self,
        seed: &BTreeSet<String>,
        options: SliceOptions,
    ) -> BTreeSet<String> {
        let roots = self.roots();
        let ranks = self.slice_ranks(&roots, options);
        let mut reached: BTreeSet<String> = seed.clone();
        loop {
            let mut grew = false;
            for arc in &self.arcs {
                if !strong(arc.kind) {
                    continue;
                }
                if !arc.tail.iter().any(|t| reached.contains(t)) {
                    continue;
                }
                for head in &arc.head {
                    if !self.slice_arc_is_productive(arc, head, &ranks) {
                        continue;
                    }
                    grew |= reached.insert(head.clone());
                }
            }
            for call in &self.demand_calls {
                let Some(tail) = self.demand_tail(call, options) else {
                    continue;
                };
                if tail.iter().any(|vertex| reached.contains(vertex))
                    && self.demand_is_productive(call, &tail, &ranks)
                {
                    grew |= reached.insert(call.head.clone());
                }
            }
            if !grew {
                return reached;
            }
        }
    }

    /// The seed of a forward query: an artifact expands to everything it
    /// elaborates to (its clauses and their occurrences); a vertex is itself.
    pub fn forward_seed(&self, target: &str) -> BTreeSet<String> {
        if self.elaborates.contains_key(target) || self.artifact_children.contains_key(target) {
            self.elaboration_of(target)
        } else {
            BTreeSet::from([target.to_string()])
        }
    }

    /// Everything an artifact elaborates to, including through its child
    /// artifacts (deleting an aggregate deletes its clauses).
    pub fn elaboration_of(&self, artifact: &str) -> BTreeSet<String> {
        let mut arts: BTreeSet<String> = BTreeSet::from([artifact.to_string()]);
        loop {
            let mut grew = false;
            for a in arts.clone() {
                if let Some(kids) = self.artifact_children.get(&a) {
                    for k in kids {
                        grew |= arts.insert(k.clone());
                    }
                }
            }
            if !grew {
                break;
            }
        }
        let mut out: BTreeSet<String> = BTreeSet::new();
        for a in &arts {
            if let Some(occs) = self.elaborates.get(a) {
                out.extend(occs.iter().cloned());
            }
        }
        out.extend(arts);
        out
    }

    /// Ablate a vertex. For an artifact: delete it, its child artifacts, and
    /// every occurrence it elaborates to — its own generated obligations are
    /// deleted, not broken, and are never reported. For an occurrence label:
    /// delete just that vertex. Returns the surviving obligations that were
    /// derivable before and are not after (measured obligations only).
    pub fn ablate(&self, vertex: &str) -> BTreeSet<String> {
        let blocked = if self.elaborates.contains_key(vertex)
            || self.artifact_children.contains_key(vertex)
        {
            self.elaboration_of(vertex)
        } else {
            BTreeSet::from([vertex.to_string()])
        };
        let roots = self.roots();
        let options = SliceOptions { calls: CallPolicy::Modular };
        let full = self.forward_blocked_under(&roots, &BTreeSet::new(), options);
        let without = self.forward_blocked_under(&roots, &blocked, options);
        self.obligations
            .iter()
            .filter(|o| {
                !blocked.contains(*o)
                    && !self.unmeasured.contains(*o)
                    && full.contains(*o)
                    && !without.contains(*o)
            })
            .cloned()
            .collect()
    }

    /// Typed-graph invariants. CertifiedBy heads must be premises or
    /// artifacts, never obligations (a check cannot be conjured by another
    /// check; it needs evidence). SupportedBy heads must not be premises.
    pub fn check(&self) -> Vec<String> {
        let mut v = Vec::new();
        for arc in &self.arcs {
            match arc.kind {
                ArcKind::CertifiedBy => {
                    for h in &arc.head {
                        if self.obligations.contains(h) {
                            v.push(format!("CertifiedBy head {} is an obligation", h));
                        }
                    }
                }
                ArcKind::SupportedBy => {
                    for h in &arc.head {
                        if self.premises.contains(h) {
                            v.push(format!("SupportedBy head {} is a premise", h));
                        }
                    }
                }
                ArcKind::ObservedInBatch => {
                    if arc.head.is_empty() {
                        v.push("ObservedInBatch has an empty obligation set".to_string());
                    }
                    for h in &arc.head {
                        if !self.obligations.contains(h) {
                            v.push(format!("ObservedInBatch head {} is not an obligation", h));
                        }
                    }
                    for t in &arc.tail {
                        if self.obligations.contains(t) {
                            v.push(format!("ObservedInBatch tail {} is an obligation", t));
                        }
                    }
                }
                _ => {}
            }
        }
        v
    }

    /// Display projection (final display operation, never used in
    /// construction): map an occurrence vertex to `artifact @ phase`, and an
    /// ambient vertex to its recorded owner and typed installation op. The
    /// identity comes from the ambient tap (`AmbientRecord`), never from
    /// parsing the label.
    /// A function identity, rendered for a reader: the friendly name, with the
    /// raw path appended where the friendly name is shared by several
    /// functions. Never a join key.
    pub fn display_function(&self, id: &str) -> String {
        self.names.function(id)
    }

    /// A record-local artifact id, rendered for a reader: its owner prefix
    /// replaced by [`Graph::display_function`]. Never a join key.
    pub fn display_artifact(&self, id: &str) -> String {
        self.names.artifact_id(id)
    }

    /// A vertex, citing identities. This is the audit rendering: `explain` and
    /// `summary` name the raw paths their justifications are keyed on.
    pub fn display(&self, v: &str) -> String {
        self.render(v, false)
    }

    /// A vertex, rendered for a reader: friendly function names, disambiguated
    /// by raw path where a friendly name is shared. This is the research
    /// rendering used by the study text and the findings.
    pub fn display_friendly(&self, v: &str) -> String {
        self.render(v, true)
    }

    fn render(&self, v: &str, friendly: bool) -> String {
        let function = |id: &str| {
            if friendly { self.names.function(id) } else { id.to_string() }
        };
        let artifact = |id: &str| {
            if friendly { self.names.artifact(id) } else { id.to_string() }
        };
        if let Some(owner) = self.ambient_owner.get(v) {
            let op = self.ambient_op.get(v).map(String::as_str).unwrap_or("?");
            return format!("{}  [ambient:{}] {}", function(owner), op, v);
        }
        match self.vertex_info.get(v) {
            Some(i) => {
                let core = match (&i.artifact, &i.phase) {
                    (Some(a), Some(p)) => format!("{} @ {}", artifact(a), p),
                    (Some(a), None) => artifact(a),
                    _ => v.to_string(),
                };
                let span = i.span.as_deref().unwrap_or("");
                if i.detail.is_empty() {
                    format!("{}  {}", core, span)
                } else {
                    format!("{}  [{}] {}", core, i.detail, span)
                }
            }
            None => v.to_string(),
        }
    }
}

// ── explanation traces ────────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Status {
    Complete,
    Partial,
    Unmeasured,
    /// Not derivable from the graph's roots: every candidate justification
    /// is circular (e.g. a recursive contract certifying itself) or
    /// otherwise disconnected from ground facts. A Complete/Partial status
    /// is only ever assigned to forward-derivable vertices.
    Ungrounded,
}

impl Graph {
    /// An AND/OR derivation of `target`, printed as a finite shared DAG:
    /// every vertex appears once with a numeric id; alternatives (distinct
    /// supporting arcs) are ORs; the tail of one arc is an AND. Only strong
    /// arcs participate — ObservedInBatch is never proof dependence. Every
    /// step cites its justification (protocol instance or focused query) and
    /// every leaf cites its attribution/join rules. Status: Complete (all
    /// leaves attributed), Partial (derivable but some leaf unresolved or
    /// some provenance missing), Unmeasured (an obligation in the chain has
    /// no strong evidence).
    pub fn explain(&self, target: &str) -> String {
        let options = SliceOptions { calls: CallPolicy::Modular };
        let slice = self.backward_slice(target, options);
        let explanation_arcs: Vec<Arc> = slice
            .steps
            .iter()
            .map(|step| Arc {
                tail: step.tail.clone(),
                head: BTreeSet::from([step.head.clone()]),
                kind: step.kind,
                query: step.query,
                why: step.why.clone(),
            })
            .collect();
        // Productive arcs by head for this target-specific demand fixed point.
        let mut by_head: BTreeMap<&str, Vec<&Arc>> = BTreeMap::new();
        for arc in &explanation_arcs {
            for h in &arc.head {
                by_head.entry(h.as_str()).or_default().push(arc);
            }
        }
        // the DAG slice: backward closure, with stable ids in first-visit order
        let mut ids: BTreeMap<String, usize> = BTreeMap::new();
        let mut order: Vec<String> = Vec::new();
        let mut stack = vec![target.to_string()];
        while let Some(v) = stack.pop() {
            if ids.contains_key(&v) {
                continue;
            }
            ids.insert(v.clone(), ids.len() + 1);
            order.push(v.clone());
            if let Some(arcs) = by_head.get(v.as_str()) {
                for arc in arcs {
                    for t in &arc.tail {
                        if !ids.contains_key(t) {
                            stack.push(t.clone());
                        }
                    }
                }
            }
        }
        // Explanation grounding distinguishes two reasons why ordinary
        // derivation may stop:
        //
        // - an explicitly unmeasured obligation is an opaque evidence
        //   boundary, not a circular justification;
        // - everything else that is not derivable from real roots is
        //   Ungrounded.
        //
        // Treat unmeasured obligations as leaves only for explanation-status
        // propagation.  Graph::forward, certification, and ablation continue
        // to use real roots, so no proof dependence is invented.
        let mut explanation_roots = self.roots();
        explanation_roots.extend(self.unmeasured.iter().cloned());
        let mut demanded = BTreeSet::from([target.to_string()]);
        for step in &slice.steps {
            demanded.insert(step.head.clone());
            demanded.extend(step.tail.iter().cloned());
        }
        let grounded: BTreeSet<String> =
            self.slice_ranks(&explanation_roots, options).into_keys().collect();
        let mut status: BTreeMap<&str, Status> = BTreeMap::new();
        for v in &order {
            if !grounded.contains(v) {
                status.insert(v.as_str(), Status::Ungrounded);
                continue;
            }
            let s = if let Some(i) = self.vertex_info.get(v) {
                if i.unresolved { Status::Partial } else { Status::Complete }
            } else {
                Status::Complete // β / ambient / artifact vertices
            };
            let s = if self.unmeasured.contains(v) { Status::Unmeasured } else { s };
            let s = if self.obligations.contains(v)
                && !by_head.contains_key(v.as_str())
                && !self.unmeasured.contains(v)
            {
                // obligation inside the slice with no strong in-arcs at all
                Status::Unmeasured
            } else {
                s
            };
            status.insert(v.as_str(), s);
        }
        loop {
            let mut changed = false;
            for v in &order {
                if status.get(v.as_str()) == Some(&Status::Ungrounded) {
                    continue; // pinned by grounding
                }
                let Some(arcs) = by_head.get(v.as_str()) else { continue };
                // OR over arcs: best arc; AND within arc: worst tail member
                let mut best = Status::Unmeasured;
                for arc in arcs {
                    let worst = arc
                        .tail
                        .iter()
                        .map(|t| status.get(t.as_str()).copied().unwrap_or(Status::Complete))
                        .max()
                        .unwrap_or(Status::Complete);
                    if worst < best {
                        best = worst;
                    }
                }
                // combine with own leaf status (an unresolved head stays ≥ Partial)
                let own = if self.vertex_info.get(v).map(|i| i.unresolved).unwrap_or(false) {
                    Status::Partial
                } else {
                    Status::Complete
                };
                let new = best.max(own);
                if status.get(v.as_str()) != Some(&new) {
                    status.insert(v.as_str(), new);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        let mut out = String::new();
        let overall = status.get(target).copied().unwrap_or(Status::Unmeasured);
        out.push_str(&format!("explain {}  —  {:?}\n", target, overall));
        for v in &order {
            let id = ids[v];
            let st = status.get(v.as_str()).copied().unwrap_or(Status::Complete);
            out.push_str(&format!("#{} {}  —  {:?}\n", id, self.display(v), st));
            // provenance line for occurrence vertices
            if let Some(i) = self.vertex_info.get(v) {
                if let Some(a) = &i.artifact {
                    out.push_str(&format!(
                        "    provenance: elaborates from {}{}{}\n",
                        a,
                        i.rule
                            .as_deref()
                            .map(|r| format!("  [attribution: {}]", r))
                            .unwrap_or_default(),
                        i.join_rule
                            .as_deref()
                            .map(|r| format!("  [join: {}]", r))
                            .unwrap_or_default(),
                    ));
                } else if let Some(r) = &i.rule {
                    out.push_str(&format!("    provenance: [attribution: {}]\n", r));
                } else if i.unresolved {
                    out.push_str("    provenance: UNRESOLVED (honesty ledger)\n");
                }
            }
            if status.get(v.as_str()) == Some(&Status::Ungrounded) {
                out.push_str(
                    "    UNGROUNDED: not derivable from roots — every candidate justification is circular or disconnected\n",
                );
            }
            if let Some(owner) = self.ambient_owner.get(v) {
                let op = self.ambient_op.get(v).map(String::as_str).unwrap_or("unknown");
                out.push_str(&format!("    ambient encoding axiom ({op}), owner {owner}\n"));
            }
            match by_head.get(v.as_str()) {
                None => {
                    if self.obligations.contains(v) {
                        out.push_str("    UNMEASURED: no strong evidence (batch witness, if any, is not proof dependence)\n");
                    } else {
                        out.push_str("    root\n");
                    }
                }
                Some(arcs) => {
                    for (k, arc) in arcs.iter().enumerate() {
                        let refs: Vec<String> =
                            arc.tail.iter().map(|t| format!("#{}", ids[t])).collect();
                        let conj = refs.join(" AND ");
                        if arcs.len() > 1 {
                            out.push_str(&format!(
                                "    alt {}: ← {} [{}: {}]\n",
                                k + 1,
                                conj,
                                arc.kind,
                                arc.why
                            ));
                        } else {
                            out.push_str(&format!("    ← {} [{}: {}]\n", conj, arc.kind, arc.why));
                        }
                    }
                }
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::record::{
        AmbientRecord, Artifact, ArtifactKind, AssertionPoint, FunctionRecord, Occurrence, Origin,
        QueryFamily, QueryRecord, SolverConfigRecord,
    };

    /// Test rows name their protocol position by the legacy phase string;
    /// this maps it back onto the typed role the analyzer quantifies over.
    /// Call-contract roles need a callee, which the tests set afterwards via
    /// `with_callee`; `call.pre`/`call.post` here use a placeholder.
    fn role_of_phase(phase: &str) -> EmissionRole {
        match phase {
            "function.ensures" => EmissionRole::FunctionEnsures,
            "assert.check" => EmissionRole::Assertion { point: AssertionPoint::Check },
            "assert.establish" => EmissionRole::Assertion { point: AssertionPoint::Establish },
            "call.pre" => EmissionRole::CallPrecondition { callee: Some("t::callee".into()) },
            "call.post" => EmissionRole::CallPostcondition { callee: "t::callee".into() },
            other => panic!("test phase {other} has no role mapping"),
        }
    }

    fn occ(role: Role, label: &str, art: Option<&str>, phase: Option<&str>) -> Occurrence {
        Occurrence {
            path: String::new(),
            role,
            carrier: Carrier::Assume,
            origin: Origin { kind: OriginKind::Source, detail: "test".into() },
            emission: phase.map(role_of_phase),
            span: None,
            assert_id: None,
            shape: None,
            label: Some(label.into()),
            node: None,
            artifact: art.map(|s| s.to_string()),
            rule: Some("test.rule".into()),
            join_rule: art.map(|_| "test.join".into()),
            sig: None,
            emitted: None,
            lowering_node: None,
            subject_fn: None,
        }
    }

    fn record(queries: Vec<QueryRecord>, artifacts: Vec<Artifact>) -> CoverageRecord {
        CoverageRecord {
            schema: crate::record::SCHEMA.into(),
            artifact_version: "0.1".into(),
            queries,
            artifacts,
            ..Default::default()
        }
    }

    /// One place carries the full query field list, so a new schema field
    /// surfaces here once instead of in every test constructor.
    fn base_query(id: u64, family: QueryFamily) -> QueryRecord {
        QueryRecord {
            id,
            family,
            parent: None,
            parent_obligation_label: None,
            target_label: None,
            terminal_path: None,
            function_variant: None,
            solver_context: 0,
            solver_config: SolverConfigRecord::default(),
            fun: "t::f".into(),
            desc: "test".into(),
            span: "test.rs:1".into(),
            ambient_batches: 0,
            available: vec![],
            occurrences: vec![],
            results: vec![],
            shadow_result: Some("valid".into()),
            evidence_backend: Some("unsat_core".into()),
            core: None,
        }
    }

    fn cores(core: Vec<&str>) -> Option<Vec<String>> {
        Some(core.iter().map(|s| s.to_string()).collect())
    }

    fn q(id: u64, occs: Vec<Occurrence>, core: Vec<&str>) -> QueryRecord {
        QueryRecord { occurrences: occs, core: cores(core), ..base_query(id, QueryFamily::Batch) }
    }

    fn focused(id: u64, target: &str, parent: &str, core: Vec<&str>) -> QueryRecord {
        QueryRecord {
            target_label: Some(target.into()),
            parent_obligation_label: Some(parent.into()),
            core: cores(core),
            ..base_query(id, QueryFamily::Focused)
        }
    }

    fn focused_unmeasured(id: u64, target: &str, parent: &str) -> QueryRecord {
        QueryRecord {
            target_label: Some(target.into()),
            parent_obligation_label: Some(parent.into()),
            core: None,
            shadow_result: Some("canceled".into()),
            evidence_backend: None,
            ..base_query(id, QueryFamily::Focused)
        }
    }

    /// A closed contract cycle must be Ungrounded, never Complete: the
    /// obligation's only support is a premise certified by an aggregate
    /// certified by that same obligation.
    #[test]
    fn circular_certification_is_ungrounded() {
        let agg = "t::f#ens";
        let mut batch = q(
            0,
            vec![
                occ(Role::Premise, "pc%0%0", Some(agg), None),
                occ(Role::Obligation, "pc%0%1", Some(agg), Some("function.ensures")),
            ],
            vec!["pc%0%0", "pc%0%1"],
        );
        batch.occurrences[0].emission =
            Some(EmissionRole::CallPostcondition { callee: "t::f".into() });
        let f = focused(1, "pc%0%t%1%0", "pc%0%1", vec!["pc%0%0", "pc%0%t%1%0"]);
        let arts = vec![Artifact {
            id: agg.into(),
            kind: ArtifactKind::EnsuresAggregate,
            owner: "t::f".into(),
            parent: None,
            span: None,
            callee: None,
            cfg_node: None,
            group: None,
        }];
        let g = build(&[record(vec![batch, f], arts)]);
        let out = g.explain("pc%0%1");
        assert!(out.starts_with("explain pc%0%1  —  Ungrounded"), "cycle not detected:\n{}", out);
        assert!(out.contains("UNGROUNDED: not derivable"));
    }

    /// Grounded chains keep their statuses: a fully attributed chain is
    /// Complete; an unresolved leaf makes its chain Partial (and only its
    /// chain).
    #[test]
    fn grounded_statuses_unchanged() {
        let mut batch = q(
            0,
            vec![
                occ(Role::Premise, "pc%0%0", None, None),
                occ(Role::Obligation, "pc%0%1", None, None),
                occ(Role::Premise, "pc%0%2", None, None),
                occ(Role::Obligation, "pc%0%3", None, None),
            ],
            vec!["pc%0%0", "pc%0%1", "pc%0%2", "pc%0%3"],
        );
        batch.occurrences[2].origin.kind = OriginKind::Unresolved;
        batch.occurrences[2].rule = None;
        let f1 = focused(1, "pc%0%t%1%0", "pc%0%1", vec!["pc%0%0", "pc%0%t%1%0"]);
        let f2 = focused(2, "pc%0%t%3%0", "pc%0%3", vec!["pc%0%2", "pc%0%t%3%0"]);
        let g = build(&[record(vec![batch, f1, f2], vec![])]);
        let clean = g.explain("pc%0%1");
        assert!(clean.starts_with("explain pc%0%1  —  Complete"), "{}", clean);
        let dirty = g.explain("pc%0%3");
        assert!(dirty.starts_with("explain pc%0%3  —  Partial"), "{}", dirty);
        assert!(dirty.contains("UNRESOLVED"));
    }

    #[test]
    fn focused_target_present_creates_supported_by_edge() {
        let target = "pc%0%t%1%0";
        let parent = "pc%0%1";
        let premise = "pc%0%0";
        let batch = q(
            0,
            vec![
                occ(Role::Premise, premise, None, None),
                occ(Role::Obligation, parent, None, None),
            ],
            vec![premise, parent],
        );
        let measurement = focused(1, target, parent, vec![premise, target]);
        let g = build(&[record(vec![batch, measurement], vec![])]);

        let support: Vec<&Arc> = g
            .arcs
            .iter()
            .filter(|arc| arc.kind == ArcKind::SupportedBy && arc.head.contains(target))
            .collect();
        assert_eq!(support.len(), 1);
        assert_eq!(support[0].query, Some(1));
        assert!(support[0].tail.contains(premise));
        let slice = g.backward_slice(target, SliceOptions { calls: CallPolicy::Modular });
        let witness = slice
            .steps
            .iter()
            .find(|step| step.kind == ArcKind::SupportedBy && step.head == target)
            .expect("focused witness must be retained in the slice");
        assert_eq!(witness.tail, support[0].tail);
        assert_eq!(witness.query, Some(1));
        assert!(!g.vacuous.contains(target));
        assert!(!g.unmeasured.contains(target));
        assert!(g.covered.contains(target));
    }

    #[test]
    fn focused_target_absent_is_measured_vacuous_without_supported_by_edge() {
        let target = "pc%0%t%1%0";
        let parent = "pc%0%1";
        let premise = "pc%0%0";
        let batch = q(
            0,
            vec![
                occ(Role::Premise, premise, None, None),
                occ(Role::Obligation, parent, None, None),
            ],
            vec![premise, parent],
        );
        let measurement = focused(1, target, parent, vec![premise]);
        let g = build(&[record(vec![batch, measurement], vec![])]);

        assert!(
            !g.arcs.iter().any(|arc| arc.kind == ArcKind::SupportedBy && arc.head.contains(target))
        );
        assert!(g.vacuous.contains(target));
        assert!(!g.unmeasured.contains(target));
        assert!(!g.covered.contains(target));
        assert!(g.arcs.iter().any(|arc| {
            arc.kind == ArcKind::TerminalOf
                && arc.head.contains(parent)
                && arc.tail.contains(target)
        }));
    }

    /// Every terminal belongs to its parent conjunction even when its focused
    /// solve is canceled or otherwise unmeasured.  The measured sibling must
    /// not make the parent look fully supported.
    #[test]
    fn unmeasured_focused_terminal_is_not_dropped() {
        let batch = q(0, vec![occ(Role::Obligation, "pc%0%1", None, None)], vec!["pc%0%1"]);
        let measured = focused(1, "pc%0%t%1%0", "pc%0%1", vec!["pc%0%t%1%0"]);
        let opaque = focused_unmeasured(2, "pc%0%t%1%1", "pc%0%1");
        let g = build(&[record(vec![batch, measured, opaque], vec![])]);

        assert!(g.unmeasured.contains("pc%0%t%1%1"));
        let out = g.explain("pc%0%1");
        assert!(out.starts_with("explain pc%0%1  —  Unmeasured"), "{}", out);
        assert!(out.contains("pc%0%t%1%1"));
        assert!(out.contains("UNMEASURED: no strong evidence"));
        assert!(!out.contains("UNGROUNDED:"), "measurement failure is not a proof cycle:\n{}", out);
    }

    #[test]
    fn multi_record_beta_vertices_remain_roots() {
        let make = || record(vec![focused(1, "pc%1%t%0%0", "pc%0%0", vec!["pc%1%t%0%0"])], vec![]);
        let g = build(&[make(), make()]);
        let roots = g.roots();
        assert!(roots.contains("r0%β:1"));
        assert!(roots.contains("r1%β:1"));
        let derived = g.forward(&roots);
        assert!(derived.contains("r0%pc%1%t%0%0"));
        assert!(derived.contains("r1%pc%1%t%0%0"));
    }

    #[test]
    fn multi_record_artifact_ids_are_namespaced() {
        let artifact = || Artifact {
            id: "crate::f#req[0]".into(),
            kind: ArtifactKind::RequiresClause,
            owner: "crate::f".into(),
            parent: None,
            span: Some("f.rs:2:5".into()),
            callee: None,
            cfg_node: None,
            group: None,
        };
        let records =
            vec![record(Vec::new(), vec![artifact()]), record(Vec::new(), vec![artifact()])];
        let graph = build(&records);

        assert!(graph.artifact_ids.contains("r0%crate::f#req[0]"));
        assert!(graph.artifact_ids.contains("r1%crate::f#req[0]"));
        assert!(!graph.artifact_ids.contains("crate::f#req[0]"));
    }

    #[test]
    fn unmeasured_slice_overapproximates_available_and_context_ambients() {
        let batch = q(
            0,
            vec![
                occ(Role::Premise, "pc%0%0", None, None),
                occ(Role::Premise, "pc%0%1", None, None),
                occ(Role::Obligation, "pc%0%2", None, None),
            ],
            vec!["pc%0%0", "pc%0%1", "pc%0%2"],
        );
        let mut opaque = focused_unmeasured(1, "pc%0%t%2%0", "pc%0%2");
        opaque.solver_context = 7;
        opaque.terminal_path = Some("q.a1".into());
        opaque.available = vec!["pc%0%0".into(), "pc%0%1".into(), "pc%0%t%2%0".into()];
        let mut r = record(vec![batch, opaque], vec![]);
        r.ambients = vec![
            AmbientRecord {
                label: "ambient%7".into(),
                owner: "t::ambient7".into(),
                op: "ReqEns".into(),
                solver_contexts: vec![7],
            },
            AmbientRecord {
                label: "ambient%8".into(),
                owner: "t::ambient8".into(),
                op: "ReqEns".into(),
                solver_contexts: vec![8],
            },
        ];
        let g = build(&[r]);
        let slice = g.backward_slice("pc%0%t%2%0", SliceOptions { calls: CallPolicy::Modular });
        let parent = g.backward_slice("pc%0%2", SliceOptions { calls: CallPolicy::Modular });
        let batch = g.backward_slices(
            ["pc%0%t%2%0".to_string(), "pc%0%2".to_string()],
            SliceOptions { calls: CallPolicy::Modular },
        );
        assert_eq!(batch["pc%0%t%2%0"], slice);
        assert_eq!(batch["pc%0%2"], parent);

        assert!(slice.definite.is_empty());
        assert_eq!(
            slice.possible,
            BTreeSet::from([
                "ambient%7".to_string(),
                "pc%0%0".to_string(),
                "pc%0%1".to_string(),
                "pc%0%t%2%0".to_string(),
            ])
        );
        assert_eq!(
            slice.boundaries,
            vec![Boundary::Unmeasured {
                vertex: "pc%0%t%2%0".into(),
                solver_context: 7,
                terminal_path: Some("q.a1".into()),
            }]
        );
    }

    /// Assert protocol: an established assumption is licensed by its own
    /// discharged check (shared `assertion` artifact, phases assert.check /
    /// assert.establish), so a terminal observing the established fact
    /// transitively reaches the facts that discharged the check. The cycle
    /// guard still applies: the certificate cannot ground itself.
    #[test]
    fn assert_certificate_reaches_the_checks_own_support() {
        let assert_art = "t::f#assert@n1";
        let batch = q(
            0,
            vec![
                occ(Role::Premise, "pc%0%0", None, None),
                occ(Role::Obligation, "pc%0%1", Some(assert_art), Some("assert.check")),
                occ(Role::Premise, "pc%0%2", Some(assert_art), Some("assert.establish")),
                occ(Role::Obligation, "pc%0%3", None, None),
            ],
            vec!["pc%0%0", "pc%0%1", "pc%0%2", "pc%0%3"],
        );
        // The check's own focused evidence: the plain premise.
        let check = focused(1, "pc%0%t%1%0", "pc%0%1", vec!["pc%0%0", "pc%0%t%1%0"]);
        // The postcondition observes only the established fact.
        let post = focused(2, "pc%0%t%3%0", "pc%0%3", vec!["pc%0%2", "pc%0%t%3%0"]);
        let g = build(&[record(vec![batch, check, post], vec![])]);

        let slice = g.backward_slice("pc%0%t%3%0", SliceOptions { calls: CallPolicy::Modular });
        // direct: the established fact; transitive through the certificate:
        // the check obligation, its terminal, and the check's own support.
        for vertex in ["pc%0%2", "pc%0%1", "pc%0%t%1%0", "pc%0%0"] {
            assert!(slice.definite.contains(vertex), "slice must reach {vertex}");
        }
        assert!(slice.possible.is_empty());
        assert!(slice.boundaries.is_empty());
        assert!(slice.steps.iter().any(|step| step.kind == ArcKind::CertifiedBy
            && step.head == "pc%0%2"
            && step.tail == BTreeSet::from(["pc%0%1".to_string()])));
    }

    #[test]
    fn slice_excludes_closed_cycle_alternative_to_grounded_support() {
        let batch = q(
            0,
            vec![
                occ(Role::Premise, "pc%0%0", None, None),
                occ(Role::Premise, "pc%0%1", None, None),
                occ(Role::Obligation, "pc%0%2", None, None),
            ],
            vec!["pc%0%0", "pc%0%1", "pc%0%2"],
        );
        let focused = focused(1, "pc%0%t%2%0", "pc%0%2", vec!["pc%0%0", "pc%0%t%2%0"]);
        let mut g = build(&[record(vec![batch, focused], vec![])]);
        // Closed alternative: x supports target only if target first licenses
        // x. The ordinary backward closure includes x; productive slicing
        // must retain only the independently grounded p -> target arc.
        g.arcs.push(Arc {
            tail: BTreeSet::from(["pc%0%1".into()]),
            head: BTreeSet::from(["pc%0%t%2%0".into()]),
            kind: ArcKind::SupportedBy,
            query: None,
            why: "synthetic cyclic alternative".into(),
        });
        g.arcs.push(Arc {
            tail: BTreeSet::from(["pc%0%t%2%0".into()]),
            head: BTreeSet::from(["pc%0%1".into()]),
            kind: ArcKind::CertifiedBy,
            query: None,
            why: "synthetic cycle back-edge".into(),
        });

        assert!(g.backward("pc%0%t%2%0").contains("pc%0%1"));
        let slice = g.backward_slice("pc%0%t%2%0", SliceOptions { calls: CallPolicy::Modular });
        assert!(slice.definite.contains("pc%0%t%2%0"));
        assert!(slice.definite.contains("pc%0%0"));
        assert!(!slice.definite.contains("pc%0%1"));
        assert!(!slice.possible.contains("pc%0%1"));
        assert!(slice.boundaries.is_empty());
        assert!(slice.steps.iter().all(|step| step.why != "synthetic cyclic alternative"));
        assert!(slice.steps.iter().all(|step| step.why != "synthetic cycle back-edge"));
    }

    #[test]
    fn opaque_call_keeps_local_requires_and_stops_before_callee_proof() {
        let caller = "t::caller";
        let callee = "t::callee";
        let node = "r.b0";

        let mut caller_batch = q(
            0,
            vec![
                occ(Role::Premise, "pc%0%0", None, None),
                occ(Role::Obligation, "pc%0%1", Some("t::callee#req"), Some("call.pre")),
                occ(Role::Premise, "pc%0%2", Some("t::callee#ens"), Some("call.post")),
                occ(Role::Obligation, "pc%0%3", Some("t::caller#ens[0]"), Some("function.ensures")),
            ],
            vec!["pc%0%0", "pc%0%1", "pc%0%2", "pc%0%3"],
        );
        caller_batch.fun = caller.into();
        caller_batch.occurrences[1].emission =
            Some(EmissionRole::CallPrecondition { callee: Some("t::callee".into()) });
        caller_batch.occurrences[1].node = Some(node.into());
        caller_batch.occurrences[2].emission =
            Some(EmissionRole::CallPostcondition { callee: "t::callee".into() });
        caller_batch.occurrences[2].node = Some(node.into());
        caller_batch.occurrences[3].emission = Some(EmissionRole::FunctionEnsures);

        let mut req_focused = focused(1, "pc%0%t%1%0", "pc%0%1", vec!["pc%0%0", "pc%0%t%1%0"]);
        req_focused.fun = caller.into();
        let mut caller_focused = focused(2, "pc%0%t%3%0", "pc%0%3", vec!["pc%0%2", "pc%0%t%3%0"]);
        caller_focused.fun = caller.into();

        let mut callee_batch = q(
            3,
            vec![
                occ(Role::Premise, "pc%3%0", None, None),
                occ(Role::Obligation, "pc%3%1", Some("t::callee#ens[0]"), Some("function.ensures")),
            ],
            vec!["pc%3%0", "pc%3%1"],
        );
        callee_batch.fun = callee.into();
        callee_batch.occurrences[1].emission = Some(EmissionRole::FunctionEnsures);
        let mut callee_focused = focused(4, "pc%3%t%1%0", "pc%3%1", vec!["pc%3%0", "pc%3%t%1%0"]);
        callee_focused.fun = callee.into();

        let functions = vec![
            FunctionRecord {
                fun: caller.into(),
                call_sites: vec![(node.into(), "caller.rs:1".into(), Some(callee.into()))],
                ..Default::default()
            },
            FunctionRecord { fun: callee.into(), ..Default::default() },
        ];
        let artifacts = vec![
            Artifact {
                id: "t::callee#req".into(),
                kind: ArtifactKind::RequiresAggregate,
                owner: callee.into(),
                parent: Some(callee.into()),
                span: None,
                callee: None,
                cfg_node: None,
                group: None,
            },
            Artifact {
                id: "t::callee#ens".into(),
                kind: ArtifactKind::EnsuresAggregate,
                owner: callee.into(),
                parent: Some(callee.into()),
                span: None,
                callee: None,
                cfg_node: None,
                group: None,
            },
            Artifact {
                id: "t::callee#ens[0]".into(),
                kind: ArtifactKind::EnsuresClause,
                owner: callee.into(),
                parent: Some("t::callee#ens".into()),
                span: Some("callee.rs:1".into()),
                callee: None,
                cfg_node: None,
                group: None,
            },
            Artifact {
                id: "t::caller#ens[0]".into(),
                kind: ArtifactKind::EnsuresClause,
                owner: caller.into(),
                parent: Some("t::caller#ens".into()),
                span: Some("caller.rs:2".into()),
                callee: None,
                cfg_node: None,
                group: None,
            },
            Artifact {
                id: "t::caller#call@r.b0".into(),
                kind: ArtifactKind::CallSite,
                owner: caller.into(),
                parent: Some(caller.into()),
                span: Some("caller.rs:1".into()),
                callee: Some(callee.into()),
                cfg_node: Some(node.into()),
                group: None,
            },
        ];
        let record = CoverageRecord {
            artifact_version: "0.1".into(),
            functions,
            queries: vec![caller_batch, req_focused, caller_focused, callee_batch, callee_focused],
            artifacts,
            ..Default::default()
        };
        let g = build(&[record]);

        let opaque = g.backward_slice("pc%0%3", SliceOptions { calls: CallPolicy::Opaque });
        assert!(opaque.definite.contains("pc%0%2"));
        assert!(opaque.definite.contains("pc%0%1"));
        assert!(opaque.definite.contains("pc%0%0"));
        assert!(!opaque.definite.contains("t::callee#ens"));
        assert!(!opaque.definite.contains("t::callee#ens[0]"));
        assert!(!opaque.definite.contains("pc%3%1"));
        assert_eq!(
            opaque.boundaries,
            vec![Boundary::Call {
                premise: "pc%0%2".into(),
                caller: caller.into(),
                callee: Some(callee.into()),
                cfg_node: Some(node.into()),
                call_artifact: Some("t::caller#call@r.b0".into()),
            }]
        );

        let modular = g.backward_slice("pc%0%3", SliceOptions { calls: CallPolicy::Modular });
        assert!(modular.definite.contains("t::callee#ens"));
        assert!(modular.definite.contains("t::callee#ens[0]"));
        assert!(modular.definite.contains("pc%3%1"));
        assert!(modular.boundaries.is_empty());
    }

    #[test]
    fn recursive_hypothesis_is_licensed_by_its_own_call_local_guard() {
        let node = "r.rec";
        let guard = "r.guard";
        let mut batch = q(
            0,
            vec![
                occ(Role::Premise, "h0", Some("t::f#req[0]"), None),
                occ(Role::Premise, "h1", Some("t::f#req[1]"), None),
                occ(Role::Obligation, "call_req", Some("t::f#req"), Some("call.pre")),
                occ(Role::Obligation, "dec", Some("t::f#dec"), None),
                occ(Role::Premise, "ih", Some("t::f#ens"), Some("call.post")),
                occ(Role::Obligation, "post", Some("t::f#ens[0]"), Some("function.ensures")),
            ],
            vec!["h0", "h1", "call_req", "dec", "ih", "post"],
        );
        batch.fun = "t::f".into();
        batch.occurrences[0].emission = Some(EmissionRole::FunctionRequires { clause: 0 });
        batch.occurrences[1].emission = Some(EmissionRole::FunctionRequires { clause: 1 });
        batch.occurrences[2].emission =
            Some(EmissionRole::CallPrecondition { callee: Some("t::f".into()) });
        batch.occurrences[2].node = Some(node.into());
        batch.occurrences[3].emission =
            Some(EmissionRole::TerminationCheck { at: crate::record::TerminationPoint::Function });
        batch.occurrences[3].node = Some(guard.into());
        batch.occurrences[4].emission =
            Some(EmissionRole::CallPostcondition { callee: "t::f".into() });
        batch.occurrences[4].node = Some(node.into());
        batch.occurrences[5].emission = Some(EmissionRole::FunctionEnsures);

        let mut call_req_t = focused(1, "call_req_t", "call_req", vec!["h0", "call_req_t"]);
        call_req_t.parent = Some(0);
        call_req_t.fun = "t::f".into();
        let mut dec = focused(3, "dec_t", "dec", vec!["h0", "dec_t"]);
        dec.parent = Some(0);
        dec.fun = "t::f".into();
        let mut post = focused(4, "post_t", "post", vec!["ih", "post_t"]);
        post.parent = Some(0);
        post.fun = "t::f".into();

        let artifacts = vec![
            Artifact {
                id: "t::f#req".into(),
                kind: ArtifactKind::RequiresAggregate,
                owner: "t::f".into(),
                parent: Some("t::f".into()),
                span: None,
                callee: None,
                cfg_node: None,
                group: None,
            },
            Artifact {
                id: "t::f#req[0]".into(),
                kind: ArtifactKind::RequiresClause,
                owner: "t::f".into(),
                parent: Some("t::f#req".into()),
                span: Some("f.rs:1".into()),
                callee: None,
                cfg_node: None,
                group: None,
            },
            Artifact {
                id: "t::f#req[1]".into(),
                kind: ArtifactKind::RequiresClause,
                owner: "t::f".into(),
                parent: Some("t::f#req".into()),
                span: Some("f.rs:2".into()),
                callee: None,
                cfg_node: None,
                group: None,
            },
            Artifact {
                id: "t::f#ens".into(),
                kind: ArtifactKind::EnsuresAggregate,
                owner: "t::f".into(),
                parent: Some("t::f".into()),
                span: None,
                callee: None,
                cfg_node: None,
                group: None,
            },
            Artifact {
                id: "t::f#ens[0]".into(),
                kind: ArtifactKind::EnsuresClause,
                owner: "t::f".into(),
                parent: Some("t::f#ens".into()),
                span: Some("f.rs:3".into()),
                callee: None,
                cfg_node: None,
                group: None,
            },
            Artifact {
                id: "t::f#dec".into(),
                kind: ArtifactKind::DecreasesAggregate,
                owner: "t::f".into(),
                parent: Some("t::f".into()),
                span: Some("f.rs:4".into()),
                callee: None,
                cfg_node: None,
                group: None,
            },
        ];
        let graph = build(&[CoverageRecord {
            artifact_version: "0.1".into(),
            functions: vec![FunctionRecord {
                fun: "t::f".into(),
                call_sites: vec![(node.into(), "f.rs:5".into(), Some("t::f".into()))],
                recursive_calls: vec![crate::record::RecursiveCallRecord {
                    call_node: node.into(),
                    callee: "t::f".into(),
                    guard_node: guard.into(),
                    span: "f.rs:5".into(),
                    loop_span: None,
                    lemma_span: None,
                }],
                ..Default::default()
            }],
            queries: vec![batch, call_req_t, dec, post],
            artifacts,
            ..Default::default()
        }]);

        let slice = graph.backward_slice("post_t", SliceOptions { calls: CallPolicy::Modular });
        // The hypothesis is reached, and it is grounded by this call's own
        // decrease guard plus the preconditions the call discharged — never by
        // the function's own ensures check, which would be circular.
        for vertex in ["ih", "dec", "dec_t", "h0", "call_req", "call_req_t"] {
            assert!(slice.definite.contains(vertex), "missing {vertex}: {slice:?}");
        }
        let step = slice
            .steps
            .iter()
            .find(|step| step.kind == ArcKind::Demand && step.head == "ih")
            .expect("recursive hypothesis has a call-local demand step");
        assert!(step.tail.contains("dec"), "guard missing from the tail: {step:?}");
        assert!(
            !step.tail.contains("post") && !step.tail.contains("post_t"),
            "induction licensed by its own conclusion: {step:?}"
        );
        // No component-wide certificate vertex is materialized.
        assert!(
            !slice.definite.iter().any(|vertex| vertex.contains("certificate")),
            "unexpected component certificate: {slice:?}"
        );
    }

    #[test]
    fn opaque_policy_does_not_hide_unguarded_recursive_cycle() {
        let aggregate = "t::f#ens";
        let node = "r.self";
        let mut batch = q(
            0,
            vec![
                occ(Role::Premise, "pc%0%0", Some(aggregate), Some("call.post")),
                occ(Role::Obligation, "pc%0%1", Some("t::f#ens[0]"), Some("function.ensures")),
            ],
            vec!["pc%0%0", "pc%0%1"],
        );
        batch.occurrences[0].emission =
            Some(EmissionRole::CallPostcondition { callee: "t::f".into() });
        batch.occurrences[0].node = Some(node.into());
        batch.occurrences[1].emission = Some(EmissionRole::FunctionEnsures);
        let focused = focused(1, "pc%0%t%1%0", "pc%0%1", vec!["pc%0%0", "pc%0%t%1%0"]);
        let record = CoverageRecord {
            artifact_version: "0.1".into(),
            functions: vec![FunctionRecord {
                fun: "t::f".into(),
                call_sites: vec![(node.into(), "f.rs:1".into(), Some("t::f".into()))],
                // Mirrors exec_allows_no_decreases_clause: no guard record.
                ..Default::default()
            }],
            queries: vec![batch, focused],
            artifacts: vec![
                Artifact {
                    id: aggregate.into(),
                    kind: ArtifactKind::EnsuresAggregate,
                    owner: "t::f".into(),
                    parent: Some("t::f".into()),
                    span: None,
                    callee: None,
                    cfg_node: None,
                    group: None,
                },
                Artifact {
                    id: "t::f#ens[0]".into(),
                    kind: ArtifactKind::EnsuresClause,
                    owner: "t::f".into(),
                    parent: Some(aggregate.into()),
                    span: Some("f.rs:2".into()),
                    callee: None,
                    cfg_node: None,
                    group: None,
                },
                Artifact {
                    id: "t::f#call@r.self".into(),
                    kind: ArtifactKind::CallSite,
                    owner: "t::f".into(),
                    parent: Some("t::f".into()),
                    span: Some("f.rs:1".into()),
                    callee: Some("t::f".into()),
                    cfg_node: Some(node.into()),
                    group: None,
                },
            ],
            ..Default::default()
        };
        let g = build(&[record]);
        let slice = g.backward_slice("pc%0%1", SliceOptions { calls: CallPolicy::Opaque });

        assert!(slice.definite.is_empty());
        assert!(!slice.boundaries.iter().any(|boundary| matches!(boundary, Boundary::Call { .. })));
        assert_eq!(slice.boundaries, vec![Boundary::Ungrounded { vertex: "pc%0%1".into() }]);
    }
}
