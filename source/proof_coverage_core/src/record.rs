//! Proof-coverage record schema (`verus-proof-coverage/1`).
//!
//! Mirrors `PROOF_COVERAGE.md` §3. Occurrences carry the model's
//! provenance dimensions (role, carrier, origin, phase, placement, source
//! span); rows the rules cannot attribute stay `origin.kind = "unresolved"`
//! and carry a bounded `shape` summary — the ledger that drives gap analysis.

use serde::{Deserialize, Serialize};

pub const SCHEMA: &str = "verus-proof-coverage/1";
pub const ARTIFACT_VERSION: &str = "0.1";

// ── typed record vocabulary ─────────────────────────────────────────────────
//
// L1 rule: the record is an observation, so every closed value set it reports
// is an enum, not a string. This also makes the schema round-trippable, so the
// producer and its consumers share one type.
//
// Every `serde` spelling below is the exact wire spelling emitted by v0.1.
// Changing a spelling changes the record format and invalidates fixtures.

/// A source construct the user wrote, or an aggregate the encoder formed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ArtifactKind {
    Function,
    RequiresAggregate,
    EnsuresAggregate,
    RequiresClause,
    EnsuresClause,
    LocalLemma,
    LemmaRequiresClause,
    LemmaEnsuresClause,
    LoopInvariantClause,
    /// The whole `decreases` measure of a function or loop. One AIR assert
    /// covers the entire lexicographic tuple, so this is what a termination
    /// obligation joins to.
    DecreasesAggregate,
    /// One component of a `decreases` measure.
    DecreasesClause,
    CallSite,
    Assertion,
    AssertForall,
    /// A user `assume` statement: a fact the proof takes on trust.
    Assumption,
    /// A loop's condition, as written; it has two occurrences (assumed at
    /// body entry, negated after exit).
    LoopCondition,
    /// An `if` condition, as written; one occurrence per arm.
    BranchCondition,
    /// An initializing assignment (`let x = e`); its equality is a premise.
    Assignment,
    /// The binding of a function's return value to its returned expression.
    ReturnBinding,
    /// A `reveal`/fuel statement.
    Reveal,
}

/// How an occurrence's provenance was attributed. `Unresolved` is a typed
/// gap, not a failure: it records that no exact rule applied.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OriginKind {
    Source,
    Derived,
    Generated,
    Unresolved,
}

/// `vir::sst::LoopInv`'s documented `(at_entry, at_exit)` flag pairing. The
/// group determines which protocol positions may license an export, so the
/// analyzer derives certificate tails from it rather than assuming one shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LoopInvariantGroup {
    /// `(true, false)`
    InvariantExceptBreak,
    /// `(true, true)`
    Invariant,
    /// `(false, true)`
    LoopEnsures,
    /// `(false, false)` — no declared protocol position.
    Unclassified,
}

/// An explicit transformation relating record rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Transform {
    TerminalSplit,
    LowerStatement,
    /// Retained for the conservative order-alignment fallback.
    LowerAssume,
}

/// `Batch` is one canonical query with aggregate evidence; `Focused` is one
/// terminal obligation with singleton-headed evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum QueryFamily {
    Batch,
    Focused,
}

/// What syntactic position carries the fact inside the AIR query.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Carrier {
    #[serde(rename = "assume")]
    Assume,
    #[serde(rename = "assert")]
    Assert,
    /// A query-local axiom. Structurally outside CFG placement.
    #[serde(rename = "axiom(query_local)")]
    QueryLocalAxiom,
    /// An assignment statement. Its equality is synthesized by the SSA pass
    /// (`var_to_const`) after structured AIR; the shadow guards that equality
    /// after SSA, from the pass's own generation trace.
    #[serde(rename = "assign")]
    Assign,
    /// A version-reconciliation equality the SSA pass inserts at a
    /// control-flow join. Nothing written stands behind it; it exists in the
    /// versioned query only.
    #[serde(rename = "ssa_reconciliation")]
    SsaReconciliation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CfgNodeKind {
    Entry,
    Exit,
    Assume,
    Assert,
    Assign,
    Call,
    Branch,
    Join,
    LoopHeader,
    LoopBody,
    LoopLatch,
    LoopExit,
    Return,
    DeadEnd,
    ProofRegion,
    Stmt,
    Transfer,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CfgEdgeKind {
    Next,
    Join,
    LoopBody,
    LoopBack,
    LoopExit,
    Transfer,
    Return,
}

/// Gives each record enum its canonical wire spelling plus an exhaustive
/// `ALL`, so `Display` can render the record's own vocabulary and the test
/// `wire_spellings_match_serde` can prove `Display` and `serde` agree. A
/// renamed variant therefore cannot silently change the record format.
macro_rules! wire_enum {
    ($ty:ident { $($variant:ident => $spelling:literal),+ $(,)? }) => {
        impl $ty {
            pub const ALL: &'static [$ty] = &[$($ty::$variant),+];

            pub fn as_str(&self) -> &'static str {
                match self { $($ty::$variant => $spelling),+ }
            }
        }

        impl std::fmt::Display for $ty {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.write_str(self.as_str())
            }
        }
    };
}

wire_enum!(ArtifactKind {
    Function => "function",
    RequiresAggregate => "requires_aggregate",
    EnsuresAggregate => "ensures_aggregate",
    RequiresClause => "requires_clause",
    EnsuresClause => "ensures_clause",
    LocalLemma => "local_lemma",
    LemmaRequiresClause => "lemma_requires_clause",
    LemmaEnsuresClause => "lemma_ensures_clause",
    LoopInvariantClause => "loop_invariant_clause",
    DecreasesAggregate => "decreases_aggregate",
    DecreasesClause => "decreases_clause",
    CallSite => "call_site",
    Assertion => "assertion",
    AssertForall => "assert_forall",
    Assumption => "assumption",
    LoopCondition => "loop_condition",
    BranchCondition => "branch_condition",
    Assignment => "assignment",
    ReturnBinding => "return_binding",
    Reveal => "reveal",
});

impl ArtifactKind {
    /// Is this a single declared clause, as opposed to an aggregate or a
    /// statement? A property of the vocabulary, not of the kind's spelling.
    pub fn is_clause(&self) -> bool {
        matches!(
            self,
            ArtifactKind::RequiresClause
                | ArtifactKind::EnsuresClause
                | ArtifactKind::LemmaRequiresClause
                | ArtifactKind::LemmaEnsuresClause
                | ArtifactKind::LoopInvariantClause
                | ArtifactKind::DecreasesClause
        )
    }
}

wire_enum!(OriginKind {
    Source => "source",
    Derived => "derived",
    Generated => "generated",
    Unresolved => "unresolved",
});

wire_enum!(LoopInvariantGroup {
    InvariantExceptBreak => "invariant_except_break",
    Invariant => "invariant",
    LoopEnsures => "loop_ensures",
    Unclassified => "unclassified",
});

wire_enum!(Transform {
    TerminalSplit => "terminal_split",
    LowerStatement => "lower_statement",
    LowerAssume => "lower_assume",
});

wire_enum!(QueryFamily {
    Batch => "batch",
    Focused => "focused",
});

wire_enum!(Carrier {
    Assume => "assume",
    Assert => "assert",
    QueryLocalAxiom => "axiom(query_local)",
    Assign => "assign",
    SsaReconciliation => "ssa_reconciliation",
});

wire_enum!(Role {
    Premise => "premise",
    Obligation => "obligation",
});

wire_enum!(CfgNodeKind {
    Entry => "entry",
    Exit => "exit",
    Assume => "assume",
    Assert => "assert",
    Assign => "assign",
    Call => "call",
    Branch => "branch",
    Join => "join",
    LoopHeader => "loop_header",
    LoopBody => "loop_body",
    LoopLatch => "loop_latch",
    LoopExit => "loop_exit",
    Return => "return",
    DeadEnd => "dead_end",
    ProofRegion => "proof_region",
    Stmt => "stmt",
    Transfer => "transfer",
});

wire_enum!(CfgEdgeKind {
    Next => "next",
    Join => "join",
    LoopBody => "loop_body",
    LoopBack => "loop_back",
    LoopExit => "loop_exit",
    Transfer => "transfer",
    Return => "return",
});

// ── typed emission role ─────────────────────────────────────────────────────
//
// Why an occurrence exists in its query: which construction emitted it and at
// which position of that construction's protocol. This is the load-bearing
// half of what `Origin.detail` used to carry as a rendered string (the callee
// of a contract fact, the clause ordinal, the loop protocol position). The
// other half — formula-shape diagnostics for unresolved rows — stays in
// `detail`, which is now explicitly diagnostic.
//
// The `phase` string protocol rules are keyed on is rendered *from* the role
// (`EmissionRole::phase`), never stored, so the role is the single source and
// the string cannot drift from it.

/// Position in an invariant block's protocol. The block assumes the
/// invariant's contents at open and must re-establish them at close, so the
/// close obligation is what licenses the open assumption.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum InvariantBlockPoint {
    Open,
    Close,
}

/// Position of a loop invariant clause in the loop protocol.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LoopPoint {
    /// Asserted before the loop is first entered.
    Establish,
    /// Assumed at the top of the loop body.
    BodyEntry,
    /// Asserted at the end of the loop body.
    Maintain,
    /// Asserted at a labeled `break` or `continue`.
    Transfer,
    /// Assumed after the loop.
    Exit,
}

/// Position of a user assertion: the check obligation, or the assumption
/// exported after it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AssertionPoint {
    Check,
    Establish,
}

/// Which half of a contract a clause belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ContractSection {
    Requires,
    Ensures,
}

/// Position of an `assert ... by(..)` contract clause: checked as an
/// obligation, or assumed as a premise. Requires are checked outside and
/// assumed inside the isolated query; ensures the reverse.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AssertQueryPoint {
    Check,
    Assume,
}

/// Position in an `assert forall` proof region.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ForallPoint {
    /// The bound-variable hypothesis assumed inside the region.
    Hypothesis,
    /// The quantified body checked inside the region.
    Goal,
    /// The quantified conclusion exported after the region.
    Establish,
}

/// Which termination obligation a `decreases` check discharges.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TerminationPoint {
    /// The function's measure decreases at a recursive call.
    Function,
    /// The loop's measure decreases at the end of the body.
    LoopEnd,
    /// The loop's measure decreases at a `continue`.
    LoopContinue,
}

/// Where a type invariant was assumed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TypeInvariantSite {
    /// A parameter, for the whole function body (query-local axiom).
    Parameter,
    /// A variable re-assumed in an isolated loop-body query.
    Loop,
    /// A variable assumed in an `assert ... by` query.
    AssertQuery,
    /// A statement in the body (havoc re-assume).
    Statement,
}

/// Where a fuel fact was assumed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FuelSite {
    /// The function's fuel setting (query-local axiom).
    Function,
    /// A `reveal` statement in the body.
    Statement,
}

/// Mirror of `vir::observer::LoweringSite` without the `Assume` payload, for
/// facts whose only recorded provenance is the lowering template that emitted
/// them. This crate does not depend on `vir`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LoweringSiteKind {
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

/// The control-flow join an SSA reconciliation serves (`air::var_to_const::SsaJoin`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(tag = "join", rename_all = "snake_case")]
pub enum SsaJoinKind {
    SwitchArm { arm: u32 },
    Fallthrough,
    Break,
}

/// Why an occurrence exists in its query.
///
/// Every attributed occurrence carries exactly one role; unresolved rows
/// carry none. Protocol rules in the analyzer quantify over these values,
/// never over rendered strings.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum EmissionRole {
    /// The function's own `requires` clause, assumed for its body.
    FunctionRequires {
        clause: u32,
    },
    /// The function's `ensures`, checked at exit.
    FunctionEnsures,
    /// A callee's `requires`, checked at the call. `callee` is absent only
    /// when the encoding did not name the callee at the check.
    CallPrecondition {
        #[serde(skip_serializing_if = "Option::is_none")]
        #[serde(default)]
        callee: Option<String>,
    },
    /// A callee's `ensures`, assumed after the call.
    CallPostcondition {
        callee: String,
    },
    LoopInvariant {
        point: LoopPoint,
    },
    /// The loop condition assumed at the top of the body.
    LoopEntryCondition,
    /// The negated loop condition assumed after the loop.
    LoopExitCondition,
    Assertion {
        point: AssertionPoint,
    },
    AssertQuery {
        section: ContractSection,
        point: AssertQueryPoint,
    },
    AssertForall {
        point: ForallPoint,
    },
    /// A user `assume`.
    UserAssumption,
    /// A written invariant block (`open_atomic_invariant!` /
    /// `open_local_invariant!`): the invariant's contents assumed at open, and
    /// the obligation to re-establish them at close. The close obligation is
    /// what licenses the open assumption.
    InvariantBlock {
        point: InvariantBlockPoint,
    },
    /// A `decreases` measure check.
    TerminationCheck {
        at: TerminationPoint,
    },
    /// The `check_decrease_height` premise the recursion encoding inserts.
    DecreaseHeightCheck,
    TypeInvariant {
        site: TypeInvariantSite,
    },
    /// The `has_type` fact for a fresh value.
    HasType,
    Fuel {
        site: FuelSite,
    },
    TraitBound,
    /// The `if` condition (or its negation) assumed in a branch arm.
    BranchCondition {
        arm: u32,
    },
    /// The equality an initializing assignment introduces.
    AssignmentEquality,
    /// The equality a mutating assignment (`x = e`, `x.f = e`) introduces,
    /// synthesized by the SSA pass from the recorded `Assign` statement.
    MutationEquality,
    /// The equality `x@m == x@k` the SSA pass inserts where control-flow
    /// paths join, so that every path leaves `x` at one version.
    SsaReconciliation {
        join: SsaJoinKind,
    },
    /// The current-value fact for a mutable reference.
    MutRefCurrent,
    /// `assume(false)` synthesized where control cannot continue.
    PathTermination,
    ArithOverflowCheck,
    PatternMatchCheck,
    /// A `has_resolved` fact.
    Resolution,
    /// A string or byte-string literal fact.
    StringLiteral,
    /// An SST assumption whose intent has no finer role above.
    Assumed {
        intent: AssumeIntent,
    },
    /// A fact whose only recorded provenance is the lowering template.
    Lowered {
        site: LoweringSiteKind,
    },
}

impl EmissionRole {
    /// The protocol position this role occupies, as the string consumers
    /// display. Rendered from the role, never stored: the role is the single
    /// source and this cannot drift from it. `None` when the role has no
    /// protocol position.
    pub fn phase(&self) -> Option<String> {
        use EmissionRole::*;
        let s: &str = match self {
            FunctionRequires { .. } => "function.requires",
            FunctionEnsures => "function.ensures",
            CallPrecondition { .. } => "call.pre",
            CallPostcondition { .. } => "call.post",
            LoopInvariant { point } => match point {
                LoopPoint::Establish => "loop.establish",
                LoopPoint::BodyEntry => "loop.body_assume",
                LoopPoint::Maintain => "loop.maintain",
                LoopPoint::Transfer => "loop.at_transfer",
                LoopPoint::Exit => "loop.exit_assume",
            },
            LoopEntryCondition => "loop.entry_condition",
            LoopExitCondition => "loop.exit_condition",
            Assertion { point: AssertionPoint::Check } => "assert.check",
            Assertion { point: AssertionPoint::Establish } => "assert.establish",
            AssertQuery { section, point } => match (section, point) {
                (ContractSection::Requires, AssertQueryPoint::Check) => "lemma.requires_check",
                (ContractSection::Requires, AssertQueryPoint::Assume) => "lemma.requires_assume",
                (ContractSection::Ensures, AssertQueryPoint::Check) => "lemma.goal",
                (ContractSection::Ensures, AssertQueryPoint::Assume) => "lemma.ensures_assume",
            },
            AssertForall { point } => match point {
                ForallPoint::Hypothesis => "forall.hypothesis",
                ForallPoint::Goal => "forall.goal",
                ForallPoint::Establish => "forall.establish",
            },
            InvariantBlock { point } => match point {
                InvariantBlockPoint::Open => "invariant_block.open",
                InvariantBlockPoint::Close => "invariant_block.close",
            },
            TerminationCheck { at } => match at {
                TerminationPoint::Function => "function.termination",
                TerminationPoint::LoopEnd => "loop.decreases_at_end",
                TerminationPoint::LoopContinue => "loop.decreases_at_continue",
            },
            TypeInvariant { site } => match site {
                TypeInvariantSite::Parameter => "function.param_type_invariant",
                TypeInvariantSite::Loop => "loop.type_invariant",
                TypeInvariantSite::AssertQuery => "lemma.type_invariant",
                TypeInvariantSite::Statement => return None,
            },
            Fuel { site: FuelSite::Function } => "function.fuel",
            Fuel { site: FuelSite::Statement } => return None,
            TraitBound => "function.trait_bound",
            BranchCondition { arm } => return Some(format!("control.branch_arm:{arm}")),
            PathTermination => "control.path_termination",
            UserAssumption
            | DecreaseHeightCheck
            | HasType
            | AssignmentEquality
            | MutationEquality
            | SsaReconciliation { .. }
            | MutRefCurrent
            | ArithOverflowCheck
            | PatternMatchCheck
            | Resolution
            | StringLiteral
            | Assumed { .. }
            | Lowered { .. } => return None,
        };
        Some(s.to_string())
    }

    /// Is this a call-contract fact crossing into a callee?
    pub fn call_contract(&self) -> Option<(ContractSection, Option<&str>)> {
        match self {
            EmissionRole::CallPrecondition { callee } => {
                Some((ContractSection::Requires, callee.as_deref()))
            }
            EmissionRole::CallPostcondition { callee } => {
                Some((ContractSection::Ensures, Some(callee.as_str())))
            }
            _ => None,
        }
    }
}

// ── source functions (snapshot 1) ────────────────────────────────────────────
//
// What the pre-simplified VIR says about each function, independent of
// whether it produced a verifier query. These are the identities the
// system-level analysis quantifies over: which functions are specification,
// proof, or executable code; which are trusted rather than verified; which
// definitions are hidden behind `reveal`; and how the functions relate through
// traits and modules. Transcribed from `vir::ast::FunctionX`; no verifier pass
// is modified.

/// `vir::ast::Mode`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FunctionMode {
    Spec,
    Proof,
    Exec,
}

/// `vir::ast::FunctionKind`, with paths rendered as friendly names.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum FunctionKind {
    Static,
    /// A method declared in a trait.
    TraitMethodDecl {
        trait_path: String,
        has_default: bool,
    },
    /// A method implementing `method` of `trait_path` for some type.
    TraitMethodImpl {
        method: String,
        trait_path: String,
    },
    /// An implementation of a foreign trait's method.
    ForeignTraitMethodImpl {
        method: String,
        trait_path: String,
    },
}

/// `vir::ast::ItemKind`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ItemKind {
    Function,
    Const,
    Static,
}

/// `vir::ast::Visibility`: public, or restricted to a module and its
/// descendants.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(tag = "scope", rename_all = "snake_case")]
pub enum Visibility {
    Public,
    Restricted { module: String },
}

/// `vir::ast::BodyVisibility`: whether a spec function's definition is
/// available at all, and where.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(tag = "body", rename_all = "snake_case")]
pub enum BodyVisibility {
    /// Declared uninterpreted: no definition is visible anywhere.
    Uninterpreted,
    Visible {
        visibility: Visibility,
    },
}

/// `vir::ast::Opaqueness`: whether a spec function's definition axiom is
/// installed by default or only under `reveal`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(tag = "opaqueness", rename_all = "snake_case")]
pub enum Opaqueness {
    Opaque,
    Revealed { visibility: Visibility },
}

/// One function of the pre-simplified crate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceFunction {
    /// The function's raw VIR path (`crate::impl&%3::view`). This is the
    /// identity every other table uses — `Artifact.owner`, `Artifact.callee`,
    /// `FunctionRecord.fun`, `QueryRecord.fun`, `AmbientRecord.owner`,
    /// `refinements`, call sites — and it is injective, because it is
    /// `FunX.path`.
    pub fun: String,
    /// Display name only (`alloc::borrow::Cow::view`). *Not* injective:
    /// Verus renders an impl method as `<self-type path>::<ident>`, dropping
    /// the impl disambiguator and the self type's type arguments, so all three
    /// `View` impls for `Cow` share this spelling. Never a join key; a
    /// consumer that shows it should disambiguate with `fun` where it is
    /// shared.
    pub friendly: String,
    /// The crate that defines the function, by friendly name (`vstd`,
    /// `core`, `alloc`, or the crate's own name).
    pub krate: String,
    /// Defined in the crate being verified. An imported function's body is
    /// absent here because it lives in its own crate, not because it is
    /// trusted; its verification status is that crate's record.
    pub local: bool,
    pub mode: FunctionMode,
    pub kind: FunctionKind,
    pub item: ItemKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub module: Option<String>,
    pub visibility: Visibility,
    pub body_visibility: BodyVisibility,
    pub opaqueness: Opaqueness,
    /// The function has a body in the crate. A function without one is
    /// trusted on its contract alone.
    pub has_body: bool,
    /// Marked `external_body` or an external fn specification: the body is
    /// not verified, so the contract is an assumption of the proof.
    pub external_body: bool,
    /// A `broadcast proof fn`: its contract is installed as an ambient axiom.
    pub broadcast: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub span: Option<String>,
}

impl SourceFunction {
    /// Is this function's contract an assumption of every proof that uses it,
    /// rather than a verified result? `external_body` is exactly that
    /// declaration, wherever the function is defined. A local function with no
    /// body is an uninterpreted or abstract declaration, not a trusted one;
    /// an imported function's body is simply elsewhere.
    pub fn trusted(&self) -> bool {
        self.external_body
    }
}

#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct CoverageRecord {
    pub schema: String,
    pub artifact_version: String,
    pub functions: Vec<FunctionRecord>,
    /// Every function of the pre-simplified crate (snapshot 1), whether or
    /// not it produced a query: mode, kind, visibility, and trust.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    #[serde(default)]
    pub source_functions: Vec<SourceFunction>,
    pub queries: Vec<QueryRecord>,
    pub ambients: Vec<AmbientRecord>,
    /// Source artifacts: what the user wrote (or the encoder aggregated),
    /// joined from occurrences via `Occurrence.artifact`.
    pub artifacts: Vec<Artifact>,
    /// `(impl method, trait method)` pairs from
    /// `vir::ast::FunctionKind::TraitMethodImpl`. A trait-method
    /// implementation's obligations project onto the trait's clause
    /// artifacts, licensed by this relation rather than by relaxing the
    /// owner check.
    pub refinements: Vec<(String, String)>,
    /// Explicit transformation records: terminal splits, alignment joins.
    pub derivations: Vec<Derivation>,
    /// Construction-exact checked exports: which obligation's discharge the
    /// encoding required before it admitted which assumption.
    ///
    /// This is L1. The producer's walk observes the pairing directly — an
    /// assume in the statement position immediately after an assert of the
    /// same formula, or an invariant block's open and close. The *claim* that
    /// the check licenses the export is the licensing rule that consumes this
    /// (`licensing::LicensingRule::CheckedExport`), not this row.
    ///
    /// It exists because a pairing is not always expressible as a shared
    /// artifact: a generated overflow check and an invariant block have no
    /// written statement behind them, so there is no artifact for the two
    /// halves to agree on. Without this relation those exports reach the
    /// graph as roots and the facts that discharged their checks drop out of
    /// every slice.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    #[serde(default)]
    pub checked_exports: Vec<CheckedExport>,
    /// Counts derived from the tables above.
    ///
    /// This is a derived view, not an observation, so consumers must not
    /// treat it as authoritative and a record may omit it. It is retained in
    /// the wire format for now because the v0.1 report reproduces it.
    #[serde(default)]
    pub summary: Summary,
    /// Content identity of the record body, `pc_r%<sha256>`.
    ///
    /// Declared last because it is computed *over* the serialized body:
    /// `audit::compute_record_id` removes this key before hashing, so the
    /// digest covers everything except itself. The producer emits the record
    /// with this field empty and fills it in once the digest is known.
    #[serde(default)]
    pub record_id: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Artifact {
    /// Stable id, e.g. "crate::f#ens", "crate::f#ens[1]", "crate::f#inv@<span>[0]",
    /// "crate::f#call@<node>", "crate::f#assert@<node>".
    pub id: String,
    pub kind: ArtifactKind,
    /// Friendly name of the owning function.
    pub owner: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<String>,
    /// For clauses: the aggregate they belong to. For call sites: the callee's
    /// contract aggregates are reachable via `callee`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parent: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub callee: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cfg_node: Option<String>,
    /// For loop invariant clauses: which declared group the clause belongs
    /// to, from `vir::sst::LoopInv`'s documented flag pairing —
    /// `invariant_except_break` (at_entry, not at_exit), `invariant`
    /// (at_entry and at_exit), `loop_ensures` (at_exit only). The group
    /// determines which protocol positions may license an export, so the
    /// analyzer derives certificate tails from it instead of assuming one
    /// shape for every clause.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub group: Option<LoopInvariantGroup>,
}

/// What construction paired a check with an export.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CheckedExportKind {
    /// A user `assert`: its discharged check licenses the proposition assumed
    /// after it. Also carried by the shared `assertion` artifact, so this row
    /// is redundant for user asserts and recorded for uniformity.
    Assertion,
    /// A check the encoding generated and then re-assumed (arithmetic
    /// overflow, pattern-match refutability, a place requirement). No written
    /// statement stands behind it, so it has no artifact.
    GeneratedCheck,
    /// An invariant block: the close obligation licenses the contents assumed
    /// at open.
    InvariantBlock,
}

/// One checked export, by occurrence label within one query.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedExport {
    pub kind: CheckedExportKind,
    /// The batch query both occurrences belong to.
    pub query: u64,
    /// Activation label of the goal obligation.
    pub check: String,
    /// Activation label of the assumption its discharge admits.
    pub export: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Derivation {
    pub transform: Transform,
    pub inputs: Vec<String>,
    pub outputs: Vec<String>,
}

/// The SST side of the story, for correlating against query occurrences.
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct FunctionRecord {
    /// Deterministic structural identity of this SST/CFG variant. Repeated
    /// checks with identical lowering input share a variant; expanded or
    /// otherwise distinct checks have different variants.
    pub variant: String,
    pub fun: String,
    /// Control graph built from the SST tree.
    pub cfg: CfgRecord,
    /// Call sites in structural order: (cfg node, span, callee). The callee
    /// is the syntactic target: for a trait method call, the trait method.
    pub call_sites: Vec<(String, String, Option<String>)>,
    /// Call sites whose trait dispatch the verifier resolved statically:
    /// (cfg node, resolved implementation method). The encoding assumes the
    /// resolved method's postcondition at such a call, so this is the callee
    /// whose contract the caller actually consumed.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    #[serde(default)]
    pub resolved_calls: Vec<(String, String)>,
    /// Every SST assume in lowering order: the site-identity tag + source span.
    pub sst_assumes: Vec<SstAssume>,
    /// `(cfg node, enclosing invariant-block node)` for every node the SST
    /// walk created while inside an `OpenInvariant` statement, innermost
    /// block first.
    ///
    /// Recorded membership, not a path prefix: the walk knows which block it
    /// is inside, so the open assumption and the close obligation are paired
    /// by a typed join rather than by re-reading structural spellings.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    #[serde(default)]
    pub invariant_block_members: Vec<(String, String)>,
    /// Prover-isolated `assert ... by(nonlinear_arith|bit_vector)` regions:
    /// anonymous local lemmas with requires/ensures clause spans.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    #[serde(default)]
    pub lemmas: Vec<LemmaRecord>,
    /// Recursive call sites, derived exactly from the SST guard block that
    /// vir::recursion::check_termination inserts (a CheckDecreaseHeight
    /// assert immediately preceding the call). No verifier hook: pure
    /// observation of the inserted construction.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    #[serde(default)]
    pub recursive_calls: Vec<RecursiveCallRecord>,
    /// Ensures clause spans (from `PostConditionSst`), in clause order.
    pub ens_spans: Vec<String>,
    /// Requires clause spans (from `FuncCheckSst.reqs`), in clause order.
    pub req_spans: Vec<String>,
    /// `if` statements: (branch cfg node, span of the condition expression).
    /// The site of a branch-condition artifact.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    #[serde(default)]
    pub branches: Vec<(String, String)>,
    /// Assignment nodes whose destination is a compiler temporary
    /// (`VarIdentDisambiguate::VirTemp` and kin): decrease-init bindings and
    /// other synthesized locals. Their equalities are encoding facts, not
    /// written assignments, so they receive no `assignment` artifact.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    #[serde(default)]
    pub synthetic_bindings: Vec<String>,
    /// Parameter spans (from `FunctionSst.pars`), in declaring order. The
    /// site of a parameter's type-invariant axiom: the lowering records the
    /// parameter ordinal, and this resolves it to a source position.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    #[serde(default)]
    pub param_spans: Vec<String>,
    /// Loops with their invariant clause spans.
    pub loops: Vec<LoopRecord>,
}

/// Construction-site identity for an SST assumption.
///
/// This mirrors `vir::sst::AssumeIntent` at the serialized boundary. Keeping
/// it typed prevents a newly added verifier intent from silently falling
/// through a string-based classifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum AssumeIntent {
    UserAssume,
    AssertedProposition,
    CheckedCondition,
    HasType,
    HasResolved,
    TypeInvariant,
    PathTermination,
    AssertForallRequire,
    AssertForallEnsures,
    AssertQueryRequire,
    AssertQueryEnsures,
    OpenedInvariant,
    AtomicUpdate,
    AtomicUpdateEnsures,
    ClosureSpec,
    ClosureRequires,
    FunctionRequires,
    MutRefCurrent,
    VarEquality,
    ExpandErrorsSplit,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SstAssume {
    pub intent: AssumeIntent,
    pub span: String,
    /// Span of the innermost enclosing loop, if any (loop bodies lower into
    /// separate queries under loop isolation).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub loop_span: Option<String>,
    /// True if the assume's formula lowers to a shape the tier-1 rules
    /// recognize on the AIR side (used by alignment to predict which SST
    /// rows will still be unresolved).
    pub recognizable: bool,
    /// Span of the innermost enclosing assert-query (local lemma) body, if
    /// any (those bodies lower into separate prover-isolated queries).
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub lemma_span: Option<String>,
    /// CFG node of this assume statement.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub node: Option<String>,
    /// Op-skeleton signature of the formula (for per-signature alignment).
    pub sig: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct LoopRecord {
    /// SST loop id (appears in AIR as the Breakable label `break_label%<id>`).
    pub id: u64,
    /// Span of the loop statement (matches the "while loop" query context span).
    pub span: String,
    /// Invariant clause spans: (span, at_entry, at_exit).
    pub invs: Vec<(String, bool, bool)>,
    /// `decreases` clause spans, in declaring order. Replaces an earlier
    /// `has_decrease: bool`, which recorded that a user-authored clause exists
    /// while discarding the clause itself, so the termination obligation had
    /// nothing to be attributed to.
    pub decreases: Vec<String>,
    /// Span of the loop condition expression, for `while` loops. The site of
    /// the loop-condition artifact.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub cond_span: Option<String>,
    pub is_for_loop: bool,
    /// CFG nodes realizing the loop protocol positions.
    pub header: String,
    pub body_entry: String,
    pub latch: String,
    pub exit: String,
}

/// An ambient axiom with a stable evidence label and its recorded owner.
/// Existing AIR names are preserved; function-owned unnamed axioms may be
/// named only in the shadow clone. Remaining unnamed axioms are background
/// (β) and are only tallied.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AmbientRecord {
    /// The axiom's shadow `:named` label as it appears in cores (join key).
    pub label: String,
    /// Which context op installed it: SpecDefinition | ReqEns | Broadcast | TraitImpl.
    pub op: String,
    /// Friendly name of the owning function/lemma.
    pub owner: String,
    /// Solver contexts it was installed into.
    pub solver_contexts: Vec<u64>,
}

#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct SolverConfigRecord {
    pub solver: String,
    pub options: Vec<(String, String)>,
    pub rlimit: u32,
    pub single_check_query: bool,
    pub ignore_unexpected_smt: bool,
    pub debug: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expected_solver_version: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct QueryRecord {
    pub id: u64,
    pub family: QueryFamily,
    /// For focused queries: the id of the batch query they refine.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parent: Option<u64>,
    /// For focused queries: the activation label of the parent obligation
    /// occurrence and the terminal's activation label.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parent_obligation_label: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_label: Option<String>,
    /// Structural path of the terminal within the parent obligation formula.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub terminal_path: Option<String>,
    /// Exact SST/CFG variant observed for the verifier query operation.
    /// `None` means this query family has no observable `FuncCheckSst`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub function_variant: Option<String>,
    pub solver_context: u64,
    /// Effective canonical AIR solver configuration captured at this query.
    /// Shadow replay must preserve this and may add only evidence options.
    pub solver_config: SolverConfigRecord,
    pub fun: String,
    pub desc: String,
    pub span: String,
    pub ambient_batches: u64,
    /// For focused queries: labels in scope (the per-obligation premise scope
    /// `I_{q,j}`). Batch queries carry their scope implicitly as
    /// `occurrences`.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    #[serde(default)]
    pub available: Vec<String>,
    pub occurrences: Vec<Occurrence>,
    pub results: Vec<String>,
    /// Outcome of the instrumented shadow run ("valid", "invalid", ...,
    /// "unmeasured" if shadow solving was unavailable).
    pub shadow_result: Option<String>,
    /// `unsat_core` or `proof_enabled_unsat_core` when a core was obtained.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub evidence_backend: Option<String>,
    /// UNSAT core of the shadow run: `None` = missing (not measured),
    /// `Some([])` = empty core — different states by design.
    pub core: Option<Vec<String>>,
}

/// Which named slot of a lowering template emitted an occurrence.
///
/// Mirror of `vir::observer::EmissionSlot`; this crate deliberately does not
/// depend on `vir`. Producer-internal for now: it carries exact clause
/// identity from the lowering sidecar to the artifact join so the join does
/// not have to go through spans.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EmissionSlot {
    LoopEstablish,
    LoopBodyEntry,
    LoopMaintain,
    LoopExit,
    LoopAtBreak,
    LoopAtContinue,
    LoopEntryCondition,
    LoopExitCondition,
    BranchThen,
    BranchElse,
    BitVectorFunctionEnsures,
    BitVectorAssertQueryEnsures,
}

impl EmissionSlot {
    /// The emission role this slot realizes. The slot is a producer-side
    /// constant recorded at the emission point; this is where the typed role
    /// of a loop or branch fact comes from.
    pub fn role(self) -> EmissionRole {
        match self {
            Self::LoopEstablish => EmissionRole::LoopInvariant { point: LoopPoint::Establish },
            Self::LoopBodyEntry => EmissionRole::LoopInvariant { point: LoopPoint::BodyEntry },
            Self::LoopMaintain => EmissionRole::LoopInvariant { point: LoopPoint::Maintain },
            Self::LoopExit => EmissionRole::LoopInvariant { point: LoopPoint::Exit },
            Self::LoopAtBreak | Self::LoopAtContinue => {
                EmissionRole::LoopInvariant { point: LoopPoint::Transfer }
            }
            Self::LoopEntryCondition => EmissionRole::LoopEntryCondition,
            Self::LoopExitCondition => EmissionRole::LoopExitCondition,
            Self::BranchThen => EmissionRole::BranchCondition { arm: 0 },
            Self::BranchElse => EmissionRole::BranchCondition { arm: 1 },
            Self::BitVectorFunctionEnsures => EmissionRole::FunctionEnsures,
            Self::BitVectorAssertQueryEnsures => EmissionRole::AssertQuery {
                section: ContractSection::Ensures,
                point: AssertQueryPoint::Check,
            },
        }
    }

    /// Whether the slot emits one declared loop invariant clause per statement.
    pub fn carries_clause(self) -> bool {
        matches!(
            self,
            Self::LoopEstablish
                | Self::LoopBodyEntry
                | Self::LoopMaintain
                | Self::LoopExit
                | Self::LoopAtBreak
                | Self::LoopAtContinue
        )
    }
}

/// Exact identity of the clause and slot that emitted an occurrence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EmittedClause {
    pub slot: EmissionSlot,
    /// Index into the declaring clause list, never into a projection of it.
    pub clause: Option<usize>,
    /// SST loop id owning the clause, for loop slots.
    pub loop_id: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Occurrence {
    /// Structural path within the query tree (placement).
    pub path: String,
    pub role: Role,
    pub carrier: Carrier,
    pub origin: Origin,
    /// Why this occurrence exists: the emitting construction and its protocol
    /// position. `None` only for unresolved rows. The former `phase` string is
    /// rendered from this (`Occurrence::phase`), not stored.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub emission: Option<EmissionRole>,
    /// Recovered source span (obligations: from the error message; premises:
    /// from SST correlation).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub assert_id: Option<String>,
    /// Bounded head-shape summary, emitted for unresolved rows (gap analysis).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub shape: Option<String>,
    /// Activation label of this occurrence in the shadow query (join key
    /// against `QueryRecord.core`; opaque to consumers).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
    /// CFG node placement (source-level), when derivable.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub node: Option<String>,
    /// Source artifact this occurrence uses/checks, when joined.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub artifact: Option<String>,
    /// Ledger rule id (crate::rules) that justified the origin attribution.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub rule: Option<String>,
    /// Ledger rule id that justified the artifact join, when artifact is set.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub join_rule: Option<String>,
    /// Op-skeleton signature (internal, alignment only).
    #[serde(skip)]
    pub sig: Option<String>,
    /// Exact emitting slot and declared clause, from the lowering sidecar.
    ///
    /// Producer-internal: it carries construction-site identity from the AIR
    /// walk to the artifact join, replacing the span join for the slots the
    /// sidecar covers. Not on the wire yet; serializing it is what retires the
    /// `phase` string.
    #[serde(skip)]
    pub emitted: Option<EmittedClause>,
    /// Exact SST/CFG source node supplied by the passive lowering sidecar.
    /// This is serialized separately as a `lower_statement` derivation.
    #[serde(skip)]
    pub lowering_node: Option<String>,
    /// Producer-internal: the function a type-invariant assumption applies,
    /// consumed by the artifact join and not serialized (the join is).
    #[serde(skip)]
    pub subject_fn: Option<String>,
}

impl Occurrence {
    /// The protocol position, rendered from the typed emission role.
    pub fn phase(&self) -> Option<String> {
        self.emission.as_ref().and_then(EmissionRole::phase)
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Origin {
    pub kind: OriginKind,
    /// source: what construct; derived/generated: the generator (and subject,
    /// e.g. the callee); unresolved: the reason bucket.
    pub detail: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Role {
    Premise,
    Obligation,
}

#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct Summary {
    pub queries: u64,
    pub premises: u64,
    pub obligations: u64,
    pub unresolved_premises: u64,
    pub unresolved_obligations: u64,
    /// Unresolved counts per reason bucket — the work-remaining ledger.
    pub unresolved_buckets: Vec<(String, u64)>,
    pub results: Vec<(String, u64)>,
}

/// An anonymous local lemma: `assert(..) by(prover) requires ..` verified in
/// its own solver query. Requires clauses are hypotheses assumed inside the
/// inner query and *checked* in the outer query; the asserted formula is the
/// obligation of the inner query and assumed in the outer one afterwards.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct LemmaRecord {
    /// Span of the whole assert-query statement; the inner query's context
    /// span equals this, which is the query<->lemma join key.
    pub span: String,
    /// "nonlinear_arith" | "bit_vector"
    pub mode: String,
    /// Clause spans, in declaration order.
    pub requires: Vec<String>,
    pub ensures: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct CfgRecord {
    pub entry: String,
    pub exit: String,
    pub nodes: Vec<CfgNode>,
    pub edges: Vec<CfgEdge>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CfgNode {
    /// Structural path (identity).
    pub id: String,
    pub kind: CfgNodeKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CfgEdge {
    pub from: String,
    pub to: String,
    pub kind: CfgEdgeKind,
}

/// One SCC-internal (recursion-guarded) call site.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct RecursiveCallRecord {
    pub callee: String,
    /// CFG node of the call itself.
    pub call_node: String,
    /// CFG node of the termination guard (the CheckDecreaseHeight assert).
    pub guard_node: String,
    /// Call span (also the guard's span, by construction).
    pub span: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub loop_span: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub lemma_span: Option<String>,
}

#[cfg(test)]
mod wire_format_tests {
    use super::*;

    /// The record's wire spellings are its format. `Display` exists so the
    /// producer can render the vocabulary it serializes; if the two ever
    /// disagree, records and the strings in reports drift apart silently.
    #[test]
    fn wire_spellings_match_serde() {
        fn check<T>(all: &'static [T])
        where
            T: Serialize + std::fmt::Debug + std::fmt::Display,
        {
            assert!(!all.is_empty());
            for variant in all {
                let serialized = serde_json::to_value(variant).expect("enum serializes");
                let spelling = serialized.as_str().expect("enum serializes to a string");
                assert_eq!(
                    spelling,
                    variant.to_string(),
                    "serde and Display disagree for {:?}",
                    variant
                );
            }
        }

        check(ArtifactKind::ALL);
        check(OriginKind::ALL);
        check(LoopInvariantGroup::ALL);
        check(Transform::ALL);
        check(QueryFamily::ALL);
        check(Carrier::ALL);
        check(Role::ALL);
        check(CfgNodeKind::ALL);
        check(CfgEdgeKind::ALL);
    }

    /// Every typed value the record can report must survive a round trip.
    /// The `Serialize`-only schema could not state this invariant at all.
    #[test]
    fn record_enums_round_trip() {
        fn round_trip<T>(all: &'static [T])
        where
            T: Serialize + serde::de::DeserializeOwned + std::fmt::Debug + PartialEq,
        {
            for variant in all {
                let json = serde_json::to_string(variant).expect("serializes");
                let back: T = serde_json::from_str(&json).expect("deserializes");
                assert_eq!(&back, variant);
            }
        }

        round_trip(ArtifactKind::ALL);
        round_trip(OriginKind::ALL);
        round_trip(LoopInvariantGroup::ALL);
        round_trip(Transform::ALL);
        round_trip(QueryFamily::ALL);
        round_trip(Carrier::ALL);
        round_trip(Role::ALL);
        round_trip(CfgNodeKind::ALL);
        round_trip(CfgEdgeKind::ALL);
    }

    /// The query-local axiom carrier is not snake_case, so it cannot be
    /// derived by a blanket rename. Pin it explicitly.
    #[test]
    fn query_local_axiom_carrier_keeps_its_wire_spelling() {
        assert_eq!(Carrier::QueryLocalAxiom.as_str(), "axiom(query_local)");
        assert_eq!(
            serde_json::to_value(Carrier::QueryLocalAxiom).unwrap(),
            serde_json::Value::String("axiom(query_local)".to_string())
        );
    }

    /// `is_clause` replaced a `kind.ends_with("_clause")` test in the
    /// analyzer. Prove the typed predicate decides exactly the same set, so
    /// the replacement cannot have changed which artifacts are clauses.
    #[test]
    fn is_clause_agrees_with_the_spelling_it_replaced() {
        for kind in ArtifactKind::ALL {
            assert_eq!(
                kind.is_clause(),
                kind.as_str().ends_with("_clause"),
                "is_clause disagrees with the old suffix test for {kind:?}"
            );
        }
    }

    /// The emission role is a tagged object on the wire, and the `phase`
    /// string consumers display is rendered from it. Pin the wire shape and
    /// the rendering for the roles the protocol rules quantify over, so a
    /// renamed variant cannot silently change either.
    #[test]
    fn emission_role_wire_shape_and_phase_rendering() {
        let cases: &[(EmissionRole, &str, Option<&str>)] = &[
            (
                EmissionRole::FunctionRequires { clause: 2 },
                r#"{"kind":"function_requires","clause":2}"#,
                Some("function.requires"),
            ),
            (
                EmissionRole::FunctionEnsures,
                r#"{"kind":"function_ensures"}"#,
                Some("function.ensures"),
            ),
            (
                EmissionRole::CallPostcondition { callee: "c::f".into() },
                r#"{"kind":"call_postcondition","callee":"c::f"}"#,
                Some("call.post"),
            ),
            (
                EmissionRole::CallPrecondition { callee: None },
                r#"{"kind":"call_precondition"}"#,
                Some("call.pre"),
            ),
            (
                EmissionRole::LoopInvariant { point: LoopPoint::Transfer },
                r#"{"kind":"loop_invariant","point":"transfer"}"#,
                Some("loop.at_transfer"),
            ),
            (
                EmissionRole::AssertQuery {
                    section: ContractSection::Ensures,
                    point: AssertQueryPoint::Check,
                },
                r#"{"kind":"assert_query","section":"ensures","point":"check"}"#,
                Some("lemma.goal"),
            ),
            (
                EmissionRole::BranchCondition { arm: 1 },
                r#"{"kind":"branch_condition","arm":1}"#,
                Some("control.branch_arm:1"),
            ),
            (
                EmissionRole::TypeInvariant { site: TypeInvariantSite::Statement },
                r#"{"kind":"type_invariant","site":"statement"}"#,
                None,
            ),
            (
                EmissionRole::Assumed { intent: AssumeIntent::CheckedCondition },
                r#"{"kind":"assumed","intent":"CheckedCondition"}"#,
                None,
            ),
        ];
        for (role, wire, phase) in cases {
            assert_eq!(&serde_json::to_string(role).unwrap(), wire, "wire shape of {role:?}");
            let back: EmissionRole = serde_json::from_str(wire).unwrap();
            assert_eq!(&back, role);
            assert_eq!(role.phase().as_deref(), *phase, "phase rendering of {role:?}");
        }
    }
}
