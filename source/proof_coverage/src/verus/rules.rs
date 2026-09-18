//! The provenance rule ledger.
//!
//! Every attribution the consumer makes — assigning an origin family to an
//! occurrence, or joining an occurrence to an artifact — must cite a rule
//! from this table by id. The audit enforces that:
//!   - attributed rows cite a rule that exists here,
//!   - no attributing rule has `Strength::Heuristic` (heuristic conclusions
//!     must stay `Unresolved` instead),
//! and reports per-rule usage so completeness is measurable per rule and
//! per construct.
//!
//! Strength taxonomy (weakest evidence a rule relies on):
//!   - Construction: keyed on object identity created by the producer
//!     (e.g. `Arc::ptr_eq` with a lowering that clones one allocation into
//!     two positions). Cannot misfire without the producer changing.
//!   - TypedVocabulary: keyed on names/constants exported by the producer
//!     (`vir::def` prefixes, `AssumeIntent` tags, exact message constants).
//!     Misfires only if the vocabulary is reused for something else.
//!   - Protocol: keyed on a documented emission order or count agreement
//!     (walk-order alignment, positional rules with count guards). Guarded
//!     so that violation of the protocol yields Unresolved, not a wrong row.
//!   - Heuristic: keyed on formula shape alone. Not allowed to attribute.

pub use proof_coverage_core::rule_schema::{Rule, Strength};

// ---- AIR-side vocabulary rules (classify_premise / classify_apply) ----
pub const R_FUEL: &str = "air.fuel";
pub const R_TYPE_INV: &str = "air.type_invariant";
pub const R_TRAIT_BOUND: &str = "air.trait_bound";
pub const R_CALLEE_ENS: &str = "air.callee_ensures";
pub const R_CALLEE_REQ: &str = "air.callee_requires";
pub const R_DECREASE_CHECK: &str = "air.decreases_check";
pub const R_RESOLUTION: &str = "air.resolution";
pub const R_STRING_LITERAL: &str = "air.string_literal";
// ---- walker protocol rules ----
pub const R_ASSERTED_PROP: &str = "walk.asserted_proposition";
pub const R_BRANCH_COND: &str = "walk.branch_condition";
pub const R_LOOP_EXIT_INV: &str = "walk.loop_exit_invariant";
pub const R_LOOP_EXIT_COND: &str = "walk.loop_exit_condition";
// ---- obligation message rules ----
pub const R_NOTE_VOCAB: &str = "msg.obligation_note";
pub const R_PATTERN_MATCH: &str = "msg.pattern_match";
// ---- SST alignment rules ----
pub const R_EXACT_LOWERING: &str = "sst.exact_lowering";
/// An SSA-generated reconciliation equality, identified by the SSA pass's own
/// generation trace and placed at the join statement's exact lowering.
pub const R_SSA_TRACE: &str = "ssa.trace";
pub const R_SST_ALIGN: &str = "sst.order_alignment";
pub const R_CONST_FALSE_EXCLUSION: &str = "sst.const_false_exclusion";
pub const R_SST_SIGBUCKET: &str = "sst.signature_bucket";
// ---- artifact join rules ----
pub const R_JOIN_SPAN: &str = "join.clause_span";
/// Origin taken from the slot the lowering recorded at the emission point.
pub const R_EMITTED_SLOT: &str = "sst.emitted_slot";
/// Artifact joined by declared clause ordinal recorded at the emission point.
pub const R_EMITTED_CLAUSE: &str = "join.emitted_clause";
/// Termination obligation joined to the decreases measure that owns it.
pub const R_JOIN_DECREASES: &str = "join.decreases_measure";
/// Origin and site of a query-local axiom taken from the declaration-level
/// sidecar recorded where `mk_unnamed_axiom` was called.
pub const R_EMITTED_AXIOM: &str = "sst.emitted_local_axiom";
/// A statement artifact (assume, assignment, reveal, branch) joined by the
/// exact CFG node of the statement that emitted the occurrence.
pub const R_JOIN_SITE: &str = "join.statement_site";
/// A source artifact joined through the exact VIR-origin -> SST-site map
/// resolved before process-local identities are discarded.
pub const R_SOURCE_PROVENANCE: &str = "join.source_provenance";
/// A loop-condition artifact joined by the SST loop id the lowering recorded
/// at the condition's emission slot.
pub const R_JOIN_LOOP_COND: &str = "join.loop_condition";
/// A user-defined type invariant assumption joined to the invariant function
/// the SST applies.
pub const R_JOIN_TYPE_INVARIANT: &str = "join.type_invariant_fn";
pub const R_JOIN_REQ_IDX: &str = "join.requires_index";
pub const R_JOIN_LEMMA_SPAN: &str = "join.lemma_clause_span";
pub const R_JOIN_CALLSITE: &str = "join.call_site_order";
pub const R_JOIN_AGGREGATE: &str = "join.contract_aggregate";
pub const R_JOIN_ASSERT: &str = "join.assert_site";
pub const R_JOIN_FORALL: &str = "join.forall_site";
pub const R_JOIN_REFINEMENT: &str = "join.trait_refinement";

pub const RULES: &[Rule] = &[
    Rule {
        id: R_FUEL,
        producer: "vir::sst_to_air fuel plumbing",
        signals: "Apply of FUEL_BOOL/FUEL_BOOL_DEFAULT/FUEL_DEFAULTS, Var FUEL_DEFAULTS, \
                  or exists-witness over PREFIX_FUEL_NAT (vir::def constants)",
        conclusion: "generated/fuel",
        strength: Strength::TypedVocabulary,
        constructs: "every function query",
        negative_probes: "user function named like fuel (namespaced by %, cannot collide)",
    },
    Rule {
        id: R_TYPE_INV,
        producer: "vir typ_invariant",
        signals: "Apply of HAS_TYPE/U_INV/I_INV/SIZED_BOUND",
        conclusion: "generated/type_invariant",
        strength: Strength::TypedVocabulary,
        constructs: "all typed locals, havoc re-assumes",
        negative_probes: "",
    },
    Rule {
        id: R_TRAIT_BOUND,
        producer: "vir trait elaboration",
        signals: "Apply name with PREFIX_TRAIT_BOUND",
        conclusion: "generated/trait_bound:<trait>",
        strength: Strength::TypedVocabulary,
        constructs: "probes/traits.rs generic dispatch",
        negative_probes: "",
    },
    Rule {
        id: R_CALLEE_ENS,
        producer: "vir func_to_air contract functions",
        signals: "Apply name with PREFIX_ENSURES",
        conclusion: "source/ensures_of:<callee>",
        strength: Strength::TypedVocabulary,
        constructs: "calls (examples corpus)",
        negative_probes: "",
    },
    Rule {
        id: R_CALLEE_REQ,
        producer: "vir func_to_air contract functions",
        signals: "Apply name with PREFIX_REQUIRES",
        conclusion: "source/requires_of:<callee>",
        strength: Strength::TypedVocabulary,
        constructs: "calls",
        negative_probes: "",
    },
    Rule {
        id: R_DECREASE_CHECK,
        producer: "vir::recursion",
        signals: "Apply of CHECK_DECREASE_HEIGHT",
        conclusion: "generated/decreases_check",
        strength: Strength::TypedVocabulary,
        constructs: "recursion example",
        negative_probes: "",
    },
    Rule {
        id: R_RESOLUTION,
        producer: "vir resolution facts",
        signals: "Apply of HAS_RESOLVED",
        conclusion: "generated/resolution",
        strength: Strength::TypedVocabulary,
        constructs: "&mut params (probes/mut_params.rs)",
        negative_probes: "",
    },
    Rule {
        id: R_STRING_LITERAL,
        producer: "vir string lowering (StmX::RevealString)",
        signals: "Apply name prefixed str%/bytes%",
        conclusion: "generated/string_literal",
        strength: Strength::TypedVocabulary,
        constructs: "reveal_strlit examples",
        negative_probes: "",
    },
    Rule {
        id: R_ASSERTED_PROP,
        producer: "vir assert lowering (assert-then-assume pairs)",
        signals: "assume structurally equal to the immediately preceding assert",
        conclusion: "derived/asserted_proposition, span from the assert",
        strength: Strength::Protocol,
        constructs: "user assertions everywhere",
        negative_probes: "adversarial_loops::lookalike_assert (must not arm loop rules)",
    },
    Rule {
        id: R_BRANCH_COND,
        producer: "vir if/match lowering",
        signals: "first premise of a Switch arm, walk order",
        conclusion: "derived/branch_condition",
        strength: Strength::Protocol,
        constructs: "if/match (probes/match_enum.rs)",
        negative_probes: "",
    },
    Rule {
        id: R_EMITTED_SLOT,
        producer: "vir sst_to_air record_emission_slot (all multi-slot templates)",
        signals: "the lowering recorded the template slot at the emission point, \
                  where the slot is a compile-time constant",
        conclusion: "the occurrence's protocol position, with no ordering or shape \
                     assumption",
        strength: Strength::Construction,
        constructs: "loops (six slots), if/else, loop conditions",
        negative_probes: "emission_slots: a loop declaring invariant_except_break, \
                          invariant and ensures keeps all three distinct across \
                          every slot",
    },
    Rule {
        id: R_JOIN_DECREASES,
        producer: "vir loop_to_stmts DEC_FAIL_LOOP_END / recursion height check",
        signals: "one assert covers the whole lexicographic measure; its error span \
                  is the owning loop statement, or the obligation is the function's \
                  own termination check",
        conclusion: "source/decreases @ that measure's aggregate artifact",
        strength: Strength::Construction,
        constructs: "recursive functions, loops with decreases, nested loops",
        negative_probes: "a function or loop with no decreases clause declares no \
                          measure artifact, so the obligation stays unjoined rather \
                          than borrowing another loop's",
    },
    Rule {
        id: R_EMITTED_AXIOM,
        producer: "vir sst_to_air record_local_axiom (six query-local axiom sites)",
        signals: "the lowering recorded, at each `mk_unnamed_axiom` call, which \
                  construction emitted the AIR Decl: a requires clause by declaring \
                  ordinal, a parameter type invariant by parameter ordinal, a trait \
                  bound by ordinal, the fuel axiom, or a loop/assert-query type \
                  invariant",
        conclusion: "exact origin and protocol site for an axiom(query_local) row; \
                     requires rows carry their declaring clause ordinal, so the \
                     artifact join is identity rather than count agreement",
        strength: Strength::Construction,
        constructs: "every function body query; isolated loop and assert-query \
                     queries; generic functions",
        negative_probes: "a function with fewer unresolved local axioms than requires \
                          clauses still attributes each clause exactly",
    },
    Rule {
        id: R_JOIN_SITE,
        producer: "proof_coverage SST walk (CFG node) + lowering sidecar (statement chain)",
        signals: "the occurrence's typed role is a written statement's fact (user assume, \
                  initializing assignment, reveal, branch condition) and the lowering \
                  sidecar resolved its emitting statement to an exact CFG node",
        conclusion: "the statement artifact `<fun>#assume|assign|reveal|branch@<node>`",
        strength: Strength::Construction,
        constructs: "assume statements, let bindings, reveal, if/else",
        negative_probes: "a paired assume of a generated check keeps its CheckedCondition \
                          role and receives no assertion or assumption artifact",
    },
    Rule {
        id: R_SOURCE_PROVENANCE,
        producer: "pre-simplification source inventory + VIR span identity transport + SST walk",
        signals: "the independently declared source artifact and the exact emitting SST site \
                  carry the same process-local VIR origin; the identity is consumed before \
                  serialization",
        conclusion: "the occurrence projects to that already-declared source artifact; no \
                     artifact is created from the occurrence, its span, or its CFG shape",
        strength: Strength::Construction,
        constructs: "assignments, explicit and implicit returns, assertions, assumptions, \
                     reveals, branches, patterns, ghost/tracked bindings, mutable-reference \
                     calls, and syntax-expanded constructs",
        negative_probes: "generated iterator, pattern, wrapper, borrow, writeback, and return \
                          plumbing carries generated origin and therefore cannot acquire a \
                          source subject",
    },
    Rule {
        id: R_JOIN_TYPE_INVARIANT,
        producer: "vir ast_to_sst assert_assume_satisfies_user_defined_type_invariant",
        signals: "an SST Assume(TypeInvariant, Call(inv_fn, [value])): the applied \
                  function is the declared type invariant",
        conclusion: "the invariant function's artifact, with the statement as site",
        strength: Strength::Construction,
        constructs: "#[verifier::type_invariant] datatypes (vstd tokens, cells)",
        negative_probes: "",
    },
    Rule {
        id: R_JOIN_LOOP_COND,
        producer: "vir sst_to_air loop_to_stmts (condition slots with loop id)",
        signals: "LoopEntryCondition / LoopExitCondition slot carrying the owning SST loop id",
        conclusion: "the loop's condition artifact `<fun>#cond<i>`, shared by the entry \
                     assumption and the negated exit assumption",
        strength: Strength::Construction,
        constructs: "while loops; nested loops keep distinct ids",
        negative_probes: "",
    },
    Rule {
        id: R_EMITTED_CLAUSE,
        producer: "vir sst_to_air loop_to_stmts (declaring clause index)",
        signals: "the emission point recorded the clause's index in the declaring \
                  `invs` vector, plus the owning SST loop id",
        conclusion: "exact source clause identity, without spans or ordinals",
        strength: Strength::Construction,
        constructs: "clauses sharing a span; entry and exit populations that differ",
        negative_probes: "emission_slots: the `invariant` clause pushed into both \
                          invs_entry and invs_exit keeps one identity, and does not \
                          collide with invariant_except_break on index 0",
    },
    Rule {
        id: R_LOOP_EXIT_INV,
        producer: "vir loop_to_stmts (loop_isolation exit region)",
        signals: "Snapshot(snap%LOOP) arms the entry-check expressions; a later \
                  assume whose Expr is Arc::ptr_eq to an armed one",
        conclusion: "source/loop_invariant @ loop.exit_assume, that clause's span",
        strength: Strength::Construction,
        constructs: "nested loops, duplicate identical invariants",
        negative_probes: "adversarial_loops: duplicate invariants stay distinct; \
                          loop-ensures clauses stay Unresolved; lookalike assert can't arm",
    },
    Rule {
        id: R_LOOP_EXIT_COND,
        producer: "vir loop_to_stmts (neg_assume after exit invariants)",
        signals: "single Not(_) assume after all armed exit invariants matched, \
                  before any assert",
        conclusion: "source/loop_exit_condition @ loop.exit_condition",
        strength: Strength::Protocol,
        constructs: "while loops incl. short-circuit conditions",
        negative_probes: "adversarial_loops::unrelated_negation (disarmed by assert)",
    },
    Rule {
        id: R_NOTE_VOCAB,
        producer: "vir error message construction (Message notes)",
        signals: "obligation Message note matches a known producer string",
        conclusion: "family per note (ensures, loop invariant, decreases, overflow, ...)",
        strength: Strength::TypedVocabulary,
        constructs: "all obligations",
        negative_probes: "",
    },
    Rule {
        id: R_PATTERN_MATCH,
        producer: "vir::ast_simplify pattern refutability check",
        signals: "note == vir::def::PATTERN_MATCH_FAIL_MESSAGE (exact)",
        conclusion: "generated/pattern_match_check",
        strength: Strength::TypedVocabulary,
        constructs: "probes/match_enum.rs",
        negative_probes: "",
    },
    Rule {
        id: R_SSA_TRACE,
        producer: "air::var_to_const generation trace (SsaTrace) + lowering sidecar",
        signals: "the SSA pass recorded that it inserted `x@m == x@k` at this Switch arm, \
                  Breakable exit or Break; the join statement has exact lowering provenance",
        conclusion: "a generated premise with role SsaReconciliation{join}, node/span of \
                     the join's SST statement (If, Loop or Break), no artifact",
        strength: Strength::Construction,
        constructs: "every control-flow join where a mutable local's versions differ",
        negative_probes: "a join without a recorded lowering frame yields an Unresolved row",
    },
    Rule {
        id: R_EXACT_LOWERING,
        producer: "vir::sst_to_air passive lowering-provenance sidecar",
        signals: "AIR statement pointer maps to an exact SST lowering stack; nearest \
                  process-local SST statement identity resolves in the same query instance",
        conclusion: "origin from AssumeIntent when present, otherwise a typed lowering-site \
                     root; span/node from the exact SST/CFG statement",
        strength: Strength::Construction,
        constructs: "all structured AIR statements produced by body_stm_to_air",
        negative_probes: "duplicate SST pointer placement is discarded before joining",
    },
    Rule {
        id: R_SST_ALIGN,
        producer: "vir ast_to_sst AssumeIntent tags + sst_to_air lowering order",
        signals: "unresolved AIR assumes of a query vs SST assume rows for the \
                  same region (function body / loop / lemma), counts equal",
        conclusion: "origin from the SST intent (sst:<Intent>), span/node from SST",
        strength: Strength::Protocol,
        constructs: "all; count mismatch leaves rows Unresolved and is counted. \
                  Construction-predicted rows feed this rule: initializing \
                  assigns (sst_to_air rewrites to assume_var) and return-value \
                  bindings (sst_to_air::Return emits assume_var(dest, ret_exp) \
                  when the postcondition has a dest and ens_exps work)",
        negative_probes: "returns in functions without postconditions or \
                  without a named return destination predict no row; \
                  probes/no_post_return.rs",
    },
    Rule {
        id: R_CONST_FALSE_EXCLUSION,
        producer: "vir sst_to_air (loop_end, dead-end assumes) vs ast_to_sst UserAssume",
        signals: "an AIR const-false assume in a region whose SST rows contain \
                  zero user/tagged assume(false) rows",
        conclusion: "generated/path_termination (by exclusion: nothing user-written \
                  in this region can lower to const false)",
        strength: Strength::Protocol,
        constructs: "match dead arms, loop_end, early return",
        negative_probes: "adversarial_loops::user_assume_false (region has a \
                  UserAssume(false) SST row: every const-false row stays Unresolved)",
    },
    Rule {
        id: R_SST_SIGBUCKET,
        producer: "same as sst.order_alignment",
        signals: "per op-skeleton signature bucket, counts equal within bucket",
        conclusion: "as sst.order_alignment",
        strength: Strength::Protocol,
        constructs: "queries where full counts disagree",
        negative_probes: "",
    },
    Rule {
        id: R_JOIN_SPAN,
        producer: "tapped SST loop/contract tables",
        signals: "occurrence span == recorded clause span (owner-scoped)",
        conclusion: "artifact = that clause",
        strength: Strength::TypedVocabulary,
        constructs: "invariant/ensures clauses",
        negative_probes: "span collisions measured by audit stats",
    },
    Rule {
        id: R_JOIN_REQ_IDX,
        producer: "requires lowering order",
        signals: "requires[k] positional index into recorded requires spans",
        conclusion: "artifact = req clause k",
        strength: Strength::Protocol,
        constructs: "function requires",
        negative_probes: "",
    },
    Rule {
        id: R_JOIN_LEMMA_SPAN,
        producer: "SST AssertQuery region walk (AssumeIntent-tagged clauses)",
        signals: "occurrence span == lemma requires/ensures clause span; inner \
                  query keyed by assert-query span == query context span",
        conclusion: "artifact = lemma clause; roles per position",
        strength: Strength::TypedVocabulary,
        constructs: "by(nonlinear_arith); by(bit_vector) outer side",
        negative_probes: "",
    },
    Rule {
        id: R_JOIN_CALLSITE,
        producer: "SST call-site walk order",
        signals: "n-th requires_of:<callee> obligation in a region vs n-th \
                  recorded call site of that callee, count-guarded",
        conclusion: "placement at the call node",
        strength: Strength::Protocol,
        constructs: "repeated calls to one callee (pc_residue probe)",
        negative_probes: "",
    },
    Rule {
        id: R_JOIN_AGGREGATE,
        producer: "contract aggregate emission",
        signals: "ensures_of/requires_of family, callee (name-keyed), kind",
        conclusion: "artifact = (callee, kind) contract aggregate",
        strength: Strength::TypedVocabulary,
        constructs: "calls incl. one callee needing both aggregates",
        negative_probes: "",
    },
    Rule {
        id: R_JOIN_ASSERT,
        producer: "walker assert-then-assume pairing + exact SST/CFG placement",
        signals: "the asserted-proposition rule fired on this exact occurrence \\
                  pair (same walk, structural formula identity) and the assert \\
                  obligation is a user assertion with an exact CFG node",
        conclusion: "one `assertion` artifact keyed by the assert's CFG node; \\
                  check joins at phase assert.check, exported assumption at \\
                  assert.establish",
        strength: Strength::Construction,
        constructs: "user assert / assert-by statements (established facts)",
        negative_probes: "asserts without exact placement stay unjoined; \\
                  generated checked conditions receive no source artifact",
    },
    Rule {
        id: R_JOIN_FORALL,
        producer: "sst_to_air assert-forall lowering (DeadEnd region + sibling export)",
        signals: "a DeadEnd whose premises open with AssumeIntent::AssertForallRequire; \\
                  its last obligation is the forall goal; the next sibling \\
                  statement is an AssertForallEnsures assume carrying the same \\
                  asserted-proposition span",
        conclusion: "one `assert_forall` artifact keyed by the goal's CFG node; \\
                  goal joins at phase forall.goal, exported conclusion at \\
                  forall.establish, hypothesis phased forall.hypothesis (unjoined)",
        strength: Strength::Protocol,
        constructs: "assert forall |x| P implies Q by { .. }, including nested regions",
        negative_probes: "region without an obligation, missing sibling export, or \\
                  export span disagreeing with the goal leaves every row unjoined",
    },
    Rule {
        id: R_JOIN_REFINEMENT,
        producer: "vir::ast::FunctionKind::TraitMethodImpl names the trait method",
        signals: "the query's function is a recorded trait-method implementation \
                  and the clause span (ensures) or clause index (requires) \
                  resolves uniquely against the trait method's declared clauses",
        conclusion: "artifact = the trait's clause; the impl's own ensures checks \
                  then license it through the existing contract certificate, which \
                  is exactly contract refinement",
        strength: Strength::TypedVocabulary,
        constructs: "trait method implementations (probes/traits.rs, construct stress)",
        negative_probes: "no recorded refinement, or an ambiguous clause span, \
                  leaves the occurrence unjoined",
    },
];

pub fn lookup(id: &str) -> Option<&'static Rule> {
    RULES.iter().find(|r| r.id == id)
}
