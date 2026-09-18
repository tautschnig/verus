# Proof coverage: why the model has this shape

The reasoning behind the contract in `PROOF_COVERAGE.md`: where the taps sit and
why they cannot sit elsewhere, what each one closes, why the graph is a
hypergraph with a fixed point, and which layer a given statement belongs to.

## 1. Where to observe

```text
Rust HIR → VIR AST → Pruned VIR AST → SST → Structured AIR
                                                   │
                                            Versioned AIR   (SSA:  var_to_const)
                                                   │
                                              WP AIR        (WP:   block_to_assert)
                                                   │
                                              SMT Solver
```

Two rules place every observation.

**Verus has the structure but not the names.** At each stage the compiler holds
richly typed data, but nothing in it is an addressable, serializable identity
that survives to the solver. We mint the names.

**Observe at the last stage before the pipeline destroys the referent.**

| Pass | What it destroys | Consequence |
|---|---|---|
| simplification | source contract shape; introduces helper functions | contract clause identity must be minted above it |
| `sst_to_air` | the correspondence between source statement and emitted assertion | provenance must be recorded *during* it |
| `var_to_const` (SSA) | the correspondence between a term and a source variable | nothing below this can be attributed to source |
| `block_to_assert` (WP) | the CFG; the whole body becomes one assertion | statements stop being addressable at all |

So **Structured AIR is the last stage where a premise is still a statement in a
place.** Below it there is nothing left to be covered.

## 2. The taps

The producer is a passive `VerificationObserver`. Canonical verification is never
instrumented. Six tap points, all in `proof_coverage/src/lib.rs`. Each hook
pushes a `RawEvent` onto a buffer; `on_finish` drains it in order and only then
runs the handlers and the shadow pipeline, so record content cannot depend on
callback interleaving.

| Tap | Taken from it | Built into | Consumed by |
|---|---|---|---|
| `on_krate_pre_simplify` | function raw paths and friendly names; `requires` / `ensures` / `returns` / `decreases` clause spans; `TraitMethodImpl` → trait method; the verifier's `CrateId` | `Artifact` (function, req/ens aggregate, req/ens clause), `refinements`, `source_functions` | source projection; trait projection; span display |
| `on_function_sst` | one recursive walk of the exact `FuncCheckSst`: control graph + assume rows + loop records (invariant spans, protocol nodes) + call sites + assert-query regions + recursion guards | `SstSite`, `Region`, `CfgRecord`, loop/call/lemma artifacts | protocol licensing rules; CFG placement |
| `on_context_installed` | installed `Commands`, install reason, replay config | `AmbientRecord` (label, owner, op, contexts) | ambient roots; ambient-support findings |
| `on_query` | which construction emitted each coverable AIR site; the query; the effective solver config | `QueryRecord`, `Occurrence` {`path`, `Role`, `Carrier`}, `Emission` | vertices; emission role; scope |
| `on_query_result` | `valid \| invalid \| canceled \| type_error \| unexpected_output` | `QueryRecord.results` | admissibility: evidence is accepted only under a canonically valid parent |
| `on_finish` → `shadow.rs` | **the measurement** | `Terminal`, `FocusedQuery`, `EvidenceBinding`, `Evidence` | the single `SupportedBy` relation |

### Snapshot 1 — source VIR, before pruning

`FunctionX` gives clause expressions in declaration order with spans, and the
impl→trait relation. `ensure` is a pair because postconditions can be layered:
`ensure.0` is what the function declares, `ensure.1` what a trait default
contributes. Omitting `ensure.1` would silently lose postconditions on exactly
the functions whose findings depend on `refines`.

Verus has no addressable notion of *"requires clause 0 of `f`"* — a clause is a
position in a `Vec<Expr>`, and after simplification that expression may be
rewritten, split or inlined. So clause identity is minted here from
`(owner, kind, ordinal)`:

```text
example::f#req      requires aggregate
example::f#req[0]   requires clause 0
example::f#ens[0]   ensures clause 0
```

This is the only place contract spans exist. They are taken here and never
copied forward, which is why a later stage cannot silently disagree with them.

**Pre-pruning, not `on_krate`.** `on_krate` is bucket-local and receives a
*pruned* crate, so inventorying there made the record depend on whether
verification ran serially or in parallel. The gate checks serial/parallel byte
determinism because this class of mistake is easy to make. `local` additionally
needs the verifier's `CrateId`, which the merged `Krate` does not carry;
without it vstd's broadcast lemmas look local and the user's functions imported.

### Snapshot 2 — the exact post-assignment SST

The tap receives the `FuncCheckSst` that `sst_to_air` will consume, after
`compute_assign_info`. It is the last IR where loops are still loops and calls
are still single statements; structured AIR has dismantled both, and a loop body
may live in a different query.

Two things Verus already provides, so the corresponding record fields are
transcriptions rather than inventions: `Assume(AssumeIntent, Exp)` already
carries a construction-site tag ("it has no effect on verification"), and
`LoopInv`'s `(at_entry, at_exit)` booleans already spell out the three declared
groups. Our `LoopInvariantGroup` is that comment transcribed, and it exists
because those two flags decide which protocol positions may license an export —
without them every clause would be assumed to export at exit, which is wrong for
`invariant_except_break`.

Four gaps this closes:

- **`SstSiteId` as a structural path** (`b0.t.b2`). Deterministic and
  span-independent. Without it, "the same statement" means span equality, which
  fails immediately: a desugared `for` loop collapses several invariant spans
  onto the loop header.
- **`RegionId` and `RegionKind`.** Loop bodies and assert-query bodies lower into
  *separate queries*. "Same function" is too coarse a scope, "same region" is the
  right one, and Verus does not name regions.
- **`CfgRecord`.** Verus has no CFG at this level and WP later collapses it. The
  graph is presentation: node identity is the structural path, so the CFG never
  becomes semantic identity.
- **`LoopClauseRecord`** with the declared group.

Recursion is detected by observing an inserted construction, not by adding a
hook: `vir::recursion::check_termination` inserts a `CheckDecreaseHeight` assert
immediately before a recursive call, and we record that pairing as
`Call { termination_guard }`.

The walk is exhaustive over all 19 `StmX` variants but **not injective**: `Fuel`,
`RevealString`, `RevealByteString` and `Air` collapse into one generic
`CfgNodeKind::Stmt`. That is acceptable only because the distinction is
recovered on the AIR side — fuel control is classified at snapshot 4, not here.
Any leaf statement whose distinction is *not* recovered later is silently lost,
so this collapse list must be re-checked whenever the analysis starts depending
on a new construct.

### Snapshot 3 — SST → Structured AIR

Verus already computes the correspondence and hands over a typed emission site
plus the full lowering stack (`LoweringProvenance` in `vir/src/observer.rs`).
All of it is **pointer identity and process-local**, so the producer's job at
this snapshot is exactly one thing: **pointer → structural path**, using the
index only snapshot 2's walk can build. The two are not independent taps; they
are a producer/consumer pair inside the producer. If `lowered_body` is absent,
exact translation is impossible and `require_lowering_provenance` records that
by leaving the query unmeasured.

What `emitted_at` buys beyond the site: **one SST statement emits several AIR
occurrences.** A loop emits its invariant clause at establish, body-entry,
maintain and exit. The site says which loop; the emission position says which of
the four. Without the position, four occurrences of one clause are
indistinguishable and the loop rule has nothing to quantify over.

`source_chain` carries the full outer-to-inner chain; the producer keeps the
nearest frame resolvable in the observed tree, which Verus's own comment
sanctions. Nesting is therefore discarded, and `RegionId` recovers loop and
assert-query nesting independently — a decision to revisit if a rule ever needs
the intermediate frames.

### Snapshot 4 — Structured AIR

A query is local declarations plus one assertion tree. There is no notion of an
occurrence and no notion of which statements are coverable, so three things must
be minted:

- **`AirSiteId`** — an addressable name per coverable position. Its two variants
  are forced, not chosen: `QueryX` has two fields, and a query-local axiom is a
  `Decl` in `local` that no statement path can address.

  ```rust
  enum AirSiteId { LocalAxiom(u32), Statement(AirPath) }
  ```

- **`role`** — a transcription: `StmtX::Assume` → `Premise`, `StmtX::Assert` →
  `Obligation`. Coverage is meaningless without knowing hypothesis from goal.
- **`carrier`** — strictly finer than `role`, which is why both exist. `Assume`
  and `QueryLocalAxiom` are both premises, but one is a statement and one is a
  declaration, and that decides the instrumentation binding mode: statement
  occurrences are *guarded* by an activation constant, axioms are *named
  directly*.

Some structure crosses the SST→AIR boundary and is read from AIR shape directly:
`Switch(Stmts)` was `StmX::If`, so the first premise in an arm is the branch
condition, and the arm is where SSA reconciliations of non-assigning arms land;
`Breakable(Ident, Stmt)` was `StmX::Loop`, and its label is Verus's own
`break_label%<id>` carrying the SST `loop_id` — one place identity legitimately
crosses inside a name, and reading it is observation rather than archaeology.

### The measurement

Not a snapshot. It branches off Structured AIR into a clone, so canonical
verification is never instrumented.

```text
Structured AIR
   └─ clone ─→ instrument_query ─→ Labeled Structured AIR
                                      └─ focused_queries ─→ N+1 queries
                                                              └─ SMT ─→ UNSAT cores
```

`instrument_query` mints, per `QuerySiteId`, a boolean constant `pc_z%<q>%<n>`
asserted as a **`:named` unit axiom** labelled `pc%<q>%<n>`, and guards the
site's formula with it. Because the label names the *activation axiom*, a core
containing it identifies the site exactly — no formula matching, no name
parsing. Query-local and ambient axioms are named directly instead.

`decompose` splits each obligation into terminals whose conjunction is
equivalent to the original: it descends conjunctions, descends implication
consequents while retaining the antecedent, descends `forall` and `let` bodies
while retaining the binder, and **never splits disjunctions**. A formula with no
applicable rule is its own single terminal. Splitting a disjunction would invent
a claim about which disjunct carried the proof, and the core does not say that —
the same reason witness tails stay joint.

One focused query per terminal replaces the target assert with `z_t && terminal`
under a fresh label, leaving the premise scope intact, then `get-unsat-core`.

The clone is otherwise byte-for-byte the canonical query: statements are guarded,
not rewritten. That leaves one class of fact no statement in the clone carries —
the equalities `var_to_const` generates, one per `Assign` and one per mutable
local whose version differs across a control-flow join. These are labelled where
they are born:

- `air::var_to_const` records a passive `SsaTrace` — every `Assume` it generates,
  in order, tagged with the input statement's pointer and, for a reconciliation,
  the join kind, variable and versions. The transformation is untouched.
- `Context::ssa_rewrite` is an optional hook the pass calls after SSA and before
  `block_to_assert`. It is unset on every canonical context. The shadow sets it
  on its own replay context to wrap each traced equality as `Assume(z ⇒ eq)`.
- The shadow computes the trace once up front on its own clone, to mint the
  constants and name each equality's site: an `Assign`'s equality keeps that
  statement's `QuerySiteId::Statement`; a reconciliation gets a
  `QuerySiteId::Reconciliation { at, join, var, from, to }`. At solve time the
  hook checks the actual trace against the plan position by position and fails
  closed (`ssa_trace_mismatch`, no evidence) on any disagreement, so a change to
  the SSA pass cannot silently mislabel.

This is the one point where a fact lives only in a compiler pass's output, and
it is covered by the pass reporting what it did, never by matching formula
shapes afterwards.

## 3. The four layers

Four different kinds of statement used to live in one vocabulary. Naming them is
most of the design.

```text
L1  record       observations. Per-run facts from the taps.
L2  fact graph   mechanical translation of L1 into graph vocabulary. No policy.
L3  argument     licensing rules, groundedness, the least fixed point, boundaries.
L4  findings     labelling L3 results against L1 artifacts.
```

The test that decides which layer a thing belongs to:

> If a reviewer rejected your definition of proof dependency, would this row
> change?

If yes it is L3; if no it is L1. A second, independently written set of taps over
the same Verus run must reproduce L1 exactly, without knowing your definition of
dependency.

The loop protocol shows the cut running through one construct:

- **L1.** Invariant clause `x > 0` has four occurrences in this query — at
  establish, body-entry, maintain and exit — each with its emission role, all
  projecting to one source `ArtifactId`. And: the focused query for terminal
  `Maintain(y>0)` had `BodyEntry(x>0)` among its evidence members.
- **Not L1.** "Establish + Maintain licenses Exit." Nothing observed that. It is
  an inference rule about Verus's loop protocol, and exactly the kind of claim a
  reviewer can argue with.

The record's job is to supply *typed distinctions*; the analyzer's is to supply
*licensing rules quantified over those distinctions*. The loop point must be in
the record because the L3 rule ranges over it: same artifact, same clause, four
occurrences, different roles. Without a typed point the analyzer would have to
recover phase from statement order or spans.

This gives the pruning criterion to apply to any proposed field:

> Every record field must be named by a specific analyzer rule or projection
> that consumes it. Unnamed → delete, or demote to debug-only.

In code:

```text
facts::facts(records)          L2   record → fact graph. Mechanical and total.
                                    SupportedBy enters through one function,
                                    facts::evidence, the only reader of a
                                    query's core.
licensing::LicensingRule::ALL  L3   seven rules, applied in order, each a
                                    paragraph on the enum variant:
                                      1 loop protocol (group-derived tails)
                                      2 assert-query protocol
                                      3 assert protocol
                                      4 assert-forall protocol
                                      5 contract, callee side
                                      6 recorded checked exports
                                      7 calls (ordinary and recursive)
licensing::demand_calls        L3   rule 6's call-local relations, kept out of
                                    the static arc set.
analysis::build                     composition; owns grounding, slicing,
                                    explanation.
```

`tests/layering.rs` checks over the fixture corpus that the fact graph carries no
licensing arc, that static rules produce only `CertifiedBy` arcs whose heads are
premises or artifacts, that demand relations are not materialized as
target-independent arcs, and that the composed graph passes its structural
check. `SliceOptions` has no `Default`, so slice policy is named at every call
site.

## 4. Why a hypergraph, and why the fixed point is not optional

```rust
enum ArcKind {
    SupportedBy,       // from a focused core: the premises one terminal's discharge consumed
    TerminalOf,        // {terminals} → parent obligation (conjunction)
    CertifiedBy,       // checked obligations → exported assumption
    Aggregates,        // {clause artifacts} → aggregate artifact
    Demand,            // call-local licensing, kept out of the static arc set
    ObservedInBatch,   // weak joint {core premises} → {core obligations}
    ElaboratesTo,      // artifact → occurrence; the deletion/display relation
}
```

`SupportedBy` is the only evidence-bearing dependency arc. **Tails are jointly
sufficient**: flattening one into pairwise premise-to-terminal edges would
assert something the solver never said.

That is what makes the fixed point necessary, and it is worth being precise
because "we already traverse with a visited set" sounds like it should be enough.
There are two least-fixed-point operators:

- **Forward grounding** is the LFP of a *conjunctive* operator: a fact is
  grounded only if *all* members of some tail are grounded. Base cases are
  background vertices, ambient labels, and premise occurrences with no
  `CertifiedBy` in-edge.
- **Backward slicing** expands productive static arcs and re-evaluates
  call-local relations.

The `silly` example is the trap:

```rust
while i < 5
    invariant x > 0, y > 0, z > 0,
{
    if y < 0 { z = -z; }   // maintaining z>0 needs y>0
    if x < 0 { y = -y; }   // maintaining y>0 needs x>0
    i = i + 1;
}
```

```text
ensures z>0            ← Exit(z>0)
Maintain(z>0)          ← BodyEntry(y>0)
Maintain(y>0)          ← BodyEntry(x>0)
Maintain(x>0)          ← BodyEntry(x>0)      // self-edge
BodyEntry(x>0)         ← Establish(x>0) ∧ Maintain(x>0)
```

A memoizing backward DFS marks `BodyEntry(x>0)` in progress, walks to
`Maintain(x>0)`, returns, sees it visited, and accepts. It gets the right answer
by luck. The cycle *is* well founded — but because the loop's entry check
supplies a base case and licenses the hypothesis, which is an induction
principle, not because the cycle is benign. So:

> A cycle must be discharged by a named protocol tail with independently
> grounded obligations, never tolerated by a visited set.

Two consequences, both simplifying. **Licensing is explicit graph data, not
traversal folklore** — static protocols are `CertifiedBy` arcs, calls are typed
relations, and both can be shown to a reader and argued with. **Nested loops
need no nested fixed point** — one LFP over one graph containing both loops'
certificates handles arbitrary nesting; nesting the fixed point would make the
result depend on evaluation order. The same holds for composition, because
certificates are just more hyperarcs over typed identities.

There is also a soundness argument, not merely a completeness one. A one-step
backward pass from `silly`'s postcondition reaches only `z > 0`, so `x > 0` and
`y > 0` would be reported `available-not-observed` — a false "unused
specification" finding for two clauses that are load bearing. The fixed point is
required for the findings to be *correct*, and `auxiliary-support` should
therefore be reserved for genuinely different cases, such as a requirement used
only by an overflow check, rather than used as a hedge for missing transitivity.

The cascade a root set implies — drop an intermediate fact and everything that
supported only it becomes useless — falls out of recomputing the fixed point. It
needs no rule of its own.

## 5. Closed vocabularies

Every closed value set the record reports is an enum with its exact wire
spelling, and a test proves `Display` and `serde` cannot drift apart. `family`,
`carrier`, `kind`, `group` and `transform` are literal constants in the producer,
so an unknown spelling is rejected at parse time. `shadow_result` and the ambient
install op are built dynamically, so they stay strings — pretending otherwise
would be a lie the type system would then enforce.

Derived values are derived, not stored: storing a copy forces every consumer to
trust the copy rather than the relation, and lets the copy drift.

Semantic enums get no `Default`. Only plumbing containers (`CoverageRecord`,
`FunctionRecord`, `CfgRecord`, `SolverConfigRecord`) derive it. A default `Role`
or `QueryFamily` would invent an observation, and an invented observation is
worse than a missing one — which is why `Gap` is a first-class row.

## 6. Fallbacks

A fallback is an attribution made by inference when exact provenance is absent.
Three claims, in order of what they protect:

1. **A fallback cannot make Verus unsound.** Canonical verification is never
   instrumented; shadow runs are separate queries in a separate context with the
   recorded configuration preserved.
2. **A fallback cannot corrupt the measurement.** "Was this token in the core"
   is set membership on the solver's own output. No fallback participates.
3. **A fallback can corrupt an attribution**, and therefore a finding. This is
   the actual risk, and it is a soundness property of *our claims*, not of the
   proof.

What makes it defensible: every fallback-derived attribution cites a rule id, so
any finding it licenses is auditable back to the inference that produced it;
ambiguity fails closed to `Unresolved`, and an unresolved row makes its
containing derivation `Partial`; and the audit type-checks fallback joins.

On both measured populations the declared-fallback citations are zero and the
remaining fallback code is dead (`PROOF_COVERAGE_GAPS.md` §5). What survives is
the principle: a join that cannot be made exact must be visible as a gap, not
guessed.

## 7. The contribution in one sentence

Proof coverage requires the VC generator to record, at emission time, **which
source construct and which output position** each assertion came from — and
observation must happen at the last IR where assertions are still addressable
statements. Everything else in the producer is either an identity scheme implied
by that requirement, or Verus encoding absorbed to avoid changing the verifier.

### What generalizes, and what is Verus

| Generalizes | Verus-specific |
|---|---|
| A VC generator should emit provenance as a first-class output; the correspondence is nearly free at emission time and unreliable to recover afterwards. The *emission position*, not just the source site, disambiguates the several assertions one source statement produces. Clause ids minted from `(owner, kind, ordinal)`. Structural-path identity for statements and for coverable positions. Explicit region nesting, because sub-bodies become separate queries. Building the CFG as presentation, never identity. Premise/obligation as the coverage axis. Separating axiom positions from statement positions, because they bind differently. Observing the exact body that lowers, not a reconstruction. A pointer-keyed sidecar must be resolved to structural identity before serialization. | `ensure` being a pair for trait defaults; a separate `returns` clause needing deduplication; `FunctionKind::TraitMethodImpl` as the refinement source; the pruned-crate determinism hazard. `AssumeIntent`'s variant list; `compute_assign_info` as the cut point; `CheckDecreaseHeight` as the recursion signal; `LoopInv`'s flag pairing; `by(nonlinear_arith \| bit_vector)` modes. `LoweringSite` mirroring `sst_to_air`; `QueryAssembly` for AIR with no SST parent; `lowered_body` being optional. Three carriers, because Verus emits query-local axioms; AIR's tree shape. |
