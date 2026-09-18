# Limitations

## 1. Measurement limits

### 1.1 Formula/Expr decomposition

### 1.2 Shadow queries the instrumented clone could not prove — 15 in vstd

`invalid` 14, `proof_fallback_canceled` 1: the guarded clone (activation
literals `z ⇒ P`, `z ∧ G`) did not prove what the canonical query proved,
within the same rlimit. Solver sensitivity to the added literals, in
`arithmetic::internals`, `bytes`, `map_lib`/`imap_lib`, `iset::fold`,
`resource::impls`. Affected terminals are `Unmeasured` and their functions
`Overapproximated` (the 13 + 2 above; 64 more functions are Overapproximated
through §1.3). Options, none taken yet: retry with a higher rlimit for the
shadow only; retry without terminal splitting; or accept `Overapproximated`
as the answer for solver-fragile proofs. No fallback here may touch the
canonical verdict.

### 1.3 Non-SMT backends

`assert ... by(integer_ring)` is `CheckSingular`; there is no core. Not
present in vstd's record (`Singular check valid` queries are outside the
`CheckValid` family the observer measures). The honest treatment, when
needed, is a certificate whose check is externally discharged so the
surrounding proof still gets findings. Bit-vector queries *are* `CheckValid`
and are fully sited.

---

## 2. Population gaps — written constructs without an artifact

21 on the corpus, 111 on vstd: source-origin occurrences with exact provenance,
a CFG node and a span, lacking only an artifact identity.

```text
                                      corpus   vstd
opened-invariant blocks (§2.1)             0     48
user `assume` in an unmeasured query       0     31
assert-query clauses                       0     18
desugared `for` loop invariants (§2.4)    19      0
ensures under macro expansion (§2.2)       0      7
assertions under macro expansion (§2.2)    1      6
assert-forall                              0      1
`assumed` with no finer position           1      0
```

The fallback count and the population gap move in opposite directions, so quote
them together. Deleting `join.loop_inv_ordinal` (§5 item 1) is what left the
desugared `for` loop's invariants unjoined — the corpus's 19 rows. Trading a
positional guess for an explicit gap is the intended direction, but it raises
this table.

### 2.1 Opened invariants — 48 rows, no artifact kind

`open_atomic_invariant!` / `open_local_invariant!` blocks in `atomic_ghost`:
24 `OpenedInvariant` assumptions (the invariant's contents at open) and 24
`invariant_block.close` obligations. The construct is one written block with
two protocol positions — the same checked-export shape as an assert or loop
(open assumes `I`, close re-establishes `I`). The **licensing** half is now
closed (§4.1, rule 6 over `checked_exports`, which pairs by label and needs no
artifact). What remains here is the **artifact identity**: these 48 rows still
have no `ArtifactKind::InvariantBlock` keyed on the block's CFG node, so the
block is not a nameable source subject in findings. Zero trusted lines: the SST
`OpenInvariant` statement is already walked.

### 2.2 Clauses under macro expansion — 6 assertions, 7 ensures

`layout::{unsigned_int_max_values, signed_int_min_max_values,
usize_size_pow2}` and `endian`/`seq`: 6 `assert` obligations with a node but no
artifact. The asserted-proposition pairing did not fire for them, so they never got an
`assertion` artifact — the assumes that follow these asserts are not
pointer-equal to the assert's formula (macro-generated `assert` chains).
The assert-site join should key on the SST `Assert` statement's own node, not
on the following assume; that is a producer change to `join.assert_site`.

`arithmetic::overflow::Checked*::to_option` (6) and
`std_specs::iter::VerusForLoopWrapper::next` (1): ensures obligations whose
span (inside a macro expansion, `#67`..`#97`) does not match any inventory
clause span, so `join.clause_span` fails closed. These are the 7 `local
ensures_clause` instrumentation gaps. The fix is the one this document has
asked for since the slot change: record the ensures clause ordinal at the
emission point (`ens_exprs` in `body_stm_to_air`), as loops and bit-vector
queries already do, and retire the span join for ensures entirely.

### 2.3 Desugared `for` loop invariants — 19 rows on the corpus

`for_loop::sum_to`'s invariant population collapses onto the loop header and the
iterator expression, so `join.clause_span` cannot discriminate, and the ordinal
rule that used to break the tie is deleted. Every protocol position of the loop
is affected (establish 3, body-entry 3, maintain 3, transfer 5, exit 5). The fix
is the one §2.2 asks for: record the clause ordinal at the emission point, as
`sst_to_air`'s slots already do for ordinary loops, so `for` desugaring stops
needing a tie-break at all.

### 2.4 Everything else is covered

Loop conditions, branch conditions, user `assume`, initializing `let`,
return bindings, `reveal`, mutations, decreases measures, assert-forall
regions, bit-vector requires/ensures, user-defined type invariants (joined
through the hoisted temporary to the invariant function, 292 rows in vstd)
all have artifacts. Generated facts — parameter and statement type
invariants, fuel, trait bounds, overflow and pattern-match checks, path
terminations, `has_type`, mutable-reference current values, checked
conditions of generated asserts — are correctly subject-free and carry a
site.

---

## 3. Identity and granularity

### 3.1 Friendly function names are not injective — closed; identities are raw paths

The collision is a property of Verus's display naming, not of its identities.
`rust_to_vir_base::set_path_as_rust_name` maps an impl method's raw path to
`<self-type path>::<method ident>`, discarding both the impl disambiguator and
the self type's generic arguments; `path_as_friendly_rust_name` then returns
that spelling. So every same-named method of several impls for one type
constructor renders identically: `vstd/std_specs/borrow.rs` declares `View`
for `Cow<'a, T>`, `Cow<'a, str>` and `Cow<'a, [T]>`, and all three `view`
methods are `alloc::borrow::Cow::view` (raw paths `impl&%0`, `%2`, `%4`);
`core::ops::range::Range::spec_end_bound` is two functions, `vstd::seq::
Seq::unref` two.

Verus itself is unaffected, because it keys identity on `Fun`/`Path` and uses
friendly names only for diagnostics and for quantifier ids. The one place
upstream is exposed is `qid_map`: `sst_to_air.rs`'s `<friendly>_nondefault_
fuel` internal qid has no disambiguating counter, so `new_internal_qid`'s
`insert` silently overwrites among colliding functions and `--profile`
misattributes that quantifier. Diagnostics only; no effect on any verdict.

The proof-coverage record used to key on the friendly name, and the v0.1 audit
rejected any record containing a collision rather than merging distinct
contracts and findings — which put the 20 colliding vstd functions outside the
accepted population. The wire format now keys every identity on the raw path
(`verus::fun_identity`, built from `FunX.path` alone): artifact ids and owners,
`Artifact.callee`, `FunctionRecord.fun`, call sites, `RecursiveCallRecord`,
`QueryRecord.fun`, `AmbientRecord.owner`, and `refinements`.
`SourceFunction.friendly` carries the display name, and the analyzer renders it
(`Graph::display_function`, `Graph::display_artifact`), appending the raw path
where a friendly name is shared, so a rendering is unambiguous without being an
identity.

`trait_path` and `module` stay friendly: they are never join keys.

The audit's checks moved with the scheme. A repeated `fun` is a violation
(injectivity is now checked, not assumed); a shared `friendly` is a stat;
and every `FunctionRecord.fun` and `QueryRecord.fun` must name a snapshot-1
row, so an identity minted anywhere other than `FunX.path` fails closed.

### 3.2 Imported contracts enter as one aggregate

A callee's postcondition reaches a caller as `callee#ens`, not as its
clauses (vstd: 2363 imported clauses "unmeasured" in `analysis_coverage`,
by design). Consequences: a caller's slice through an aggregate reaches
every clause the callee proved, including ones the caller never used (the
two-crate study shows `r > 0` reaching `twice`); and the caller-side finding
"which clause of the callee's contract did I need" cannot be asked. Verus
emits `ens%f` as one predicate, so this is a genuine granularity boundary
of the encoding, not an attribution gap. Closing it needs the shadow clone
to split the `ens%f` application into its clause conjuncts (definitions are
available: the callee's ensures predicate body) — a measurement design, not
a join.

### 3.3 Trait contracts are certified relative to the recorded implementations

A generic call's trait clause is `CertifiedBy` the refinement checks of
every implementation *in the record*, and the slice records a
`trait_contract` boundary naming them. Implementations in other crates are
outside; in a multi-crate analysis the definers bridge (§7 of the analysis
contract) identifies them, otherwise the boundary is the honest statement.

---

## 4. Analysis boundaries

### 4.1 Rules, and how to see which are missing

Seven licensing rules (`licensing::LicensingRule::ALL`): loop protocol,
assert-query protocol, assert protocol, assert-forall protocol, contract callee
side, recorded checked exports, and calls (ordinary and recursive, as call-local
relations rather than static arcs — §4.1a).

Rules 1–5 pair a construct's two halves through a shared source artifact. Rule 6
exists for the constructs that have none: a generated overflow check and an
invariant block have no written statement behind them, so the producer records
the pairing directly (`CoverageRecord.checked_exports`) and the rule turns it
into `CertifiedBy`. The pairing is L1 — the walk observes it; the claim that it
licenses the export is L3.

`pc_analyze RECORD unlicensed` is the census. A premise with no licensing
in-edge is a graph **root**: the fixed point takes it on trust and never asks
what established it. Most roots are correct — a function's own `requires`, an
ambient axiom, control and data flow of the body, and a checked export's
*hypothesis* (`forall.hypothesis` is a bound variable; nothing establishes it).
A root that is really an assumption some checked construct *exported* is a hole,
and it fails **open**: every fact that supported only the discharge of that
export drops out of every slice and is reported unused, at `status = Complete`,
with no gap and no occlusion (§4.2a).

The census splits the holes the way the work splits.

**No licensing rule for the construct.** On vstd, none remain. On `examples/`:

```text
  rows  artifact  cfg node  positioned  fns  construct
   244         0       244          no    5  assumed/AtomicUpdate
    13         0        13          no    4  assumed/AtomicUpdateEnsures
    10         0        10          no    7  assumed/ClosureSpec
     2         0         2          no    2  assumed/ClosureRequires
    38         0        38          no    1  assumed/ExpandErrorsSplit
```

Read the columns: `cfg node` equals `rows`, so placement is already complete —
the record knows where these facts are. `artifact` is 0, so there is no identity
shared between the export and the check that licenses it. `positioned` is no, so
the role does not say which occurrence is which. Both are record relations, not
semantics.

Both remaining protocols have now been read in the verifier source, and both are
instances of the checked-export shape. Neither needs a new semantics decision.

**Atomic update — a two-sided protocol** (`ast_to_sst.rs`, `ExprX::Update` and
`ExprX::TryOpenAtomicUpdate`). Verus's own comments give the desugaring:

```text
try_open_atomic_update!  (implementer)     update(x)  (client)
  assume(req(au, x))        H                assert(req(au, x))       G
  assert(outer_mask ⊆ mask)                  assume(ens(au, x, y))    E
  ... body ...                               if branch_bool(y) {
  assert(ens(au, x, y))     G                  assume(input/output/resolves)
  if branch_bool(y) {                        }
    assume(input/output/resolves)
  }
```

So the earlier claim in this section — that no obligation carries the intent —
was wrong. The obligation exists on both sides; it is emitted as a plain
`StmX::Assert` and therefore reaches the record typed only as
`lowered { site: assert }`, which is why the census sees `artifact 0` and reads
as if there were nothing to pair with. On `examples/helping.rs` the client-side
triple is adjacent and unambiguous:

```text
b23.b15  obligation  lowered/assert           helping.rs:436:21   G
b23.b16  premise     assumed/AtomicUpdateEnsures  helping.rs:436:21   E
```

`AtomicUpdateEnsures` is thus the same fix as `CheckedCondition`: record the
adjacent (check, export) pair. The two sides split the 244 `AtomicUpdate` rows,
and most of them are **legitimate roots**, not holes:

| statement | intent | status |
|---|---|---|
| `assume(req(au,x))` on the implementer side | `AtomicUpdate` | `H` of the triple — root by design, like `forall.hypothesis` |
| `assume(ens(au,x,y))` on the client side | `AtomicUpdateEnsures` | genuine export, licensed by the adjacent `assert(req)` |
| `assume(input/output/resolves)` under `branch_bool(y)` | `AtomicUpdate` | guarded consequences, same family as a branch condition |
| `assume(pred(au) == pred)`, init-dummy equalities | `AtomicUpdate` | definitional, same family as `VarEquality` |

Only the second row is a fail-open hole. Splitting the rest is a
`root_expectation` classification, so the census stops reporting 244 rows as one
undifferentiated construct.

**Closures are the assert-forall shape exactly.** `StmX::ClosureInner` lowers to
`StmtX::DeadEnd` (`sst_to_air.rs:2702`), and `ExprX::NonSpecClosure` emits the
exported spec as the *sibling statement after* it (`ast_to_sst.rs:2103`). Our own
record on a minimal exec closure:

```text
b1.d.b1  premise     assumed/ClosureRequires   requires i < 10     H
b1.d.b5  obligation  lowered/assert            ensures r == i + 1  G
b2       premise     assumed/ClosureSpec       the closure object  E
```

Compare §3 of `PROOF_COVERAGE.md` on assert-forall: "a `DeadEnd` whose premises
open with `AssertForallRequire`, whose last obligation is the forall goal,
followed by a sibling statement carrying the exported `AssertForallEnsures`
assumption." Substitute `ClosureRequires` / `ClosureSpec` and it is the same
sentence, with the same path structure (`b1.d.*` then `b2`) keeping nested
closures distinct. `ClosureRequires` is an `H` and should be `Expected`;
`ClosureSpec` is licensed by the closure's own ensures obligation.

Two things that looked like soundness risks are not. A **spec** closure
(`ExprX::Closure`, `let f: spec_fn(int) -> int = |x| x + 1`) lowers to a pure
`Exp` with no statement and no obligation, so it contributes no rows at all —
the `ClosureSpec` population is entirely exec/proof closures. And a closure
passed to a higher-order function does not misattribute: the `call_requires(f,
..)` obligation at the call site is an ordinary `call_precondition` on the
callee, already rule 7, while the closure *body* is verified inside the caller's
own query (`b1.d`), so licensing the export in the caller is where the discharge
actually happens.

**`ExpandErrorsSplit` — decided, deferred.** 38 rows, 1 file. `--expand-errors`
is a diagnostic mode that splits a failing obligation into sub-goals; coverage
does not target it, and a failing obligation has no core to attribute. The
resolution is to exclude the intent from the census (one arm in
`root_expectation`, returning a bucket that is neither a hole nor a trusted
root), not to model it. Not done yet.

Two constructs that were in this table are now closed, both through
`CoverageRecord.checked_exports` (`PROOF_COVERAGE.md` §3) and licensing rule 6:

- **generated checks** (`assumed/CheckedCondition`, 279 vstd rows over 213
  functions — the widest hole) were never missing the pairing. The producer walk
  computes the (check, export) pair for *every* assert-then-assume; record
  assembly then discarded it unless the assert resolved to a *source*
  `assertion` artifact. An overflow or pattern-match check has no written
  statement behind it, so a correctly-observed pair was thrown away for want of
  an identity to hang it on. The pair is now recorded directly.
- **invariant blocks** (24 vstd rows over 20 functions) had both halves visible
  as roles but shared one untyped `opened_invariant` role. `EmissionRole::
  InvariantBlock { point: Open | Close }` positions them, and the SST walk
  records block membership (`FunctionRecord.invariant_block_members`) while it
  is inside an `OpenInvariant`, so the two halves pair by a typed join rather
  than by comparing structural paths.

Neither needed a trusted line.

**Rule exists, join did not fire.** These need no modelling. On vstd:

```text
  rows  artifact  cfg node  positioned  fns  construct
    48        48        48         yes   19  assert.establish
    14         0         0         yes   12  lemma.requires_assume
     4         4         4         yes    4  lemma.ensures_assume
     1         0         1         yes    1  forall.establish
```

`artifact` or `cfg node` short of `rows` names the join that failed:
`lemma.requires_assume`'s 14 rows have no CFG node at all, which is why rule 2
cannot pair them.

The 48 `assert.establish` rows are diagnosed but unfixed. For each, *no*
`assert.check` obligation carrying the same artifact exists anywhere in the
record, and every query in those 19 functions is `valid`, so this is not §1.3.
They are `assert ... by(bit_vector)` and compute-mode lemmas
(`bits::lemma_u64_shr_is_div`, `arithmetic::power2::lemma2_to64`, ...): the
follow-on assume is classified as an *assert* export (`Assertion { Establish }`)
while its check is an assert-query goal, so the two halves of one construct land
in different role families and neither rule 2 nor rule 3 can bridge them. The
fix is a producer classification change — an assume following an
`assert ... by(..)` is that query's exported conclusion, not an asserted
proposition.

### Two invariants any new label-bearing relation must satisfy

Both were learned by getting them wrong on `checked_exports`, and both are cheap
to check:

1. **Join canonicalization.** `audit::canonicalize` renumbers query ids and
   `pc%` labels into fingerprint order so records are byte-identical under
   parallel verification. A new relation that names occurrences by label must be
   rewritten there too; otherwise its rows keep pre-canonicalization spellings
   and resolve to nothing. Before the fix, 1564 of 1650 rows named labels that
   existed nowhere in the emitted record.
2. **Never carry a walk-local index across record assembly.** Reconciliation
   occurrences are inserted at their join positions after the query walk, which
   shifts every later index. The assert pairing had recorded indices and was
   silently failing closed on the shifted ones — the `origin.detail ==
   "assertion"` guard turned a wrong index into a skipped join rather than a
   mis-assignment, which is why five `assert.establish` rows were roots. Pairs
   are now resolved by structural path, which insertion does not disturb.

The graph's own structural check is what caught both: a `CertifiedBy` head must
be a premise or an artifact, and every malformed row surfaced as
`CertifiedBy head ... is an obligation`.

### 4.2a Findings fail open, and occlusion does not catch it

`occluded` withholds a verdict only for `loop_invariant_clause`,
`ensures_clause` and `assertion` artifact kinds, and only when an artifact-less
occurrence of the *same family* exists in that function
(`pc_analyze.rs`, `occluded_details`). A `requires_clause` or
`ensures_aggregate` verdict is never occluded, and the families above do not
match `assumed/*` or `opened_invariant`. Over `examples/`: 9 occluded out of
3071 root-scoped findings.

So a function in the census is a function whose findings can be confidently
wrong. `examples/atomic_increment.rs::increment_good` reports
`vstd::atomic::impl&%22::load#ens` as `unlinked` — the atomic load whose result
*is* the returned value the postcondition constrains — at `status = Complete`.
256 vstd functions and 3 of the 147 example files are in this state.

Until the rules land, the safe policy for running over unfamiliar code is to
treat any `assumed/*` or `opened_invariant` root as an occlusion trigger for
every artifact kind in its function: coverage drops on those functions, and the
report stops making claims it cannot support.

### 4.1a Call-local licensing — implemented; per-clause tails — not

Ordinary and recursive calls are represented as call-local licensing relations
rather than static arcs. An ordinary call is based on the callee's ensures
aggregate; a recursive call is based on *that call's* decrease guard, so no
component certificate is materialized and well-foundedness is decided per call.
This lifted the old over-restriction on mutual recursion, where a later call's
`decreases` may legitimately use an earlier call's postcondition. `impact`
traverses the same relations, so the forward and backward directions cannot
drift.

What is **not** refined is the precondition tail. Verus checks one aggregate
`req%g(args)` predicate per call, so the tail carries every precondition check
the caller discharged, not only the clauses the callee's proof used. This is
sound and over-inclusive — it can only add facts to a slice, so it never
manufactures an `available-not-observed` finding — but a clause used solely to
discharge a check the callee never needed goes unreported.

A revision that measured call preconditions per clause was reverted. It split
only the requires side, and it did so by unfolding `req%g` and re-lowering the
callee's clauses through `expand_errors::split_precondition` — the one place in
the producer that reconstructed formulas rather than observing them, which is
also what made it asymmetric with the assumed `ens%g(args)` on the premise side
(§3.2). Both sides are opaque predicate applications; refining either is the
same measurement change, and it should be made once for both
(`PROOF_COVERAGE.md` §6).

Shadow replays can opt into `smt.core.minimize=true` with
`VERUS_PROOF_COVERAGE_MINIMIZE_CORES=1`; canonical verifier contexts remain
unchanged. It is not the default because the artifact's mergesort probe
exceeded its 180-second budget with minimization enabled. Non-unique minimal
cores and the contract aggregates (§3.2) are the remaining precision limits.

### 4.2 Finding vocabulary — decided to settle at the end

Deferred by decision and now with data to settle against:

- **Vacuous terminals are the trust base.** All 71 vacuous terminals in vstd
  are `admit()` proofs (`std_specs::hash`, `std_specs::range`, `tokens`,
  ...): the postcondition holds because `assume(false)` precedes it. The
  record types this exactly (`user_assumption` with an `#assume@<node>`
  artifact; the function is `Ungrounded`). What is missing is the
  presentation: "this contract is trusted; N verified postconditions rest on
  it" is one forward query (`impact`) per admit, not a new mechanism.
  `external_body` contracts (81 in the corpus's imports) are the other half
  of the trust base and are already typed in `source_functions`.
- **Interprocedural findings.** The modular slice crosses calls and crates;
  the vocabulary for "dead precondition over this corpus" and "unused
  postcondition over this corpus" is not written.
- **Program facts in the study text.** Branch conditions, assignments and
  return bindings are artifact-bearing and appear under `direct-support`
  next to specification clauses. The record distinguishes them by kind; the
  text does not group them.
- **Forward vocabulary.** `impact` prints may-depend reach and the
  load-bearing set; whether these become findings, and with what
  qualifiers, is open.

### 4.3 Report performance

`pc_analyze vstd.json report opaque` takes 6m02s for 7432 terminals
(`build` itself is seconds). Each terminal's slice recomputes
`slice_ranks` over the whole graph; the ranks depend only on the policy and
should be computed once per policy. Not a correctness issue.

### 4.4 Overapproximated functions

66 in vstd, all downstream of §1.3 (recommends never checked) and §1.4
(shadow-invalid). No analysis fix applies; the statuses are the honest ones.

---

## 5. Removal gate

1. no occurrence cites `sst.order_alignment`, `sst.signature_bucket`,
   `sst.const_false_exclusion`, `join.loop_inv_ordinal`,
   `join.requires_index` — **met on corpus and vstd** (0, 0, 0, deleted,
   deleted);
2. no production record emits a `lower_assume` derivation — **met**;
3. missing exact SST-to-AIR provenance leaves the query unmeasured — **met**
   (`require_lowering_provenance` fails closed);
4. missing artifact identity or loop group is reported, not defaulted —
   **met** (`Unresolved`, `Unclassified` are declared unobserved by the
   fixture-coverage test);
5. the production schema no longer emits fallback-only fields — **open**:
   `FunctionRecord.sst_assumes`, `Occurrence.sig`, `Transform::LowerAssume`,
   and the `align_sst` / `sst_shape_recognizable` / `sst_sig` code
   (~350 lines) are dead and should be deleted with their audit checks;
6. any retained debug fallback is explicit and excluded from findings —
   moot once 5 is done.

---

## 6. Ready-for-scale criteria

1. every file has a baseline classification and coverage preserves it —
   **met** (vstd 2045/0 with and without the feature);
2. every instrumented batch is measured or explicitly rejected — **met**
   (`valid` / `canonical_missing` / `invalid` / `proof_fallback_canceled`,
   no silent state);
3. every failed focused query remains an opaque terminal — **met**;
4. every attributed row cites a rule; every unattributed row is explicit —
   **met** (zero unresolved on both populations);
5. every certification edge cites a modeled protocol — **met** for the
   seven rules; the atomic-update and closure protocols are the known
   omissions (§4.1);
6. audit violations zero or named — **met** (zero on vstd);
7. timeouts and canonicalization refusals reported separately from
   provenance incompleteness — **met**;
8. aggregate findings report their eligible population and occluded
   population — **met** (`analysis_coverage`; `occluded` verdicts).

The standard does not require complete provenance. It requires every
missing part to have one concrete, non-misleading status. On vstd the missing
parts are §2.1 (48 rows), §2.2 (13 rows), the unmeasured-query assumes and
assert-query clauses of §2 (50 rows), and the deferred decisions of §4.2. §3.1
is closed: whole-vstd analysis is now inside the accepted population.
