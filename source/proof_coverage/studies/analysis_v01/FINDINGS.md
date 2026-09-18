# Expected text findings

These are the intended readings of the generated `findings.txt` files. They
are stated independently of query-local `pc%...` labels.

## Joint evidence

For `joint_chain`, the postcondition witness contains the two requirements
`p` and `p ==> q` together. It is one joint witness:

```text
{ requires p, requires p ==> q } jointly supports ensures q
```

The requirement `unused` was available to the measured query and was not
observed. The query and selected-root function view therefore report:

```text
available-not-observed joint_chain#req[2]
```

The representation must not split the witness and claim either observed
requirement independently supports the postcondition.

## Vacuity

For `contradictory`, the focused query is measured but its terminal is absent
from the accepted evidence. The two contradictory requirements are printed
as one atomic contradiction witness:

```text
{ requires p, requires !p } contradiction-witness
terminal ensures false: not observed
```

The terminal receives a `vacuous-terminal` finding. The unrelated
requirement remains `available-not-observed`. This evidence is displayed
directly from the focused query even though there is no terminal support edge
to traverse. At function scope, `p` and `!p` appear under
`direct-contradiction`, separate from `direct-support`.

## Isolated loop

For `count_to`, the postcondition directly observes the loop invariant at its
exit position. Backward expansion reaches the same invariant's establishment
and maintenance obligations through the loop certificate:

```text
ensures r == n
  <- invariant i <= n at exit             direct
  <- establish invariant i <= n           transitive
  <- maintain invariant i <= n            transitive
```

The loop exit condition is also observed as a generated occurrence with a
source span. It does not yet have a stable source-artifact identity, so this
study does not classify the loop-condition line as a source fact.

## Nested loops

For `nested_count`, the selected postcondition directly observes the outer
loop exit invariants. The least fixed point then reaches:

```text
outer invariant establishment and maintenance
  <- inner invariant exit
  <- inner invariant establishment and maintenance
```

This is one global monotone fixed point over the verification-argument graph.
There is no special-case nested-loop traversal in the analyzer.

## Recursion

For `self_count`, the recursive call postcondition is directly observed. It
is grounded by a call-local demand edge whose base is the decrease
obligation. The recursive contract is not treated as an unconditional root,
and no component certificate is materialized.

For `even_p` and `odd_p`, opaque intraprocedural analysis reports:

```text
function postcondition
  <- other member's call postcondition    direct, imported
  <- local call precondition              transitive
  <- local decrease obligation            transitive
  stop: mutual-recursion call boundary
```

Opaque mode stops at the mutual-recursion call boundary after retaining the
call's local decrease and demanded precondition checks. Modular mode follows
the same call-local demand edge into the other member's proof.

The query-local axioms in this example (each function's own requires clause,
the parameter type invariant, fuel) are attributed exactly from the
declaration-level lowering sidecar.

## Trait boundary

For `use_increment`, the function postcondition directly observes the trait
method's imported postcondition. The caller requirement is reached
transitively through the local call-precondition check, and traversal stops
at the trait-call boundary:

```text
ensures r == x + 1
  <- Increment::inc postcondition          direct, imported
  <- requires x < 10 at the call           transitive, local
  <- caller requires x < 10                transitive, local
  stop: trait dispatch
```

The study makes no claim about implementation-contract refinement or
behavioral subtyping.

## Established asserts

For `established`, the postcondition witness observes the established
assumption exported by the user assert. The assert statement is one source
artifact with two occurrences: its check obligation (`assert.check`) and the
assumption exported after it (`assert.establish`). The assert certificate
licenses the assumption from its own discharged check, so the requirements
that discharged the check are transitive in the postcondition slice:

```text
ensures a + b == 7
  <- assert(a + b == 7) established        direct
  <- assert(a + b == 7) check              transitive (certificate)
  <- requires a == 3                       transitive
  <- requires b == 4                       transitive
```

The query-level view still reports both requirements
`available-not-observed` for the postcondition query itself: they were in
scope and absent from that one witness. At function scope they are covered
by the slice and produce no finding. The pairing between check and
established assumption is construction-exact from the producer walk
(`join.assert_site`); asserts without exact CFG placement stay unjoined.

## Auxiliary-only support

For `abs_like` in `auxiliary`, the requirement `x > i32::MIN` is observed
only by the generated arithmetic-overflow check for `-x`. It is absent from
the postcondition's direct and transitive slice, so the function finding
remains:

```text
finding available-not-observed artifact=auxiliary::abs_like#req[0]
  auxiliary-support terminal=[arith_overflow_check] ... query=...
```

The qualifier is a per-terminal witness statement: the requirement supports
an auxiliary obligation while contributing nothing observed to the selected
root. It neither suppresses the finding nor claims the requirement is
removable.

The postcondition witness itself contains no specification clause. Its
evidence is the program: both arms of the `if` (one `branch_condition`
artifact, `abs_like#branch@<node>`, with an occurrence per arm), the return
value's binding (`abs_like#return@<node>`), and the parameter's type
invariant. The first two are written constructs and appear under
`direct-support` with their statement artifacts; the type invariant is an
encoding fact with a site but no subject, and appears under
`generated-support`.

## Trait dispatch and crates

For `via_trait` in `traits_modular`, the generic call assumes
`Step::step`'s postcondition. In modular mode the trait clause is certified
by both implementations' refinement checks jointly:

```text
ensures r > x
  <- Step::step postcondition                     direct
  <- Step::step#ens[0] checked in One::step        transitive (certificate, joint)
  <- Step::step#ens[0] checked in Two::step        transitive (certificate, joint)
  boundary: trait_contract, implementations = {One::step, Two::step}
```

For `via_impl`, the verifier resolved the call to `Two::step` statically and
assumed `Two`'s own contract, so the slice expands into `Two::step`'s proof
including its stronger second clause `r == x + 2`; no trait boundary appears.

For the two-crate study (`crates/`), `crate_b::twice` calls
`crate_a::add_one` twice. Analyzing both records together, the modular slice
of `twice`'s postcondition reaches `add_one`'s ensures checks and return
binding in `crate_a`, because the caller's imported aggregate and the callee's
own aggregate are one vertex, identified by the crate that defines `add_one`.
The forward query `impact r0%crate_a::add_one#ens[1] modular` reaches
`twice`'s postcondition through the aggregate — the aggregate granularity is
why the unused clause `r > 0` reaches it too — and reaches nothing outside
`crate_a` in opaque mode.

## Statement artifacts

Every written statement whose fact reaches a query has an artifact, keyed by
the exact CFG node of the emitting statement: `#assume@<node>` for a user
`assume`, `#assign@<node>` for an initializing `let`, `#return@<node>` for the
return value's binding, `#reveal@<node>` for a reveal, `#branch@<node>` for
an `if` (two occurrences, one per arm), and `#cond<i>` for a loop's condition
(two occurrences: assumed at body entry, negated after exit). Compiler
temporaries — decrease-init bindings and call-argument temporaries, decided by
the variable's disambiguator — are encoding facts with a site and receive no
artifact. Over the study and probe corpus there is no occurrence of `source`
origin without an artifact.

## Ambient identity

For `uses_ambient` in `ambient`, the first postcondition observes the spec
function's definition axiom and the second observes the broadcast lemma's
axiom. Ambient evidence is displayed with its recorded owner and typed
installation op, taken from the ambient tap:

```text
ambient::double         [ambient:SpecDefinition]
ambient::double_is_even [ambient:Broadcast]
```

The `pc_a%...` labels remain opaque transport tokens; identity comes only
from the recorded owner/op relation. The function summary collects these
under `ambient-support`.

## Mutations

For `accumulate` in `mutation`, the loop rebuilds `total`, increments `i`,
and toggles an unrelated `scratch`. The postcondition `r == n` reaches the
two live mutations through the loop certificate:

```text
ensures r == n
  <- invariant total == i at exit          direct
  <- maintain total == i                   transitive (certificate)
  <- total = total + 1                     transitive   (#assign@<node>, sst:AssignUpdate)
  <- i = i + 1                             transitive
```

and never reaches `scratch = scratch ^ 1` or `let mut scratch = 7`, which are
the function findings, alongside the genuinely unused `requires n <= 100`.
The mutation's equality is synthesized by the SSA pass after our labelling
point; rather than rewrite the statement, the shadow guards that equality
where the SSA pass generates it, from the pass's own trace (see the producer
document's measurement section). `negate_twice` checks the old-value reading:
both `y = -y` statements are direct support of `r == x`.

A function finding's candidate population is every `available-not-observed`
observation by a measured terminal of the function, not only the roots' own
queries: the loop body is its own query, and a body fact the roots never
reach would otherwise not be a candidate at all. Survivors are those absent
from every root's direct and transitive slice.

## Transformation semantics: what is and is not measured

Initializing assignments (`let x = e`) are SST `VarEquality` assumptions and
were always measured; mutating assignments are measured by guarding the
equality the SSA pass makes of each `Assign`, from that pass's generation
trace. Havoc has no fact of its own — a havocked variable is a fresh symbol —
but its observable encoding effect, the re-assumed type invariant, is measured
and typed (`type_invariant`).

The version-reconciliation equalities `var_to_const` inserts where
control-flow paths join (`x@m == x@k` at each `Switch` arm, `Breakable` exit
and `Break`) are measured the same way: the pass records them in its trace,
the shadow guards them after SSA, and each becomes a generated premise
(`ssa_reconciliation`, role `SsaReconciliation { join }`) placed at the join
statement. No user statement stands behind them, so they carry no artifact;
they can and do appear in a core (a postcondition over a mutated variable
depends on the reconciliation that carries its final version out of the loop),
where they read as generated support, like a branch condition or a fuel fact.

## The four models

`models.rs` exercises each model against the construct that distinguishes it.

**assert-forall (`all_positive`).** The exported quantified conclusion used
to be a graph root, so both requirements looked `auxiliary-only`. With the
checked-export certificate `{forall.goal} ⊢ forall.establish` they are
goal-supporting transitive, and the inner `assert(values[i] == value)` is
in the chain:

```text
ensures forall .. values[i] > 0
  <- forall.establish                      direct
  <- forall.goal                           transitive (certificate)
  <- assert values[i] == value              transitive
  <- requires value > 0                     transitive
  <- requires forall .. values[i] == value  transitive
```

**for loop (`fill`).** The desugaring collapses invariant spans onto the
loop header and the iterator, so span equality cannot discriminate. Ordinal
alignment per protocol position, count-guarded, gives the user's clauses
their identity; the positions whose observed population does not match the
declared clause count stay unjoined and appear in `analysis_coverage`
rather than being guessed.

**clause groups (`count_to_limit`).** `invariant_except_break` receives an
entry certificate but no exit export, `invariant` receives both, and the
loop `ensures` is licensed by the exit-side checks alone. Because this
function still has unidentified `at_transfer` evidence, the verdict for its
plain invariant is reported `occluded` — the honest answer, since those
unidentified rows could be that clause at the transfer position.

**trait refinement (`UpToTen::clamp`).** The contract is declared on
`Bounded::clamp`, so the impl's obligations project onto the trait's
clauses through the recorded relation — without it the impl has no
classified artifacts at all. The requirement `self.ok(input)` is then
legitimately `unlinked`: the postcondition `output == input` holds without it.

**no declared goals (`rootless`).** Reports `state = no-declared-goals`
with the policy named, instead of rendering an empty analysis.
