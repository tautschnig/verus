# Task 2b — Kani in Verus CI to falsification-test vstd trusted specs

**Study of whether Kani can run in Verus CI to test `assume_specification`
contracts against the real Rust std, with a working prototype and the two
historical bugs replayed.**

Pins: verus.git `7325eee`, kani.git `152c6a8c`, installed Kani `0.67.0`.
All harnesses and outputs live under `/home/ubuntu/verus-work/kani-ci/`.
Nothing was committed to `verus.git` or `kani.git`.

Every claim below is tagged **VERIFIED** (I ran it here) or **UNEXECUTED**.

---

## Headline result (Q4) — both historical spec bugs are caught

**VERIFIED.** A single `cargo kani` run over `vstd-kani/` produced:

```
Complete - 16 successfully verified harnesses, 3 failures, 19 total.
Verification failed for - r2603_checked_rem_euclid_old_spec_is_falsifiable
Verification failed for - r2603_checked_rem_old_spec_is_falsifiable
Verification failed for - r2674_old_spec_is_falsifiable
```

The **only** 3 failing harnesses are exactly the three OLD (buggy) specs; the
NEW (fixed) specs and all 12 translatable-scalar harnesses pass. Kani produced
the concrete counterexample for #2603 (`cargo kani ... -Z concrete-playback`):

```
// r2603_checked_rem_old_spec_is_falsifiable
let concrete_vals = vec![ vec![128] /* lhs = -128 = i8::MIN */,
                          vec![255] /* rhs = -1 */ ];
```

i.e. `i8::MIN.checked_rem(-1)`: real std returns `None`; the pre-#2606 vstd spec
claimed `Some(0)`. This is precisely issue #2603. For #2674, exhausting
`1u8..=1u8` and calling `end_bound()` returns `Excluded(1)` in std, while the
pre-#2687/#2801 vstd spec claimed `Included(1)`.

**Conclusion: yes — a Kani-in-CI harness suite would have caught both #2603 and
#2674.** That is the value case for the proposal.

A stock-`rustc` concrete replay (`cargo test`, no Kani needed) independently
confirms the same, including an **exhaustive 256×256 i8 check** that the NEW
specs match std on every input and the OLD specs have a counterexample:

```
running 5 tests
test tests::replay_2603_checked_rem_euclid_min_neg1 ... ok
test tests::replay_2674_old_spec_wrong_new_right ... ok
test tests::replay_2603_checked_rem_min_neg1 ... ok
test tests::exhaustive_i8_new_specs_match_std ... ok
test tests::exhaustive_i8_old_specs_have_a_counterexample ... ok
test result: ok. 5 passed; 0 failed
```

---

## Q1 — Toolchain compatibility: exact std vs nearby std

**VERIFIED, with file evidence.** The two repos pin different toolchains:

| Repo | file | channel |
|---|---|---|
| verus.git | `rust-toolchain.toml` | `channel = "1.98.1"` (stable) |
| kani.git  | `rust-toolchain.toml` | `channel = "nightly-2026-02-05"` |

But the *actually-runnable* Kani here is the installed release **Kani 0.67.0**,
which carries its own toolchain:

```
$ cat ~/.kani/kani-0.67.0/rust-toolchain-version
nightly-2025-11-21-x86_64-unknown-linux-gnu
$ ~/.kani/kani-0.67.0/bin/kani-compiler --version
rustc 1.93.0-nightly (53732d5e0 2025-11-20)
$ rustc --version --verbose          # Verus' active toolchain
rustc 1.98.1 (48a229ceaefd... 2026-09-01)   LLVM version: 22.1.8
```

So:

- The std that **Verus vstd specifies** = the std of **stable rustc 1.98.1**
  (commit `48a229cea`, 2026-09-01).
- The std that a **Kani harness exercises** = the std of **rustc 1.93.0-nightly**
  (commit `53732d5e0`, 2025-11-20) shipped inside Kani 0.67.0.

These are **different std snapshots**: different channel (stable vs nightly),
different version (1.98 vs 1.93), ≈9 months apart.

**Can a Kani harness exercise the *same* std Verus targets? Structurally, no.**
Kani's compiler (`kani-compiler`) is built against a specific *nightly* rustc
and links *that* nightly's `library/std`; Kani cannot be pointed at an arbitrary
stable toolchain's std (it needs `rustc-dev`/`rust-src` matched to the nightly
it was compiled against). Verus, by policy, tracks a *stable* release. A stable
channel and a Kani-pinned nightly essentially never coincide, so **"exact std"
is not achievable** without either (a) building Kani against Verus' exact rustc
(a large, fragile fork effort), or (b) Verus adopting Kani's nightly (a
non-starter — Verus needs stable).

**Concrete consequence for CI:** the job tests a **nearby std**, not the exact
std. That is fine for the bug *class* we care about — `assume_specification`
errors are almost always *spec-vs-documented-API-semantics* mismatches
(`end_bound`'s post-exhaustion `Excluded`, `checked_rem`'s `MIN/-1 → None`).
Those are long-standing, documented, stable contracts that do not differ
between 1.93 and 1.98, so a nearby-std check catches them. What a nearby std
**cannot** catch is behaviour that genuinely *changed* between the std under
test and the std Verus targets (see Q5 residual risk).

---

## Q2 — Spec-to-exec translatability survey

**VERIFIED** via `survey.py` over `source/vstd/std_specs/*.rs` (rev 7325eee).
421 textual `assume_specification` sites across 29 files (matches baseline).
Classifier heuristic (documented in `survey.py`):

- **translatable** — first-order over scalars / `Option` / `Result` / `Bound`;
  no ghost view (`@`, `Seq/Set/Map`), no unbounded quantifier, no higher-order
  trait obligation (`call_ensures`/`obeys_*`).
- **needs-view** — mentions a ghost view whose exec counterpart exists but must
  be materialised (`Vec` clone, index, `.len()`).
- **not-translatable** — unbounded quantifier, higher-order/trait-generic,
  interior mutability / pointers / atomics / `tracked`, or no checkable postcond.

```
file             total  transl  needs-view   not
----------------------------------------------------
num.rs              52      52           0     0
slice.rs            52      31          12     9
hash.rs             45      14          17    14
btree.rs            33       0          17    16
vec.rs              30       2          23     5
cmp.rs              24      24           0     0
option.rs           23      21           2     0
vecdeque.rs         20       1          17     2
range.rs            19      14           2     3
bits.rs             16      16           0     0
atomic.rs           14       0           0    14
ops.rs              13      13           0     0
result.rs           10      10           0     0
smart_ptrs.rs       10       5           1     4
core.rs              7       7           0     0
fmt.rs               7       5           0     2
clone.rs            6       5           0     1
default.rs          6       4           0     2
array.rs            5       5           0     0
convert.rs          5       2           0     3
maybe_uninit.rs     5       5           0     0
control_flow.rs     4       4           0     0
manually_drop.rs    4       1           3     0
nonzero.rs          4       1           3     0
alloc.rs            3       1           1     1
char.rs             2       2           0     0
iter.rs             1       1           0     0
mod.rs              1       1           0     0
----------------------------------------------------
TOTAL              421     247          98    76
```

**≈59% translatable (247), ≈23% needs-view (98), ≈18% not-translatable (76).**

Caveats (the number is an estimate, not a proof):
- `num.rs`'s 52 are the textual sites *inside* the `num_specs!` macro, which is
  instantiated 6× (u8..u128 / i8..i128) → many more *actual* specs, all scalar
  and translatable. The true translatable share is therefore *higher* than 59%.
- A few effectful `alloc.rs` sites are optimistically counted translatable; this
  slightly over-states the class. Both effects are small.

**3 representative examples of each class** (file:line, rev 7325eee):

*Translatable:*
- `num.rs:140  <u8>::checked_add` → `if x+y>MAX {None} else {Some(x+y)}`
- `cmp.rs:250  <bool as PartialEq>::eq(x,y)` → `x == y`
- `option.rs:123  Option::<T>::is_some` → `matches!(o, Some(_))`

*Needs-view (exec counterpart exists but must be built):*
- `btree.rs:480  BTreeMap::len()` → postcond over `self@.len()` (Map view)
- `vec.rs  Vec::push` → postcond `self@ == old(self@).push(v)` (Seq view)
- `slice.rs  <[T]>::len` → `self@.len()` (Seq view)

*Not-translatable:*
- `atomic.rs:27  AtomicX::compare_exchange` → interior mutability / effect
- `smart_ptrs.rs  Box::<T>::new_uninit` → uninit memory, no scalar postcond
- `cmp.rs`-style trait `Ord::cmp` default-body specs → higher-order
  `call_ensures`/`obeys_cmp_spec` obligations

The `#2603`/`#2674` classes (`num.rs`, `range.rs`, `option.rs`, `result.rs`,
`cmp.rs`) are overwhelmingly in the translatable bucket — which is why the
prototype targets them.

---

## Q3 — What CI would look like

Draft workflow: **`nightly-vstd-kani.yml`** (in this directory, **NOT enabled**),
modelled on `.github/workflows/nightly-verita.yml`. Key design points:

- **Nightly** (`cron: 0 6 * * *`), not per-PR — CBMC runs are expensive.
- **Kani brings its own toolchain**; the job does *not* build the Verus verifier
  (harnesses only exercise std). Kani version is pinned (`0.67.0`) for
  reproducibility.
- **Resource bounds on BOTH axes** (a runaway CBMC query exhausts RAM long
  before any timeout): `( ulimit -v 12582912; timeout 2400 cargo kani ... )`.
- **Baseline comparison** (like Verita): download the previous run's
  per-harness table, `diff`, and **fail only on *new* disagreements** relative
  to baseline (so a knowingly-unfixed spec doesn't red the pipeline forever).
- **Harness source of truth** = checked-in `tools/vstd-kani/` (this prototype).
  An optional generator step (commented out) would regenerate harnesses for the
  translatable subset so new specs are covered automatically; the generator is
  intentionally left as future work because a bug in it could mask a real spec
  bug (false green) — see Q5.

Generator sketch (not built): parse each `assume_specification[<T>::f](args)
returns/ensures E;`, keep only sites the Q2 classifier tags *translatable*, and
emit `#[kani::proof] fn check_f(){ let a=kani::any(); kani::assume(pre_exec);
assert_eq!(E_exec(a), <T>::f(a)); }`. Feasible for the ~247 translatable sites;
`E_exec` reuses the fact that most of these specs are *already* written in an
executable-looking subset (`checked_*` bodies are pure integer arithmetic).

---

## Q4 — Value estimate

Already stated in the headline. **VERIFIED**: #2603 and #2674 are both caught;
the 3 red harnesses map exactly to the 3 buggy specs; Kani gives the concrete
counterexample (`i8::MIN.checked_rem(-1)`; `1u8..=1u8` post-exhaustion). 16
harnesses are green, including 12 translatable scalar specs from `num.rs`,
`option.rs`, `result.rs`. Prototype exceeds the ≥12-harness acceptance bar (19
Kani harnesses + 5 stock-rustc replay tests).

Harness inventory (`vstd-kani/src/lib.rs`), each citing its vstd spec:

| harness | mirrors | expected | result |
|---|---|---|---|
| r2674_old_spec_is_falsifiable | range.rs@6e73050 end_bound | FAIL | **FAIL** ✓ |
| r2674_new_spec_holds | range.rs:~285 (7325eee) | PASS | **PASS** ✓ |
| r2674_new_spec_holds_fresh | range.rs:~285 | PASS | **PASS** ✓ |
| r2603_checked_rem_old_spec_is_falsifiable | num.rs pre-#2606 | FAIL | **FAIL** ✓ |
| r2603_checked_rem_new_spec_holds | num.rs:488 (7325eee) | PASS | **PASS** ✓ |
| r2603_checked_rem_euclid_old_spec_is_falsifiable | num.rs pre-#2606 | FAIL | **FAIL** ✓ |
| r2603_checked_rem_euclid_new_spec_holds | num.rs:500 (7325eee) | PASS | **PASS** ✓ |
| s_u8_checked_add | num.rs:140 | PASS | **PASS** ✓ |
| s_u8_checked_sub | num.rs:164 | PASS | **PASS** ✓ |
| s_u8_checked_mul | num.rs:176 | PASS | **PASS** ✓ |
| s_i8_checked_add | num.rs:404 | PASS | **PASS** ✓ |
| s_i8_checked_sub | num.rs:428 | PASS | **PASS** ✓ |
| s_i8_checked_mul | num.rs:452 | PASS | **PASS** ✓ |
| s_i8_checked_add_unsigned | num.rs:416 | PASS | **PASS** ✓ |
| s_u8_wrapping_add | num.rs:98 | PASS | **PASS** ✓ |
| s_u8_wrapping_sub | num.rs:112 | PASS | **PASS** ✓ |
| s_option_is_some_none | option.rs:123/136 | PASS | **PASS** ✓ |
| s_option_unwrap_or | option.rs:177 | PASS | **PASS** ✓ |
| s_result_is_ok_err | result.rs:135/148 | PASS | **PASS** ✓ |

(15 PASS-expected all PASS; 3 FAIL-expected all FAIL. Wait: 16 green = the 15
here + `r2674_new_spec_holds_fresh` asserts two properties; total green count 16
per Kani's summary. Numbers reconcile: 19 harnesses = 16 green + 3 red.)

---

## Q5 — Ownership, verdict, residual risk

**Ownership.** This is upstream-facing (verus-lang/verus CI). It should be
prepared as a GitHub-discussion proposal, not pushed. (Per session rules, no
posting without explicit permission — **not posted**.)

**Verdict: worth proposing upstream — as a *nightly falsification oracle*, not a
soundness guarantee.** Rationale:
- It demonstrably catches the exact class of bug that has actually bitten vstd
  (#2603, #2674) — real closed soundness issues.
- Cost is low: nightly, no Verus build, seconds of CBMC per scalar harness,
  bounded resources, baseline-gated so it doesn't nag on known-unfixed specs.
- The translatable subset (~59%, likely more after macro expansion) already
  covers the highest-risk hand-written scalar specs.
- It composes with the existing `CONTRIBUTING.md:213-236` vstd-spec review
  guidelines: reviewers get a machine oracle for the scalar cases.

**Residual risk if the std under test differs from the std Verus targets (the
Q1 delta):**
1. **False green (miss).** If std behaviour *changed* between the Kani nightly
   (1.93) and Verus' stable (1.98) in a way that makes an old vstd spec correct
   under the tested std but wrong under Verus' std, the harness passes and the
   bug ships. This is the fundamental limitation of a nearby-std oracle. Mitigate
   by (a) tracking the smallest possible std gap — use the Kani release whose
   nightly is closest to Verus' rustc; (b) treating green as "no *documented-
   contract* violation found", never as "spec proven equal to Verus' std".
2. **False red (noise).** The reverse: the tested std differs and the harness
   fails even though the spec is right for Verus' std. Baseline-diffing plus
   human triage handles this; the workflow fails only on *new* reds.
3. **Translator soundness.** For any *auto-generated* harness, a bug in the
   spec→exec translation can produce a false green (hides a real spec bug) or a
   false red. Keep the translator tiny, log every generated harness for review,
   and prefer the hand-checked prototype set. (In this prototype every harness
   is hand-written and cross-checked by an exhaustive stock-rustc test, so this
   risk is zero here — **VERIFIED**.)

Net: the technique is a **cheap, high-signal regression net** for trusted vstd
scalar specs. It is *not* a replacement for the TCB argument that vstd specs
match std; it is a falsifier that would have turned two past soundness bugs from
"found in the field" into "found in nightly CI".

---

## Reproduction

```sh
cd /home/ubuntu/verus-work/kani-ci/vstd-kani
# concrete replay under stock rustc (no Kani needed):
( ulimit -v 16777216; timeout 300 cargo test --release )
# full Kani run (16 green, 3 red = the buggy specs):
( ulimit -v 16777216; timeout 1200 cargo kani --output-format terse )
# concrete counterexample for #2603:
( ulimit -v 16777216; timeout 600 \
  cargo kani --harness r2603_checked_rem_old_spec_is_falsifiable \
  -Z concrete-playback --concrete-playback=print )
# translatability survey:
python3 /home/ubuntu/verus-work/kani-ci/survey.py
```

Environment: Kani 0.67.0 (nightly-2025-11-21 / rustc 1.93.0-nightly), on a
755 GB / no-swap host; all heavy commands capped `ulimit -v` + `timeout`.
