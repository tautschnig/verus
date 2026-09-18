# Choosing and cross-checking the SMT solver

Verus discharges its proof obligations with an SMT solver. By default it uses
[Z3](https://github.com/Z3Prover/z3). Verus also has experimental support for
[cvc5](https://cvc5.github.io/), either as a replacement for Z3 or as a second
solver that cross-checks Z3's answers.

Both solvers are shipped in the Verus release archive, so no extra installation
is needed. When running Verus from a source tree, set `VERUS_Z3_PATH` and
`VERUS_CVC5_PATH` to the respective executables if they are not already on the
path.

## Selecting the solver

- Default: Z3.
- `-V cvc5`: use cvc5 instead of Z3 for the default prover.

`-V` flags are Verus's extended options; pass them on the Verus command line
(or forward them through `cargo verus ... -- -V cvc5`).

cvc5 is not a drop-in replacement for every query. See
[Current limitations](#current-limitations) below.

## Cross-checking with a second solver

Cross-checking runs the *identical* SMT query on two independent solvers and
compares their verdicts. The motivation is soundness: a single solver that
wrongly reports `unsat` (a proof) is only dangerous if a second, independent
solver makes the same mistake. An `unsat`/`sat` disagreement on the same query
is therefore a strong signal of either a solver bug or an encoding that is not
actually solver-neutral, and Verus stops on it.

Two flags enable cross-checking for the default prover (Z3 is the primary whose
verdict is authoritative; cvc5 is the secondary):

- `-V cross-check` (*warn* mode): use Z3's verdict, but emit a warning when cvc5
  cannot independently confirm a proof, and hard-error on an `unsat`/`sat`
  disagreement.
- `-V cross-check-strict` (*strict* mode): additionally treat "Z3 proved it but
  cvc5 could not confirm it" as a hard error.

Cross-checking currently covers the default prover only. `by(nonlinear_arith)`
and `by(bit_vector)` queries run in their own tuned, single-solver contexts.

### Reconciliation table

For each `check-sat`, the primary (Z3) and secondary (cvc5) verdicts are
reconciled as follows:

| Z3 (primary) | cvc5 (secondary) | `-V cross-check` (warn) | `-V cross-check-strict` |
|---|---|---|---|
| `unsat` | `unsat`   | accept (confirmed)          | accept (confirmed) |
| `unsat` | `unknown` | **warn**: unconfirmed proof | **hard error**: unconfirmed proof |
| `unsat` | `sat`     | **hard error**: disagreement | **hard error**: disagreement |
| `sat`   | `unsat`   | **hard error**: disagreement | **hard error**: disagreement |
| `sat`   | `sat`     | accept                      | accept |
| `sat`   | `unknown` | accept                      | accept |
| `unknown` | `unsat` | **warn**: cvc5 proved a goal Z3 left unknown | **warn**: same |
| `unknown` | `unknown` | accept                    | accept |
| `unknown` | `sat`   | accept                      | accept |

"Accept" means Verus proceeds with the primary's verdict. The primary's verdict
always determines whether the obligation passes or fails; the secondary only
adds warnings or a hard stop.

### What a disagreement dump contains

On a hard error, Verus writes the offending query and both solvers' output to
`.verus-solver-log/disagreement-<n>.smt2` (one file per disagreement, numbered
across the run). Each dump contains:

- the name of the function whose query disagreed;
- both verdicts (`z3 (primary) = ...`, `cvc5 (secondary) = ...`);
- the full solver-neutral query text that was sent, byte-for-byte, to *both*
  solvers;
- Z3's response transcript;
- cvc5's response transcript.

Because the query text is identical for both solvers, the dump is a
self-contained reproducer you can replay against either solver offline.

## Cost

Cross-checking runs a full cvc5 solve alongside every default-prover Z3 query,
so it is substantially slower than plain Z3. On `vstd` (2059 obligations,
forced clean re-verification, `--time`) the wall-clock cost measured on a
96-core machine was roughly:

| run | verdict | total wall | verify-crate wall |
|---|---|---|---|
| Z3 only               | 2059 verified, 0 errors | ~32 s  | ~10 s |
| Z3 + cvc5 cross-check | 2059 verified, 0 errors | ~100 s | ~77 s |

The overhead is dominated by cvc5's `check-sat` solving time, not by feeding it
the shared declarations/prelude (profiling one module showed cvc5 spending ~92%
of its time in `check-sat` and only ~8% ingesting declarations, while being
about 10x slower than Z3 on the same queries). Cross-checking is intended for
periodic soundness auditing and for investigating suspect proofs, not for the
routine edit-verify loop.

## Current limitations

- **cvc5 is slower and less complete on some queries.** It is typically slower
  than Z3 on bit-vector and quantifier-heavy goals, and on a number of `vstd`
  proofs it returns `unknown` where Z3 returns `unsat`. Under `-V cross-check`
  those show up as "could not independently confirm" warnings rather than
  errors; under `-V cross-check-strict` they become errors.
- **`#[verifier::rlimit]` and `--profile` are Z3-only.** Verus adjusts Z3's
  resource limit per query, but cvc5 accepts only a single up-front per-query
  budget, so `#[verifier::rlimit]` does not retune cvc5 mid-run. Quantifier
  profiling (`--profile`, `--profile-all`) relies on Z3's instrumentation and
  is unavailable with cvc5.
- Cross-checking does not cover the `nonlinear_arith`, `bit_vector`, or
  `integer_ring` prover modes.
