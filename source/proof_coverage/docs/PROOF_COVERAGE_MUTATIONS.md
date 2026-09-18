# Confirmation mutations

`PROOF_COVERAGE_FINDINGS.md` §7 asks for confirmation mutations and requires the
mutation result to be stored separately from the finding. This file is that
store.

A finding is witness-relative: core absence alone does not establish semantic
removability (§1, §4). A mutation is stronger evidence — the clause was deleted
and canonical verification still succeeded — but it is not part of the finding,
and a *failed* mutation may reflect solver sensitivity or trigger behaviour
rather than refuting the observation.

Method: blank the flagged source span, re-run canonical Verus with the same
flags the example sweep uses, compare `verification results`. A negative control
deletes a clause the analysis did *not* flag, in the same function where
possible.

Date: 2026-09-14. Binaries: the gate's accepted build.

| # | finding | subject | mutation | control |
|---|---|---|---|---|
| 1 | `checked-but-unused-proof-step` | `guide/bst_map_generic.rs` `Node::insert`, asserts 161/162/181 | remove all three → **34 verified, 0 errors** | remove unflagged 171/217/218 → **2 errors** |
| 2 | `checked-but-unused-proof-step` | `rw2022_script.rs` `fibo_impl`, loop invariant `fibo_fits_u64(i as nat)` (line 133) | remove → **12 verified, 0 errors** | remove near-identical unflagged line 132 `fibo_fits_u64(n as nat)` → **1 error** |
| 3 | `unobserved-context` | `cuckoo_hash_table/rwlock.rs`, `broadcast use group_multiset_axioms;` at 62, 206, 211, 216, 230 | each individually removable; **all five at once → 27 verified, 0 errors** | none available — all five sites in the file are flagged |
| 4 | `goal-unused-precondition` | `guide/quants.rs` `test_seq_5_is_evens`, 5 of 6 `requires` clauses (17, 18, 19, 21, 22) | keep only line 20 → **verifies**; so the minimal sufficient set is 1 of 6 | remove *both* copies of `is_even(s[3])` (20 and 21) → **1 error**, so exactly one is load-bearing |
| 5 | `vacuous-postcondition` (`extent = all`) | `chapter-2-3.rs` `merge_sort` | none needed — measured from the core | — |

Notes on individual rows:

- **#4 is the sharpest result.** `is_even(s[3])` is written twice and
  `is_even(s[2])` is missing — a copy-paste error in Verus's own tutorial
  (`// ANCHOR: quants_finite`, so it is embedded in the published guide). The
  analysis had to choose between two *syntactically identical* clauses and
  reported line 20 load-bearing and line 21 unused. That discrimination comes
  from the UNSAT core, not from slicing, and the joint mutation confirms exactly
  one is required.
- **#3 is dead proof boilerplate in production-style code**: the author added
  `broadcast use` to every `#[inductive]` proof and none of it is needed.
- **#5 needs no mutation** and is corroborated independently: the body is
  `assume(false); input` with the author's own
  `// TODO(jonh): haven't actually implemented`, and the same function also
  reports `goal-without-body-support`.
- Other `extent = all` vacuities in the corpus are `admit()` stubs:
  `oneshot.rs` `shoot`/`shoot_with_two_halves` (7 clauses,
  `// TODO(bsdinis): need the resource lib`), `broadcast_proof.rs`
  `mod_add_zero` (`admit()` under a commented-out `by (integer_ring)` — a live
  §1.3 backend gap), `atomics.rs` `proof_int`.

## Not validated

- **`lemma_requires_clause` findings.** A line-deletion mutation does not
  isolate them: deleting `assert_bit_vector(t ^ t == 0)` in
  `extensionality.rs` removes the assert *and* its conclusion, not the
  requires clause the finding is about. That mutation fails, which says nothing
  about the finding. These rows are unvalidated and should not be quoted as
  confirmed.
- **`extent = some` vacuities** need no mutation: the clause *is* proved on its
  other terminals, and the vacuous ones are infeasible branches, which is what
  `assert(false)` and `assert_by_contradiction!` produce by design.
  `imo_1988_6.rs` `is_perfect_square` is the clean example — its postcondition
  reports `extent = some` at 3 of 7 terminals, so the contract holds and three
  branches are dead. Do not read it as an unproved postcondition; that is
  `extent = all` , which is what `merge_sort` reports.
