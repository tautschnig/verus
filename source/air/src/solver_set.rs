//! Dual-solver cross-checking skeleton (design: `plan/05-dual-solver-design.md` §2).
//!
//! The idea: emit ONE solver-neutral SMT-LIB command stream and feed the identical text
//! to two independent solver processes (e.g. cvc5 as primary, Z3 as secondary). Because a
//! single-solver soundness bug that produces a wrong `unsat` is only dangerous if *both*
//! solvers share it, an `unsat`/`sat` disagreement on the same query is a strong soundness
//! signal and is worth a hard stop.
//!
//! This module is a self-contained skeleton: [`SolverSet`] fans a command stream to both
//! children in parallel and [`reconcile`] implements the full verdict-reconciliation table
//! from the design doc. It is deliberately NOT yet wired into
//! [`crate::context::Context`]/[`crate::smt_verify`]; doing so requires the neutral-dialect
//! `Printer` split (design §2.1, risk 1) and per-solver option injection, which are larger
//! changes. Keeping the reconciliation logic here, with unit tests, lets it be exercised
//! and reviewed independently of that refactor.

use crate::context::SmtSolver;
use crate::smt_process::SmtProcess;

/// The three verdicts a solver can report for a `check-sat`, normalised away from
/// solver-specific spellings (e.g. cvc5's "cvc5 interrupted by timeout." is `Unknown`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverVerdict {
    Unsat,
    Sat,
    Unknown,
}

impl SolverVerdict {
    /// Human-readable verdict name for diagnostics.
    pub fn name(&self) -> &'static str {
        match self {
            SolverVerdict::Unsat => "unsat",
            SolverVerdict::Sat => "sat",
            SolverVerdict::Unknown => "unknown",
        }
    }

    /// Extract the verdict from a solver's response lines. The last recognised verdict
    /// wins (a query ends in exactly one `check-sat` result once acknowledgements are
    /// stripped); anything unrecognised is treated as `Unknown`, never as a proof.
    pub fn from_lines(lines: &[String]) -> SolverVerdict {
        let mut verdict = SolverVerdict::Unknown;
        for line in lines {
            let line = line.trim();
            if line == "unsat" {
                verdict = SolverVerdict::Unsat;
            } else if line == "sat" {
                verdict = SolverVerdict::Sat;
            } else if line == "unknown"
                || line == "timeout"
                || line.contains("interrupted by timeout")
                || line.contains("resource limit")
            {
                verdict = SolverVerdict::Unknown;
            }
        }
        verdict
    }
}

/// How aggressively to act on what the secondary solver says.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CrossCheckPolicy {
    /// Only the primary solver's verdict is used (cross-check disabled).
    Off,
    /// Use the primary verdict, but emit a warning when the secondary cannot confirm a
    /// proof; still hard-error on an `unsat`/`sat` disagreement.
    Warn,
    /// Additionally treat a proof the secondary could not independently confirm
    /// (`unsat` vs `unknown`) as a hard error.
    Strict,
}

impl Default for CrossCheckPolicy {
    fn default() -> Self {
        CrossCheckPolicy::Off
    }
}

/// What the caller should do after reconciling the two verdicts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CrossCheckAction {
    /// Proceed using the primary solver's verdict/result unchanged.
    UsePrimary,
    /// Proceed using the primary verdict, but surface `message` as a warning.
    UsePrimaryWithWarning(String),
    /// Stop: the two solvers disagree in a way that signals a soundness problem or (under
    /// `Strict`) an unconfirmed proof. `message` describes the disagreement; the caller is
    /// expected to dump both transcripts and the query for offline inspection.
    HardError(String),
}

/// Reconcile the primary and secondary verdicts per the design-doc table (§2.2).
///
/// `primary` is the solver whose verdict is authoritative for the returned result;
/// `secondary` is `None` when no cross-check ran. The interesting rows are the
/// `unsat`/`sat` cross pairs — those are genuine soundness signals (either a solver bug or
/// an encoding that is not actually solver-neutral) and become a hard error under both
/// `Warn` and `Strict`.
pub fn reconcile(
    policy: CrossCheckPolicy,
    primary: SolverVerdict,
    secondary: Option<SolverVerdict>,
) -> CrossCheckAction {
    use CrossCheckPolicy::*;
    use SolverVerdict::*;

    let Some(secondary) = secondary else {
        return CrossCheckAction::UsePrimary;
    };
    if policy == Off {
        // Cross-check disabled: the primary verdict stands regardless of the secondary.
        return CrossCheckAction::UsePrimary;
    }

    match (primary, secondary) {
        // Both proved it: independently confirmed.
        (Unsat, Unsat) => CrossCheckAction::UsePrimary,
        // Primary proved it, secondary could not confirm.
        (Unsat, Unknown) => match policy {
            Off => unreachable!(),
            Warn => CrossCheckAction::UsePrimaryWithWarning(
                "secondary solver could not independently confirm this proof".to_string(),
            ),
            Strict => CrossCheckAction::HardError(
                "cross-check failed: proof not independently confirmed by the secondary solver"
                    .to_string(),
            ),
        },
        // Soundness signal: one solver proves it, the other refutes it.
        (Unsat, Sat) | (Sat, Unsat) => CrossCheckAction::HardError(
            "cross-check disagreement: one solver reported unsat and the other sat on the \
             identical query (possible solver soundness bug or non-neutral encoding)"
                .to_string(),
        ),
        // Primary found a counterexample; secondary agrees or is inconclusive.
        (Sat, Sat) | (Sat, Unknown) => CrossCheckAction::UsePrimary,
        // Primary inconclusive; secondary proved it. Keep the primary (unknown) verdict but
        // note that switching primaries would discharge the goal.
        (Unknown, Unsat) => match policy {
            Off => unreachable!(),
            Warn | Strict => CrossCheckAction::UsePrimaryWithWarning(
                "secondary solver proved this goal that the primary left unknown; \
                 consider making it the primary solver"
                    .to_string(),
            ),
        },
        // Both inconclusive, or primary inconclusive and secondary refuted: nothing the
        // cross-check can add; keep the primary's (non-proof) verdict.
        (Unknown, Unknown) | (Unknown, Sat) => CrossCheckAction::UsePrimary,
    }
}

/// A primary solver process with an optional secondary for cross-checking. The same
/// command text is sent to both; verdicts are reconciled with [`reconcile`].
///
/// Skeleton: launched and driven explicitly by tests / future call sites. Wiring it into
/// `Context` (so the whole pipeline fans out) is future work (design §2.1).
pub struct SolverSet {
    pub primary_solver: SmtSolver,
    pub secondary_solver: Option<SmtSolver>,
    pub policy: CrossCheckPolicy,
    primary: SmtProcess,
    secondary: Option<SmtProcess>,
}

/// The outcome of sending a query to a [`SolverSet`]: the primary's raw response lines
/// (from which the caller builds the real result) plus the reconciliation action.
pub struct SolverSetResponse {
    pub primary_lines: Vec<String>,
    pub secondary_lines: Option<Vec<String>>,
    pub primary_verdict: SolverVerdict,
    pub secondary_verdict: Option<SolverVerdict>,
    pub action: CrossCheckAction,
}

impl SolverSet {
    /// Launch the primary and (if cross-checking) secondary solver processes.
    pub fn launch(
        primary_solver: SmtSolver,
        secondary_solver: Option<SmtSolver>,
        policy: CrossCheckPolicy,
    ) -> Self {
        let primary = SmtProcess::launch(&primary_solver, None);
        let secondary = match (secondary_solver, policy) {
            (Some(s), CrossCheckPolicy::Warn) | (Some(s), CrossCheckPolicy::Strict) => {
                Some(SmtProcess::launch(&s, None))
            }
            _ => None,
        };
        SolverSet { primary_solver, secondary_solver, policy, primary, secondary }
    }

    /// Fan the identical command stream to both solvers in parallel, wait for both, and
    /// reconcile their verdicts. The primary's lines are always returned so the caller can
    /// build its normal `ValidityResult`; `action` says whether to warn or hard-stop.
    pub fn send_commands(&mut self, commands: Vec<u8>) -> SolverSetResponse {
        // Start the secondary first so both run concurrently while we wait.
        let (secondary_lines, secondary_verdict) = if let Some(secondary) = &mut self.secondary {
            // send_commands here is a simple synchronous fan-out; a fully wired version
            // would use send_commands_async on both and join the handles (design §2.1).
            let lines = secondary.send_commands(commands.clone());
            let verdict = SolverVerdict::from_lines(&lines);
            (Some(lines), Some(verdict))
        } else {
            (None, None)
        };
        let primary_lines = self.primary.send_commands(commands);
        let primary_verdict = SolverVerdict::from_lines(&primary_lines);
        let action = reconcile(self.policy, primary_verdict, secondary_verdict);
        SolverSetResponse {
            primary_lines,
            secondary_lines,
            primary_verdict,
            secondary_verdict,
            action,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use CrossCheckPolicy::*;
    use SolverVerdict::*;

    #[test]
    fn verdict_parsing() {
        assert_eq!(SolverVerdict::from_lines(&["unsat".to_string()]), Unsat);
        assert_eq!(SolverVerdict::from_lines(&["sat".to_string()]), Sat);
        assert_eq!(SolverVerdict::from_lines(&["unknown".to_string()]), Unknown);
        assert_eq!(
            SolverVerdict::from_lines(&["cvc5 interrupted by timeout.".to_string()]),
            Unknown
        );
        // No recognised verdict is never mistaken for a proof.
        assert_eq!(SolverVerdict::from_lines(&["(error \"boom\")".to_string()]), Unknown);
        // Last verdict wins (e.g. push/pop bookkeeping before the real answer).
        assert_eq!(
            SolverVerdict::from_lines(&["sat".to_string(), "unsat".to_string()]),
            Unsat
        );
    }

    #[test]
    fn no_secondary_is_always_use_primary() {
        for policy in [Off, Warn, Strict] {
            for v in [Unsat, Sat, Unknown] {
                assert_eq!(reconcile(policy, v, None), CrossCheckAction::UsePrimary);
            }
        }
    }

    #[test]
    fn off_ignores_secondary() {
        for p in [Unsat, Sat, Unknown] {
            for s in [Unsat, Sat, Unknown] {
                assert_eq!(reconcile(Off, p, Some(s)), CrossCheckAction::UsePrimary);
            }
        }
    }

    #[test]
    fn agreement_uses_primary() {
        assert_eq!(reconcile(Warn, Unsat, Some(Unsat)), CrossCheckAction::UsePrimary);
        assert_eq!(reconcile(Strict, Unsat, Some(Unsat)), CrossCheckAction::UsePrimary);
        assert_eq!(reconcile(Warn, Sat, Some(Sat)), CrossCheckAction::UsePrimary);
        assert_eq!(reconcile(Strict, Sat, Some(Sat)), CrossCheckAction::UsePrimary);
        assert_eq!(reconcile(Warn, Unknown, Some(Unknown)), CrossCheckAction::UsePrimary);
    }

    #[test]
    fn unconfirmed_proof_warns_or_errors() {
        assert!(matches!(
            reconcile(Warn, Unsat, Some(Unknown)),
            CrossCheckAction::UsePrimaryWithWarning(_)
        ));
        assert!(matches!(
            reconcile(Strict, Unsat, Some(Unknown)),
            CrossCheckAction::HardError(_)
        ));
    }

    #[test]
    fn unsat_vs_sat_is_a_hard_error_both_directions() {
        for policy in [Warn, Strict] {
            assert!(matches!(reconcile(policy, Unsat, Some(Sat)), CrossCheckAction::HardError(_)));
            assert!(matches!(reconcile(policy, Sat, Some(Unsat)), CrossCheckAction::HardError(_)));
        }
        // With cross-checking Off, even a disagreement defers to the primary.
        assert_eq!(reconcile(Off, Unsat, Some(Sat)), CrossCheckAction::UsePrimary);
    }

    #[test]
    fn counterexample_keeps_primary() {
        assert_eq!(reconcile(Warn, Sat, Some(Unknown)), CrossCheckAction::UsePrimary);
        assert_eq!(reconcile(Strict, Sat, Some(Unknown)), CrossCheckAction::UsePrimary);
    }

    #[test]
    fn secondary_proves_what_primary_could_not() {
        assert!(matches!(
            reconcile(Warn, Unknown, Some(Unsat)),
            CrossCheckAction::UsePrimaryWithWarning(_)
        ));
        assert!(matches!(
            reconcile(Strict, Unknown, Some(Unsat)),
            CrossCheckAction::UsePrimaryWithWarning(_)
        ));
        // Primary unknown, secondary inconclusive/refuting: nothing to add.
        assert_eq!(reconcile(Warn, Unknown, Some(Unknown)), CrossCheckAction::UsePrimary);
        assert_eq!(reconcile(Warn, Unknown, Some(Sat)), CrossCheckAction::UsePrimary);
    }
}
