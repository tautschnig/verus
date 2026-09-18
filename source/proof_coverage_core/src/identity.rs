//! Typed identities used inside the producer and consumers.
//!
//! SMT `:named` symbols remain compact strings at the solver boundary. These
//! types prevent transport spellings such as `pc%7%3` from becoming the data
//! model or being parsed to recover semantic identity.

use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QueryId(pub u64);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SolverToken(String);

impl SolverToken {
    pub fn new(value: impl Into<String>) -> Self {
        Self(value.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn into_string(self) -> String {
        self.0
    }
}

impl fmt::Display for SolverToken {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// Which control-flow join an SSA reconciliation equality serves. Mirrors
/// `air::var_to_const::SsaJoin`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SsaJoin {
    /// A `Switch` arm brought up to the versions after the switch.
    SwitchArm(u32),
    /// The non-breaking exit of a `Breakable`.
    Fallthrough,
    /// A `Break` brought up to the versions at its `Breakable`'s exit.
    Break,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum QuerySiteId {
    LocalAxiom(u32),
    /// A statement of the structured (pre-SSA) query, by structural path. An
    /// `Assign` statement's site labels the equality the SSA pass makes of it.
    Statement(String),
    /// The equality `var@to == var@from` the SSA pass inserts at the join of
    /// the `Switch`, `Breakable` or `Break` statement at `at`. No written
    /// statement stands behind it; the identity is the pass's own trace.
    Reconciliation { at: String, join: SsaJoin, var: String, from: u32, to: u32 },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OccurrenceId {
    pub query: QueryId,
    pub site: QuerySiteId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EvidenceId {
    Occurrence(OccurrenceId),
    Ambient(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn solver_tokens_are_opaque_transport_values() {
        let token = SolverToken::new("pc%7%13");
        assert_eq!(token.as_str(), "pc%7%13");
        assert_eq!(token.to_string(), "pc%7%13");
    }

    #[test]
    fn structural_sites_distinguish_statement_and_local_axiom() {
        let query = QueryId(7);
        let statement = EvidenceId::Occurrence(OccurrenceId {
            query,
            site: QuerySiteId::Statement("b0.s1.b2".to_string()),
        });
        let local =
            EvidenceId::Occurrence(OccurrenceId { query, site: QuerySiteId::LocalAxiom(0) });
        assert_ne!(statement, local);
    }
}
