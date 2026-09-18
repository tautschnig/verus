//! Verifier-independent rule-ledger schema. The Verus rule *instances*
//! (vocabulary, lowering protocols) live in the adapter (`verus::rules`).

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Strength {
    Construction,
    TypedVocabulary,
    Protocol,
    Heuristic,
}

pub struct Rule {
    pub id: &'static str,
    /// Where the classified fact is produced (the trusted-side site whose
    /// behavior the rule relies on).
    pub producer: &'static str,
    /// The signals the rule observes.
    pub signals: &'static str,
    /// What it concludes.
    pub conclusion: &'static str,
    pub strength: Strength,
    /// Constructs the rule is known to cover (probe evidence).
    pub constructs: &'static str,
    /// Probes that must NOT trigger the rule (near-match traps).
    pub negative_probes: &'static str,
}
