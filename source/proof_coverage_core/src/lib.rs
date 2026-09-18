//! Verifier-independent proof-coverage core.
//!
//! Everything here consumes emitted `verus-proof-coverage/1` JSON records
//! only; nothing may import `vir`, `air`, or the Verus adapter. Verifier
//! knowledge (vocabulary, lowering protocols, alignment) lives in the
//! `proof_coverage` adapter crate, which depends on this one.

pub mod analysis;
pub mod audit;
pub mod facts;
pub mod identity;
pub mod licensing;
pub mod projection;
pub mod record;
pub mod rule_schema;
