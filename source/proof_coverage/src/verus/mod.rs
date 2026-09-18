//! The Verus adapter: everything that knows about `vir`/`air` — the
//! observer/producer, AIR classification vocabulary, SST walks and predicted
//! rows, shadow solving, and the concrete rule ledger (lowering protocols,
//! `AssumeIntent` alignment, def-vocabulary keys). New verifier knowledge
//! belongs here, never in `core`.

pub mod cfg;
pub mod classify;
pub mod rules;
pub mod shadow;

/// The record's function identity: the raw VIR path (`crate::impl&%0::view`),
/// built from `FunX.path` alone.
///
/// Not the friendly name. `path_as_friendly_rust_name` renders an impl method
/// as `<self-type path>::<ident>`, discarding the impl disambiguator *and* the
/// self type's type arguments, so it is not injective: `View for Cow<'a, T>`,
/// `Cow<'a, str>` and `Cow<'a, [T]>` all render `alloc::borrow::Cow::view`.
/// `FunX.path` distinguishes them (`impl&%0`, `%2`, `%4`), and every
/// identity-bearing field of the record uses it. Friendly names are carried
/// separately, for display only (`SourceFunction.friendly`).
pub fn fun_identity(fun: &vir::ast::Fun) -> String {
    path_identity(&fun.path)
}

/// The raw spelling of a VIR path, matching `NameCtxt`'s own segment joining.
/// `krate_to_string_ignore_stable_id` drops the stable crate id, so two
/// versions of one crate share a spelling; cross-record identity already keeps
/// such owners record-local.
pub fn path_identity(path: &vir::ast::Path) -> String {
    let mut parts = vec![vir::def::krate_to_string_ignore_stable_id(&path.krate)];
    parts.extend(path.segments.iter().map(|segment| segment.to_string()));
    parts.join("::")
}
