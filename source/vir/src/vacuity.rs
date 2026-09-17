//! Support for the `-V vacuity-checks` lint.
//!
//! This module collects the *trusted-construct inventory*: every place in the crate where
//! verification trusts the developer rather than proving something. These are `assume(..)` and
//! `admit()` sites, `#[verifier::external_body]` functions, `assume_specification` /
//! `external_fn_specification` proxies, and `#[verifier::external]` items. When a function
//! "verifies", it verifies *modulo* these constructs, so shipping the list alongside the verdict
//! is the honest answer (Task 4 items V1/V6/V7).

use crate::ast::{Constant, CrateId, ExprX, Krate};
use crate::ast_util::{fun_as_friendly_rust_name, path_as_friendly_rust_name};
use crate::messages::Span;
use crate::visitor::VisitorControlFlow;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TrustedKind {
    Assume,
    Admit,
    ExternalBody,
    AssumeSpecification,
    ExternalFn,
    ExternalType,
}

impl TrustedKind {
    pub fn label(&self) -> &'static str {
        match self {
            TrustedKind::Assume => "assume",
            TrustedKind::Admit => "admit",
            TrustedKind::ExternalBody => "external_body",
            TrustedKind::AssumeSpecification => "assume_specification",
            TrustedKind::ExternalFn => "external fn",
            TrustedKind::ExternalType => "external type",
        }
    }
}

#[derive(Clone, Debug)]
pub struct TrustedConstruct {
    pub kind: TrustedKind,
    /// Friendly name of the enclosing item (or the item itself).
    pub name: String,
    /// Source location, when we have one. `external` items only carry a path, no span.
    pub span: Option<Span>,
}

/// Walk the crate and collect every trusted construct, ordered by kind then name. Only items
/// belonging to `local` (the crate actually being verified) are reported; imported items from
/// `vstd`/`core`/other dependencies are omitted, since their trust was accounted for when those
/// crates were verified.
pub fn collect_trusted_constructs(krate: &Krate, local: &CrateId) -> Vec<TrustedConstruct> {
    let mut out: Vec<TrustedConstruct> = Vec::new();

    for function in krate.functions.iter() {
        if &function.x.name.path.krate != local {
            continue;
        }
        let name = fun_as_friendly_rust_name(&function.x.name);

        // A proxy means the function is an assume_specification / external_fn_specification:
        // its ensures clauses are trusted specs for some other (often std) function.
        if let Some(proxy) = &function.x.proxy {
            out.push(TrustedConstruct {
                kind: TrustedKind::AssumeSpecification,
                name: name.clone(),
                span: Some(proxy.span.clone()),
            });
        } else if function.x.attrs.is_external_body {
            // external_body: the body is not verified; its ensures clauses are trusted.
            out.push(TrustedConstruct {
                kind: TrustedKind::ExternalBody,
                name: name.clone(),
                span: Some(function.span.clone()),
            });
        }

        // assume(..) and admit() sites inside the (verified) body.
        if let Some(body) = &function.x.body {
            let mut sites: Vec<(TrustedKind, Span)> = Vec::new();
            crate::ast_visitor::expr_visitor_walk(body, &mut |e| {
                if let ExprX::AssertAssume { is_assume: true, expr, .. } = &e.x {
                    // `admit()` lowers to `assume(false)`; distinguish it for the report.
                    let kind = if matches!(&expr.x, ExprX::Const(Constant::Bool(false))) {
                        TrustedKind::Admit
                    } else {
                        TrustedKind::Assume
                    };
                    sites.push((kind, e.span.clone()));
                }
                VisitorControlFlow::Recurse
            });
            for (kind, span) in sites {
                out.push(TrustedConstruct { kind, name: name.clone(), span: Some(span) });
            }
        }
    }

    for fun in krate.external_fns.iter() {
        if &fun.path.krate != local {
            continue;
        }
        out.push(TrustedConstruct {
            kind: TrustedKind::ExternalFn,
            name: fun_as_friendly_rust_name(fun),
            span: None,
        });
    }
    for path in krate.external_types.iter() {
        if &path.krate != local {
            continue;
        }
        out.push(TrustedConstruct {
            kind: TrustedKind::ExternalType,
            name: path_as_friendly_rust_name(path),
            span: None,
        });
    }

    out.sort_by(|a, b| (a.kind.label(), &a.name).cmp(&(b.kind.label(), &b.name)));
    out
}
