use crate::context::Context;
use crate::verus_items::RustItem;
use rustc_hir::HirId;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    BinaryOp, CallTarget, Expr, ExprX, FieldOpr, FunctionX, Mode, Place, PlaceX, ReadKind,
    SpannedTyped, TypDecoration, TypX, UnaryOpr, UnfinalizedReadKind, VariantCheck, VirErr,
    VirErrAs,
};
use vir::def::Spanned;
use vir::messages::WarningAllow;

/// Traits with special handling
#[derive(Clone, Copy, Debug)]
pub enum SpecialTrait {
    Clone,
    //PartialEq,
}

/// What to do for a given automatically-derived trait impl
#[derive(Debug)]
pub enum AutomaticDeriveAction {
    Special(SpecialTrait),
    VerifyAsIs,
    /// Ignore, optionally providing a warning
    Ignore,
}

pub fn get_action(rust_item: Option<RustItem>) -> AutomaticDeriveAction {
    match rust_item {
        Some(RustItem::PartialEq | RustItem::Eq) => AutomaticDeriveAction::Ignore,
        Some(RustItem::Clone) => AutomaticDeriveAction::Special(SpecialTrait::Clone),

        Some(RustItem::Copy) => AutomaticDeriveAction::VerifyAsIs,

        Some(RustItem::Hash)
        | Some(RustItem::Default)
        | Some(RustItem::Debug)
        | Some(RustItem::Ord)
        | Some(RustItem::PartialOrd) => AutomaticDeriveAction::Ignore,

        Some(_) | None => AutomaticDeriveAction::VerifyAsIs,
    }
}

pub fn is_automatically_derived(attrs: &[rustc_hir::Attribute]) -> bool {
    for attr in attrs.iter() {
        match attr {
            rustc_hir::Attribute::Unparsed(item) => match &item.path.segments[..] {
                [segment] => {
                    if segment.as_str() == "automatically_derived" {
                        return true;
                    }
                }
                _ => {}
            },
            rustc_hir::Attribute::Parsed(rustc_hir::attrs::AttributeKind::AutomaticallyDerived) => {
                return true;
            }
            _ => {}
        }
    }
    false
}

pub fn modify_derived_item<'tcx>(
    ctxt: &Context<'tcx>,
    id: rustc_span::def_id::DefId,
    inputs: &Vec<rustc_middle::ty::Ty>,
    span: Span,
    hir_id: HirId,
    action: &AutomaticDeriveAction,
    function: &mut FunctionX,
) -> Result<Option<vir::ast::Function>, VirErr> {
    let AutomaticDeriveAction::Special(special) = action else {
        return Ok(None);
    };
    match special {
        SpecialTrait::Clone => {
            if &*function.name.path.last_segment() == "clone" {
                return clone_add_post_condition(ctxt, id, inputs, span, hir_id, function);
            }
        }
    }
    Ok(None)
}

fn clone_add_post_condition<'tcx>(
    ctxt: &Context<'tcx>,
    mut id: rustc_span::def_id::DefId,
    inputs: &Vec<rustc_middle::ty::Ty>,
    span: Span,
    hir_id: HirId,
    functionx: &mut FunctionX,
) -> Result<Option<vir::ast::Function>, VirErr> {
    let mut adt_did: Option<rustc_span::def_id::DefId> = None;
    if inputs.len() >= 1 {
        use rustc_middle::ty::{AdtDef, TyKind};
        if let TyKind::Ref(_, t, _) = inputs[0].kind() {
            if let TyKind::Adt(AdtDef(adt_def_data), _) = t.kind() {
                // It's more convenient to put verifier::allow on the datatype than on the function
                id = adt_def_data.did;
                adt_did = Some(adt_def_data.did);
            }
        }
    }
    let warn = |msg: &str| {
        crate::attributes::warning_maybe(
            ctxt.tcx,
            id,
            span,
            &WarningAllow::AutoderiveCloneWithoutSpec,
            || msg,
            |msg| ctxt.diagnostics.borrow_mut().push(VirErrAs::Warning(msg)),
        );
    };
    let warn_unexpected = || {
        warn(
            "autoderive Clone impl does not take the form Verus expects; continuing, but without adding a specification for the derived Clone impl",
        )
    };
    let warn_unsupported = || {
        warn(
            "Verus does not (yet) support this autoderive Clone impl; continuing, but without adding a specification for the derived Clone impl",
        )
    };

    let Some(body) = &functionx.body else {
        return Ok(None);
    };

    if functionx.ensure.0.len() != 0 {
        warn_unexpected();
        return Ok(None);
    }

    let ExprX::Block(_stmts, Some(last_expr)) = &body.x else {
        warn_unexpected();
        return Ok(None);
    };

    // `self` as a spec value (the referent of the &self parameter) and the return value.
    let self_param = &functionx.params[0];
    let self_typ = match &*self_param.x.typ {
        TypX::Decorate(TypDecoration::Ref, _, t) => t.clone(),
        _ => {
            warn_unexpected();
            return Ok(None);
        }
    };
    let self_place = SpannedTyped::new(
        &last_expr.span,
        &self_param.x.typ,
        PlaceX::Local(self_param.x.name.clone()),
    );
    // Immutable dereference is implicit in VIR: reading the `&Self` parameter yields the value,
    // and the expression carries the referent type.
    let self_val = SpannedTyped::new(
        &last_expr.span,
        &self_typ,
        ExprX::ReadPlace(
            self_place,
            UnfinalizedReadKind { preliminary_kind: ReadKind::Copy, id: 0 },
        ),
    );
    // Inside the synthesized predicate the clone result is a parameter named `clone_result`;
    // the method's own `ensures` passes its return value for it.
    let ret_spec_name =
        vir::ast_util::str_unique_var("clone_result", vir::ast::VarIdentDisambiguate::AirLocal);
    let ret_var = SpannedTyped::new(&last_expr.span, &self_typ, ExprX::Var(ret_spec_name.clone()));
    let method_ret_var =
        SpannedTyped::new(&last_expr.span, &self_typ, ExprX::Var(functionx.ret.x.name.clone()));

    let ensure = match &last_expr.x {
        ExprX::ReadPlace(pl, _) => match &pl.x {
            // `*self` (a Copy type): ensures ret == self
            PlaceX::Local(id) if &*id.0 == "self" => SpannedTyped::new(
                &last_expr.span,
                &vir::ast_util::bool_typ(),
                ExprX::Binary(BinaryOp::Eq(Mode::Spec), ret_var.clone(), self_val.clone()),
            ),
            _ => {
                warn_unexpected();
                return Ok(None);
            }
        },
        // struct: `S { f: Clone::clone(&self.f), .. }`
        // ensures forall fields f: cloned(self.f, ret.f)
        ExprX::Ctor(dt, variant, binders, None) => {
            let Some(conjuncts) =
                fieldwise_cloned(ctxt, &last_expr.span, dt, variant, binders, &self_val, &ret_var)
            else {
                warn_unsupported();
                return Ok(None);
            };
            vir::ast_util::conjoin(&last_expr.span, &conjuncts)
        }
        // enum: `match self { V(a, ..) => V(Clone::clone(a), ..), .. }`
        // ensures for each variant V: self is V ==> ret is V && fieldwise cloned
        ExprX::Match(_, arms, _) => {
            let mut conjuncts: Vec<Expr> = Vec::new();
            for arm in arms.iter() {
                let ExprX::Ctor(dt, variant, binders, None) = &arm.x.body.x else {
                    warn_unsupported();
                    return Ok(None);
                };
                let Some(fields) = fieldwise_cloned(
                    ctxt,
                    &last_expr.span,
                    dt,
                    variant,
                    binders,
                    &self_val,
                    &ret_var,
                ) else {
                    warn_unsupported();
                    return Ok(None);
                };
                let is_variant = |e: &Expr| {
                    SpannedTyped::new(
                        &last_expr.span,
                        &vir::ast_util::bool_typ(),
                        ExprX::UnaryOpr(
                            UnaryOpr::IsVariant { datatype: dt.clone(), variant: variant.clone() },
                            e.clone(),
                        ),
                    )
                };
                let mut rhs = vec![is_variant(&ret_var)];
                rhs.extend(fields);
                let rhs = vir::ast_util::conjoin(&last_expr.span, &rhs);
                conjuncts.push(SpannedTyped::new(
                    &last_expr.span,
                    &vir::ast_util::bool_typ(),
                    ExprX::Logical(vir::ast::LogicalOp::Implies, is_variant(&self_val), rhs),
                ));
            }
            vir::ast_util::conjoin(&last_expr.span, &conjuncts)
        }
        _ => {
            warn_unexpected();
            return Ok(None);
        }
    };

    let ensure = cleanup_span_ids(ctxt, span, hir_id, &ensure);

    // The fieldwise postcondition names the datatype's fields, which a public method's
    // `ensures` may not do when some field is not public. So the postcondition is a call to
    // a synthesized `closed spec fn clone_spec(self, ret)` whose body is the fieldwise
    // conjunction: the predicate is well-formed everywhere, and its body is visible exactly
    // where the fields are (the datatype's transparency: the join of the datatype's visibility
    // with its fields'). Callers outside that scope get an opaque fact, which is all they could
    // use anyway; callers inside see the fields.
    let mut body_vis = functionx.visibility.clone();
    if let Some(adt_did) = adt_did {
        body_vis = body_vis.join(&crate::rust_to_vir_base::mk_visibility(ctxt, adt_did));
        let adt_def = ctxt.tcx.adt_def(adt_did);
        for variant in adt_def.variants().iter() {
            for field in variant.fields.iter() {
                body_vis = body_vis
                    .join(&crate::rust_to_vir_base::mk_visibility_from_vis(ctxt, field.vis));
            }
        }
    }
    let spec_name = Arc::new(vir::ast::FunX {
        path: functionx.name.path.pop_segment().push_segment(Arc::new("clone_spec".to_string())),
    });
    let mk_spec_param = |p: &vir::ast::Param| {
        Spanned::new(
            p.span.clone(),
            vir::ast::ParamX {
                name: p.x.name.clone(),
                typ: p.x.typ.clone(),
                mode: Mode::Spec,
                unwrapped_info: None,
                user_mut: false,
            },
        )
    };
    let ret_spec_param = Spanned::new(
        functionx.ret.span.clone(),
        vir::ast::ParamX {
            name: ret_spec_name.clone(),
            typ: functionx.ret.x.typ.clone(),
            mode: Mode::Spec,
            unwrapped_info: None,
            user_mut: false,
        },
    );
    let bool_ret = Spanned::new(
        functionx.ret.span.clone(),
        vir::ast::ParamX {
            name: vir::ast_util::air_unique_var(vir::def::RETURN_VALUE),
            typ: vir::ast_util::bool_typ(),
            mode: Mode::Spec,
            unwrapped_info: None,
            user_mut: false,
        },
    );
    let spec_fn = ctxt.spanned_new(
        span,
        FunctionX {
            name: spec_name.clone(),
            proxy: None,
            kind: vir::ast::FunctionKind::Static,
            visibility: functionx.visibility.clone(),
            body_visibility: vir::ast::BodyVisibility::Visibility(body_vis.clone()),
            opaqueness: vir::ast::Opaqueness::Revealed { visibility: body_vis },
            owning_module: functionx.owning_module.clone(),
            mode: Mode::Spec,
            typ_params: functionx.typ_params.clone(),
            typ_bounds: functionx.typ_bounds.clone(),
            params: Arc::new(vec![mk_spec_param(self_param), ret_spec_param]),
            ret: bool_ret,
            ens_has_return: true,
            require: Arc::new(vec![]),
            ensure: (Arc::new(vec![]), Arc::new(vec![])),
            returns: None,
            decrease: Arc::new(vec![]),
            decrease_when: None,
            decrease_by: None,
            fndef_axioms: None,
            mask_spec: None,
            atomic_update: None,
            unwind_spec: None,
            item_kind: vir::ast::ItemKind::Function,
            attrs: Default::default(),
            body: Some(ensure),
            extra_dependencies: vec![],
            async_ret: None,
        },
    );
    // ensures clone_spec(self, ret)
    let self_arg = SpannedTyped::new(
        &last_expr.span,
        &self_param.x.typ,
        ExprX::ReadPlace(
            SpannedTyped::new(
                &last_expr.span,
                &self_param.x.typ,
                PlaceX::Local(self_param.x.name.clone()),
            ),
            UnfinalizedReadKind { preliminary_kind: ReadKind::Copy, id: 0 },
        ),
    );
    let call = SpannedTyped::new(
        &last_expr.span,
        &vir::ast_util::bool_typ(),
        ExprX::Call {
            target: CallTarget::Fun(
                vir::ast::CallTargetKind::Static,
                spec_name,
                Arc::new(
                    functionx
                        .typ_params
                        .iter()
                        .map(|x| Arc::new(TypX::TypParam(x.clone())))
                        .collect(),
                ),
                Arc::new(vec![]),
                vir::ast::CallTargetAttrs {
                    autospec: vir::ast::AutospecUsage::IfMarked,
                    const_var: false,
                    assume_external_allowed: false,
                },
            ),
            args: Arc::new(vec![self_arg, method_ret_var]),
            post_args: None,
            body: None,
        },
    );
    let call = cleanup_span_ids(ctxt, span, hir_id, &call);
    functionx.ensure.0 = Arc::new(vec![call]);
    Ok(Some(spec_fn))
}

/// For a derived clone body `V { f: Clone::clone(&self.f) | *self.f, .. }`, the conjuncts
/// `cloned::<T_f>(self.f, ret.f)` for each field (or `ret.f == self.f` for a copied field).
/// `cloned` (vstd::pervasive) is `strictly_cloned || equal`, so it also covers a `clone`
/// specification that returns the value itself. None if a field initializer has another shape.
fn fieldwise_cloned<'tcx>(
    ctxt: &Context<'tcx>,
    span: &vir::messages::Span,
    dt: &vir::ast::Dt,
    variant: &vir::ast::Ident,
    binders: &vir::ast::Binders<Expr>,
    self_val: &Expr,
    ret_var: &Expr,
) -> Option<Vec<Expr>> {
    if ctxt.no_vstd {
        return None;
    }
    let mut conjuncts: Vec<Expr> = Vec::new();
    for binder in binders.iter() {
        let field_typ = binder.a.typ.clone();
        // spec-mode field read: ReadPlace(Field(.., Temporary(e)))
        let field = |e: &Expr| {
            let base = SpannedTyped::new(span, &e.typ, PlaceX::Temporary(e.clone()));
            let place = SpannedTyped::new(
                span,
                &field_typ,
                PlaceX::Field(
                    FieldOpr {
                        datatype: dt.clone(),
                        variant: variant.clone(),
                        field: binder.name.clone(),
                        get_variant: false,
                        check: VariantCheck::None,
                    },
                    base,
                ),
            );
            SpannedTyped::new(
                span,
                &field_typ,
                ExprX::ReadPlace(
                    place,
                    UnfinalizedReadKind { preliminary_kind: ReadKind::Copy, id: 0 },
                ),
            )
        };
        let (self_f, ret_f) = (field(self_val), field(ret_var));
        let is_clone_call = match &binder.a.x {
            ExprX::Call { target: CallTarget::Fun(_, fun, _, _, _), .. } => {
                &*fun.path.last_segment() == "clone"
            }
            _ => false,
        };
        if is_clone_call {
            let fun = vir::fun!(vir::ast::CrateId::Vstd => "pervasive", "cloned");
            let target = CallTarget::Fun(
                vir::ast::CallTargetKind::Static,
                fun,
                Arc::new(vec![field_typ.clone()]),
                Arc::new(vec![]),
                vir::ast::CallTargetAttrs {
                    autospec: vir::ast::AutospecUsage::IfMarked,
                    const_var: false,
                    assume_external_allowed: false,
                },
            );
            conjuncts.push(SpannedTyped::new(
                span,
                &vir::ast_util::bool_typ(),
                ExprX::Call {
                    target,
                    args: Arc::new(vec![self_f, ret_f]),
                    post_args: None,
                    body: None,
                },
            ));
        } else if matches!(&binder.a.x, ExprX::ReadPlace(..)) {
            // a Copy field read directly
            conjuncts.push(SpannedTyped::new(
                span,
                &vir::ast_util::bool_typ(),
                ExprX::Binary(BinaryOp::Eq(Mode::Spec), ret_f, self_f),
            ));
        } else {
            return None;
        }
    }
    Some(conjuncts)
}

// TODO better place for this
fn cleanup_span_ids<'tcx>(ctxt: &Context<'tcx>, span: Span, hir_id: HirId, expr: &Expr) -> Expr {
    vir::ast_visitor::map_expr_place_visitor(
        expr,
        &|e: &Expr| {
            let e = ctxt.spans.spanned_typed_new(span, &e.typ, e.x.clone());
            let mut erasure_info = ctxt.erasure_info.borrow_mut();
            erasure_info.hir_vir_ids.push((Some(hir_id), e.span.id));
            Ok(e)
        },
        &|p: &Place| {
            let p = ctxt.spans.spanned_typed_new(span, &p.typ, p.x.clone());
            let mut erasure_info = ctxt.erasure_info.borrow_mut();
            erasure_info.hir_vir_ids.push((Some(hir_id), p.span.id));
            Ok(p)
        },
    )
    .unwrap()
}
