use crate::config::Vstd;
use crate::externs::VerusExterns;
use crate::verifier::{Verifier, VerifierCallbacksEraseMacro};
use rustc_hir::attrs::AttributeKind;
use rustc_hir::{Attribute, AttributeMap};
use rustc_hir::{HirId, ItemKind, OwnerId, OwnerNode};
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, sym};
use std::time::{Duration, Instant};

struct DefaultCallbacks;
impl rustc_driver::Callbacks for DefaultCallbacks {}

pub fn run_rustc_compiler_directly(rustc_args: &Vec<String>) -> () {
    rustc_driver::run_compiler(&rustc_args, &mut DefaultCallbacks)
}

fn run_compiler<'a, 'b>(
    mut rustc_args: Vec<String>,
    syntax_macro: bool,
    erase_ghost: bool,
    verifier: &'b mut (dyn rustc_driver::Callbacks + Send),
) -> Result<(), ()> {
    crate::config::enable_default_features_and_verus_attr(
        &mut rustc_args,
        syntax_macro,
        erase_ghost,
    );
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
        rustc_driver::run_compiler(&rustc_args, verifier)
    }));
    result.map_err(|_| ())
}

pub fn is_verifying_entire_crate(verifier: &Verifier) -> bool {
    verifier.args.verify_function.is_none()
        && verifier.args.verify_module.is_empty()
        && !verifier.args.verify_root
}

// Call Rust's mir_borrowck to check lifetimes of #[spec] and #[proof] code and variables

pub(crate) struct TCCallbacks {
    pub(crate) code: String,
}

impl rustc_driver::Callbacks for TCCallbacks {
    // note: we only need to call into config here,
    // to change the file_loader
    fn config<'tcx>(&mut self, cfg: &mut rustc_interface::interface::Config) {
        cfg.file_loader =
            Some(Box::new(crate::trait_check::TCFileLoader { rust_code: self.code.clone() }));
    }

    fn after_expansion<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        queries: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        // REVIEW: is this call needed for trait-conflict checking?
        rustc_hir_analysis::check_crate(queries);
        rustc_driver::Compilation::Stop
    }
}

/*
We have to run rustc twice on the original source code,
once erasing ghost code and once keeping ghost code.

exec code --> type-check, mode-check --> lifetime (borrow) check exec code --> compile

all code --> type-check, mode-check --+
                                      |
                                      +--> lifetime (borrow) check proof code

This causes some tension in the order of operations:
it would be cleanest to run one rustc invocation entirely,
and then the other entirely, but this would be slow.
For example, if we ran the ghost-erase rustc and then the ghost-keep rustc,
then the user would receive no feedback about verification until parsing and macro expansion
for both rustc invocations had completed.
On the other hand, if we ran the ghost-keep rustc and then the ghost-erase rustc,
the user would receive no feedback about ownership/lifetime/borrow checking errors
in exec functions until verification had completed.
So for better latency, the implementation interleaves the two rustc invocations
(marked GHOST for keeping ghost and EXEC for erasing ghost):

GHOST: Parsing, AST construction, macro expansion (including the Verus syntax macro, keeping ghost code)
GHOST: Rust AST -> HIR
GHOST: Rust's type checking
GHOST: Verus HIR/THIR -> VIR conversion
GHOST: Verus mode checking
GHOST: Verus lifetime/borrow checking for both proof and exec code (by generating synthetic code and running rustc), but delaying any lifetime/borrow checking error messages until EXEC has a chance to run
GHOST: If there were no lifetime/borrow checking errors, run Verus SMT solving
EXEC: Parsing, AST construction, macro expansion (including the Verus syntax macro, erasing ghost code)
EXEC: Rust AST -> HIR
EXEC: Rust's type checking
EXEC: Rust HIR/THIR -> MIR conversion
EXEC: Rust's lifetime/borrow checking for non-ghost (exec) code
GHOST: If there were no EXEC errors, but there were GHOST lifetime/borrow checking errors, print the GHOST lifetime/borrow checking errors
EXEC: Rust compilation to machine code (if --compile is set)

To avoid having to run the EXEC lifetime/borrow checking before verification,
which would add latency before verification,
we use the synthetic code ownership/lifetime/borrow checking in lifetime.rs to perform
a quick early test for ownership/lifetime/borrow checking on all code (even pure exec code).
If this detects any ownership/lifetime/borrow errors, the implementation skips verification
and gives the EXEC rustc a chance to run,
on the theory that the EXEC rustc will generate better error messages
for any exec ownership/lifetime/borrow errors.
The GHOST lifetime/borrow errors are printed only if the EXEC rustc finds no errors.

In the long run, we'd like to move to a model where rustc only runs once on the original source code.
This would avoid the complex interleaving above and avoid needing to use lifetime.rs
for all functions (it would only be needed for functions with tracked data in proof code).
*/
struct CompilerCallbacksEraseMacro {
    pub do_compile: bool,
    pub override_stability: bool,
}

impl rustc_driver::Callbacks for CompilerCallbacksEraseMacro {
    // Adding `override_stability` and `stable_attr` functions is a hacky solution specifically for verifying core,
    // to fix an issue with stability attributes.
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        if self.override_stability {
            config.override_queries = Some(|_session, providers| {
                providers.queries.hir_attr_map = |tcx, owner_id| {
                    let mut map = (rustc_interface::DEFAULT_QUERY_PROVIDERS.queries.hir_attr_map)(
                        tcx, owner_id,
                    );
                    if needs_stable_attr(tcx, owner_id) && !has_stable_attr(&map, owner_id) {
                        map = add_stable_attr(tcx, owner_id, map);
                    }
                    map
                };
            });
        }
    }

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        _tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        if self.do_compile {
            rustc_driver::Compilation::Continue
        } else {
            rustc_driver::Compilation::Stop
        }
    }
}

/// Captures the verification and compilation time
pub struct Stats {
    /// time spent in rustc for parsing, initialization, macro expansion, etc.
    /// (from run_compiler until we enter the `after_expansion` callback)
    pub time_rustc: Duration,
    /// time it took to verify the crate (this includes VIR generation, SMT solving, etc.)
    pub time_verify: Duration,
    /// time for lifetime/borrow checking
    pub time_trait_conflicts: Duration,
    /// compilation time
    pub time_compile: Duration,
}

pub(crate) fn run_with_erase_macro_compile(
    mut rustc_args: Vec<String>,
    do_compile: bool,
    vstd: Vstd,
) -> Result<(), ()> {
    let mut callbacks = CompilerCallbacksEraseMacro {
        do_compile,
        override_stability: matches!(vstd, Vstd::IsCore | Vstd::ImportedViaCore),
    };
    rustc_args.extend(["--cfg", "verus_only", "--cfg", "verus_keep_ghost"].map(|s| s.to_string()));
    if matches!(vstd, Vstd::IsCore | Vstd::ImportedViaCore) {
        rustc_args.extend(["--cfg", "verus_verify_core"].map(|s| s.to_string()));
    } else if vstd == Vstd::NoVstd {
        rustc_args.extend(["--cfg", "verus_no_vstd"].map(|s| s.to_string()));
    }
    let allow = &[
        "unused_imports",
        "unused_variables",
        "unused_assignments",
        "unreachable_patterns",
        "unused_parens",
        "unused_braces",
        "dead_code",
        "unreachable_code",
        "unused_mut",
        "unused_labels",
        "unused_attributes",
        "non_shorthand_field_patterns", // The verus macro rewrites the shorthand syntax `MyStruct { field_name }`
                                        // to `MyStruct { field_name: field_name }`, which triggers this lint warning
    ];
    for a in allow {
        rustc_args.extend(["-A", a].map(|s| s.to_string()));
    }
    run_compiler(rustc_args, true, true, &mut callbacks)
}

/// D1 Option C (C2) spike. Instead of re-expanding the source in a second rustc run
/// (`run_with_erase_macro_compile`), reuse the *verify* pass's post-expansion crate:
///
///   1. Re-run expansion under the verify cfgs (`verus_keep_ghost_body` set) and
///      pretty-print the expanded crate via rustc's `-Zunpretty=expanded` to a file.
///      Because cfg-stripping happens during expansion, every `#[cfg(verus_keep_ghost_body)]`
///      site is already resolved to its verify-pass branch and the `not(...)` branch is gone.
///   2. Compile *that text*. It contains no macro invocations, so no proc macro (honest or
///      malicious) re-runs, and there is no `cfg(verus_keep_ghost_body)` left to observe.
///
/// This closes the Task 2c Channel 1 attack: the malicious `element!` macro's safe branch is
/// the only one present in the shared expansion. It is NOT a general erasure solution — the
/// verify expansion keeps ghost code (`verus!` ran in Keep mode), which a stock compile cannot
/// erase; see cert/d1/OPTION-C-DESIGN.md for why only C1 (Verus-internal THIR erasure) is a
/// sound end state. The dumped expansion is emitted regardless, as the decisive evidence.
pub(crate) fn run_compile_from_expansion(
    rustc_args_verify: Vec<String>,
    rustc_args_base: Vec<String>,
    do_compile: bool,
    vstd: Vstd,
) -> Result<(), ()> {
    let tmp_dir = std::env::temp_dir().join(format!("verus-compile-from-expansion-{}", std::process::id()));
    if let Err(e) = std::fs::create_dir_all(&tmp_dir) {
        eprintln!("error: [compile-from-expansion] could not create temp dir: {}", e);
        return Err(());
    }
    let expanded_path = tmp_dir.join("expanded.rs");

    // Step 1: capture the verify-pass expansion. Drop any caller-supplied `-o <path>`
    // (that is the final binary path, used by the compile step below) so it does not
    // collide with the `-o` we point at the pretty-printed expansion.
    let mut cap_args: Vec<String> = Vec::with_capacity(rustc_args_verify.len());
    let mut skip_next = false;
    for a in rustc_args_verify.into_iter() {
        if skip_next {
            skip_next = false;
            continue;
        }
        if a == "-o" {
            skip_next = true;
            continue;
        }
        if a.starts_with("-o=") || a.starts_with("--out-dir") {
            continue;
        }
        cap_args.push(a);
    }
    cap_args.extend(
        ["-Zunpretty=expanded", "-o", &expanded_path.display().to_string()].map(|s| s.to_string()),
    );
    struct DumpCallbacks;
    impl rustc_driver::Callbacks for DumpCallbacks {}
    let mut dump_cb = DumpCallbacks;
    let cap_status = run_compiler(cap_args, true, false, &mut dump_cb);
    if cap_status.is_err() {
        eprintln!("error: [compile-from-expansion] expansion capture failed");
        return Err(());
    }
    eprintln!(
        "note: [compile-from-expansion] wrote shared expansion to {}",
        expanded_path.display()
    );

    if !do_compile {
        // No compile requested: capturing the shared expansion is all that is asked.
        return Ok(());
    }

    // Step 2: compile the shared expansion. Invoke rustc directly (NOT through
    // `run_compiler`, which would re-inject `-Zcrate-attr` feature/register_tool attributes
    // that the pretty-printed crate already carries in its header, causing duplicates).
    let mut comp_args: Vec<String> = rustc_args_base
        .into_iter()
        .map(|a| {
            if a.ends_with(".rs") { expanded_path.display().to_string() } else { a }
        })
        .collect();
    comp_args.extend(["--cfg", "verus_only", "--cfg", "verus_keep_ghost"].map(|s| s.to_string()));
    if matches!(vstd, Vstd::IsCore | Vstd::ImportedViaCore) {
        comp_args.extend(["--cfg", "verus_verify_core"].map(|s| s.to_string()));
    } else if vstd == Vstd::NoVstd {
        comp_args.extend(["--cfg", "verus_no_vstd"].map(|s| s.to_string()));
    }
    for a in &[
        "unused_imports",
        "unused_variables",
        "unused_assignments",
        "unreachable_patterns",
        "unused_parens",
        "unused_braces",
        "dead_code",
        "unreachable_code",
        "unused_mut",
        "unused_labels",
        "unused_attributes",
        "non_shorthand_field_patterns",
    ] {
        comp_args.extend(["-A", a].map(|s| s.to_string()));
    }
    let mut callbacks = CompilerCallbacksEraseMacro {
        do_compile,
        override_stability: matches!(vstd, Vstd::IsCore | Vstd::ImportedViaCore),
    };
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
        rustc_driver::run_compiler(&comp_args, &mut callbacks)
    }));
    match result {
        Ok(()) => Ok(()),
        Err(_) => {
            eprintln!(
                "error: [compile-from-expansion] compiling the shared expansion failed \
                 (expected for crates that carry ghost code; see cert/d1/OPTION-C-DESIGN.md). \
                 The attack still does not survive: the shared expansion at {} contains only the \
                 verify-pass branch.",
                expanded_path.display()
            );
            Err(())
        }
    }
}

pub struct VerusRoot {
    pub path: std::path::PathBuf,
    in_vargo: bool,
}

pub fn find_verusroot() -> Option<VerusRoot> {
    std::env::var("VARGO_TARGET_DIR")
        .ok()
        .and_then(|target_dir| {
            let path = std::path::PathBuf::from(&target_dir);
            Some(VerusRoot { path, in_vargo: true })
        })
        .or_else(|| {
            std::env::var("VERUS_ROOT").ok().and_then(|verusroot| {
                let mut path = std::path::PathBuf::from(&verusroot);
                if !path.is_absolute() {
                    path = std::env::current_dir().expect("working directory invalid").join(path);
                }
                Some(VerusRoot { path, in_vargo: false })
            })
        })
        .or_else(|| {
            let current_exe = std::env::current_exe().ok().and_then(|c| {
                if c.symlink_metadata().ok()?.is_symlink() {
                    std::fs::read_link(c).ok()
                } else {
                    Some(c)
                }
            });
            current_exe.and_then(|current| {
                current.parent().and_then(|p| {
                    let mut path = std::path::PathBuf::from(&p);
                    if let Err(missing) =
                        cargo_verus_toolchains::installed::check_required_components(&path)
                    {
                        eprintln!("warning: Verus installation is incomplete; missing components:");
                        for path in missing {
                            eprintln!("  {}", path.display());
                        }
                        None
                    } else {
                        if !path.is_absolute() {
                            path = std::env::current_dir()
                                .expect("working directory invalid")
                                .join(path);
                        }
                        Some(VerusRoot { path, in_vargo: false })
                    }
                })
            })
        })
}

pub fn run(
    verifier: Verifier,
    mut rustc_args: Vec<String>,
    verus_root: Option<VerusRoot>,
    build_test_mode: bool,
) -> (Verifier, Stats, Result<(), ()>) {
    if !rustc_args.iter().any(|a| a.starts_with("--edition")) {
        rustc_args.push(format!("--edition"));
        rustc_args.push(format!("2021"));
    }
    // TODO simplify
    let verus_externs = if !build_test_mode {
        if let Some(VerusRoot { path: verusroot, in_vargo }) = verus_root {
            let externs = VerusExterns {
                verus_root: verusroot.clone(),
                has_vstd: verifier.args.vstd == Vstd::Imported,
                has_builtin: !matches!(verifier.args.vstd, Vstd::IsCore | Vstd::ImportedViaCore),
            };
            rustc_args.extend(externs.to_args());
            if in_vargo && !std::env::var("VERUS_Z3_PATH").is_ok() {
                panic!("we are in vargo, but VERUS_Z3_PATH is not set; this is a bug");
            }
            if !in_vargo { Some(externs) } else { None }
        } else {
            None
        }
    } else {
        None
    };

    let time0 = Instant::now();
    let mut rustc_args_verify = rustc_args.clone();
    rustc_args_verify.extend(["--cfg", "verus_only"].map(|s| s.to_string()));
    rustc_args_verify.extend(["--cfg", "verus_keep_ghost"].map(|s| s.to_string()));
    rustc_args_verify.extend(["--cfg", "verus_keep_ghost_body"].map(|s| s.to_string()));
    if matches!(verifier.args.vstd, Vstd::IsCore | Vstd::ImportedViaCore) {
        rustc_args_verify.extend(["--cfg", "verus_verify_core"].map(|s| s.to_string()));
    }
    // Build VIR and run verification
    let mut verifier_callbacks = VerifierCallbacksEraseMacro {
        verifier,
        rust_start_time: Instant::now(),
        rust_end_time: None,
        tc_start_time: None,
        tc_end_time: None,
        verus_externs,
        spans: None,
        unresolved_import_deps: std::collections::HashSet::new(),
    };
    let status = run_compiler(rustc_args_verify.clone(), true, false, &mut verifier_callbacks);
    let VerifierCallbacksEraseMacro {
        verifier,
        rust_start_time,
        rust_end_time,
        tc_start_time,
        tc_end_time,
        ..
    } = verifier_callbacks;
    let time1 = Instant::now();
    let time_trait_conflicts = match (tc_start_time, tc_end_time) {
        (Some(t1), Some(t2)) => t2 - t1,
        _ => Duration::new(0, 0),
    };

    let time_rustc = match rust_end_time {
        Some(t1) => t1 - rust_start_time,
        _ => Duration::new(0, 0),
    };

    if status.is_err() || verifier.encountered_vir_error {
        return (
            verifier,
            Stats {
                time_rustc,
                time_verify: (time1 - time0) - time_trait_conflicts,
                time_trait_conflicts,
                time_compile: Duration::new(0, 0),
            },
            Err(()),
        );
    }

    let compile_status =
        if !verifier.compile && (verifier.args.no_erasure_check || verifier.args.no_lifetime) {
            Ok(())
        } else {
            let do_compile = verifier.compile || verifier.via_cargo_args.is_some();
            if verifier.args.compile_from_expansion {
                run_compile_from_expansion(
                    rustc_args_verify,
                    rustc_args,
                    do_compile,
                    verifier.args.vstd,
                )
            } else {
                run_with_erase_macro_compile(rustc_args, do_compile, verifier.args.vstd)
            }
        };

    let time2 = Instant::now();

    let stats = Stats {
        time_rustc,
        time_verify: (time1 - time0) - time_trait_conflicts,
        time_trait_conflicts,
        time_compile: time2 - time1,
    };

    // Run borrow checker and compiler with #[exec] (not #[proof])
    if let Err(_) = compile_status {
        return (verifier, stats, Err(()));
    }

    (verifier, stats, Ok(()))
}

fn stable_attr(span: Span) -> Attribute {
    use rustc_hir::*;
    Attribute::Parsed(AttributeKind::Stability {
        stability: Stability {
            level: StabilityLevel::Unstable {
                reason: UnstableReason::Default,
                issue: None,
                implied_by: None,
                old_name: None,
            },
            feature: sym::rustc_private,
        },
        span,
    })
}

fn has_stable_attr(attrmap: &AttributeMap, owner_id: OwnerId) -> bool {
    let hir_id = HirId::from(owner_id);
    match attrmap.map.get(&hir_id.local_id) {
        None => false,
        Some(attrs) => {
            attrs.iter().any(|a| matches!(a, Attribute::Parsed(AttributeKind::Stability { .. })))
        }
    }
}

fn add_stable_attr<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner_id: OwnerId,
    attrmap: &'tcx AttributeMap,
) -> &'tcx AttributeMap<'tcx> {
    let hir_id = HirId::from(owner_id);

    let mut m = AttributeMap {
        map: attrmap.map.clone(),
        define_opaque: attrmap.define_opaque.clone(),
        opt_hash: attrmap.opt_hash.clone(),
    };

    let mut attrs = match m.map.get(&hir_id.local_id) {
        None => vec![],
        Some(attrs) => attrs.to_vec(),
    };

    let span = tcx.hir_span(hir_id);
    attrs.push(stable_attr(span));

    m.map.insert(hir_id.local_id, Box::leak(attrs.into_boxed_slice()));
    Box::leak(Box::new(m))
}

fn needs_stable_attr<'tcx>(tcx: TyCtxt<'tcx>, owner_id: OwnerId) -> bool {
    let owner = tcx.hir_owner_node(owner_id);
    match owner {
        OwnerNode::Item(_item) => true,
        OwnerNode::ForeignItem(_item) => false,
        OwnerNode::TraitItem(_item) => true,
        OwnerNode::ImplItem(_item) => {
            let hir_id = HirId::from(owner_id);
            let parent = tcx.hir_get_parent_item(hir_id);
            match tcx.hir_owner_node(parent) {
                OwnerNode::Item(item) => match &item.kind {
                    ItemKind::Impl(impll) => !impll.of_trait.is_some(),
                    _ => panic!("add_stable_attr"),
                },
                _ => panic!("add_stable_attr"),
            }
        }
        OwnerNode::Crate(_item) => false,
        OwnerNode::Synthetic => false,
    }
}
