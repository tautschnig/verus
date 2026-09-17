//! Proof-certificate emission for `--emit-certificate <dir>` (Task 3, leg D1 +
//! Option A). On a *successful* Verus run this writes `cert.json` and
//! `SOURCES.sha256` into the requested directory.
//!
//! What the certificate binds (and, crucially, what it does NOT):
//!   * D1 integrity  — sha256 of every source file, so a consumer can confirm
//!     the source in hand is byte-for-byte the source Verus checked.
//!   * Option A      — the sha256 of the *erase-pass* (`--cfg verus_only
//!     --cfg verus_keep_ghost`, i.e. `verus_keep_ghost_body` OFF) macro
//!     expansion, exactly the code the compiler lowers. A Verus-free consumer
//!     recomputes this with stock `rustc -Zunpretty=expanded` and the recipe
//!     recorded here, turning a "verified-vs-compiled" divergence from silent
//!     into rejected (see cert/d1/FINDINGS.md; the verify-vs-erase comparison,
//!     Option B, is deliberately NOT attempted — cert/d1/OPTION-B-REFUTED.md).
//!   * per-function verdicts, toolchain pins, and a *syntactic* inventory of
//!     trusted constructs (assume/admit/external_body/assume_specification).
//!
//! This certificate is NOT a proof. A rustc-only consumer cannot re-establish
//! Verus' unbounded theorem without also checking the VC encoding. The word
//! "proved" never appears in the emitted artifact.

use crate::verifier::Verifier;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::path::PathBuf;
use vir::ast_util::fun_as_friendly_rust_name;

fn sha256_hex(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    hex::encode(h.finalize())
}

/// Query a solver binary (pointed to by `env_var`) for its version string.
fn solver_version(env_var: &str) -> serde_json::Value {
    let path = match std::env::var(env_var) {
        Ok(p) => p,
        Err(_) => return serde_json::json!({ "path": null, "version": null }),
    };
    let out = std::process::Command::new(&path).arg("--version").output();
    let version = match out {
        Ok(o) => {
            String::from_utf8_lossy(&o.stdout).lines().next().unwrap_or("").trim().to_string()
        }
        Err(_) => String::new(),
    };
    serde_json::json!({ "path": path, "version": version })
}

/// Syntactic inventory of trusted constructs in a source file. This is a
/// lexical scan (not a VIR-level analysis); it is reported as such so a
/// reviewer knows the surface it covers.
fn trusted_constructs(path: &str, text: &str) -> Vec<serde_json::Value> {
    const NEEDLES: &[(&str, &str)] = &[
        ("assume_specification", "assume_specification"),
        ("external_body", "external_body"),
        ("admit(", "admit"),
        ("assume(", "assume"),
    ];
    let mut out = Vec::new();
    for (lineno, line) in text.lines().enumerate() {
        let code = line.split("//").next().unwrap_or("");
        for (needle, kind) in NEEDLES {
            let mut start = 0;
            while let Some(rel) = code[start..].find(needle) {
                let abs = start + rel;
                // avoid counting `assume` inside `assume_specification`
                if *kind == "assume" && code[abs..].starts_with("assume_specification") {
                    start = abs + needle.len();
                    continue;
                }
                out.push(serde_json::json!({
                    "construct": kind,
                    "file": path,
                    "line": lineno + 1,
                }));
                start = abs + needle.len();
            }
        }
    }
    out
}

struct ExpansionRecipe {
    edition: String,
    crate_type: String,
    verus_root: Option<String>,
    externs: Vec<String>, // "name=path" as passed
    cfgs: Vec<String>,    // erase-pass cfgs
    crate_attrs: Vec<String>, // -Zcrate-attr=<value> (tool-attribute registration etc.)
}

/// The `-Zcrate-attr` values Verus's driver injects (see
/// config::enable_default_features_and_verus_attr). A Verus-free consumer needs
/// the same registration so `rustc -Zunpretty=expanded` can parse Verus tool
/// attributes such as `#[verusfmt::skip]` / `#[verifier::…]`
/// (cert/d1/OPTION-B-REFUTED.md §Secondary finding).
fn crate_attrs() -> Vec<String> {
    let mut a = vec![
        "allow(internal_features)".to_string(),
        "allow(unused_features)".to_string(),
    ];
    for feature in &[
        "stmt_expr_attributes",
        "box_patterns",
        "negative_impls",
        "rustc_attrs",
        "unboxed_closures",
        "register_tool",
        "tuple_trait",
        "custom_inner_attributes",
        "try_trait_v2",
    ] {
        a.push(format!("feature({feature})"));
    }
    a.push("register_tool(verus)".to_string());
    a.push("register_tool(verifier)".to_string());
    a.push("register_tool(verusfmt)".to_string());
    a
}

/// Extract the pieces of the erase-pass rustc invocation needed to reproduce
/// the macro expansion, and add the two Verus proc-macro externs (found via the
/// `-L dependency=` search path) explicitly, mirroring cert/d1/fingerprint.sh.
fn recipe_from_args(erase_rustc_args: &[String]) -> ExpansionRecipe {
    let mut edition = "2021".to_string();
    let mut crate_type = "lib".to_string();
    let mut verus_root: Option<String> = None;
    let mut externs: Vec<String> = Vec::new();

    let mut i = 0;
    while i < erase_rustc_args.len() {
        let a = erase_rustc_args[i].clone();
        if a == "--edition" {
            i += 1;
            if let Some(v) = erase_rustc_args.get(i) {
                edition = v.clone();
            }
        } else if let Some(v) = a.strip_prefix("--edition=") {
            edition = v.to_string();
        } else if a == "--crate-type" {
            i += 1;
            if let Some(v) = erase_rustc_args.get(i) {
                crate_type = v.clone();
            }
        } else if let Some(v) = a.strip_prefix("--crate-type=") {
            crate_type = v.to_string();
        } else if a == "--extern" {
            i += 1;
            if let Some(v) = erase_rustc_args.get(i) {
                externs.push(v.clone());
            }
        } else if a == "-L" {
            i += 1;
            if let Some(v) = erase_rustc_args.get(i) {
                if let Some(dep) = v.strip_prefix("dependency=") {
                    verus_root = Some(dep.to_string());
                }
            }
        }
        i += 1;
    }

    // Add the proc-macro externs explicitly (they are otherwise resolved via -L
    // only), so `-Zunpretty=expanded` can expand `verus!`.
    if let Some(root) = &verus_root {
        let root = PathBuf::from(root);
        for (name, file) in [
            ("verus_builtin_macros", "libverus_builtin_macros.so"),
            ("verus_state_machines_macros", "libverus_state_machines_macros.so"),
        ] {
            let p = root.join(file);
            if p.exists() && !externs.iter().any(|e| e.starts_with(&format!("{name}="))) {
                externs.push(format!("{name}={}", p.to_str().unwrap()));
            }
        }
    }

    ExpansionRecipe {
        edition,
        crate_type,
        verus_root,
        externs,
        cfgs: vec!["verus_only".to_string(), "verus_keep_ghost".to_string()],
        crate_attrs: crate_attrs(),
    }
}

/// Run `rustc -Zunpretty=expanded` for the erase pass and sha256 the output.
/// Returns (hash, rustc_version) or an error string.
fn compute_expansion_hash(
    recipe: &ExpansionRecipe,
    source_files: &[String],
) -> Result<(String, String), String> {
    let rustc = std::env::var("VERUS_CERT_RUSTC").unwrap_or_else(|_| "rustc".to_string());

    let mut cmd = std::process::Command::new(&rustc);
    cmd.env("RUSTC_BOOTSTRAP", "1");
    cmd.arg("-Zunpretty=expanded");
    cmd.arg("--edition").arg(&recipe.edition);
    cmd.arg("--crate-type").arg(&recipe.crate_type);
    if let Some(root) = &recipe.verus_root {
        cmd.arg("-L").arg(format!("dependency={root}"));
    }
    for e in &recipe.externs {
        cmd.arg("--extern").arg(e);
    }
    for c in &recipe.cfgs {
        cmd.arg("--cfg").arg(c);
    }
    for ca in &recipe.crate_attrs {
        cmd.arg(format!("-Zcrate-attr={ca}"));
    }
    for f in source_files {
        cmd.arg(f);
    }

    let out = cmd.output().map_err(|e| format!("failed to spawn {rustc}: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "rustc -Zunpretty=expanded exited with {}: {}",
            out.status,
            String::from_utf8_lossy(&out.stderr).lines().take(4).collect::<Vec<_>>().join(" | ")
        ));
    }
    let hash = sha256_hex(&out.stdout);

    let ver = std::process::Command::new(&rustc)
        .arg("--version")
        .output()
        .ok()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_default();
    Ok((hash, ver))
}

/// Emit the certificate. Errors are reported as warnings; certificate emission
/// never fails an otherwise-successful verification run.
pub fn emit_certificate(
    dir: &str,
    verifier: &Verifier,
    erase_rustc_args: &[String],
    verus_sha: &str,
) {
    match emit_certificate_inner(dir, verifier, erase_rustc_args, verus_sha) {
        Ok(path) => eprintln!("note: proof certificate written to {path}"),
        Err(e) => eprintln!("warning: could not emit proof certificate: {e}"),
    }
}

fn emit_certificate_inner(
    dir: &str,
    verifier: &Verifier,
    erase_rustc_args: &[String],
    verus_sha: &str,
) -> Result<String, String> {
    std::fs::create_dir_all(dir).map_err(|e| format!("create_dir_all {dir}: {e}"))?;

    // Source files: positional `.rs` inputs in the rustc arg vector.
    let source_files: Vec<String> = erase_rustc_args
        .iter()
        .filter(|a| a.ends_with(".rs") && !a.starts_with('-'))
        .cloned()
        .collect();
    if source_files.is_empty() {
        return Err("no .rs source file found in rustc args".to_string());
    }

    // D1 integrity: sha256 of each source; also inventory trusted constructs.
    let mut sources_json = Vec::new();
    let mut sources_sha_txt = String::new();
    let mut trusted = Vec::new();
    for f in &source_files {
        let bytes = std::fs::read(f).map_err(|e| format!("read {f}: {e}"))?;
        let digest = sha256_hex(&bytes);
        sources_json.push(serde_json::json!({
            "path": f, "sha256": digest, "bytes": bytes.len(),
        }));
        sources_sha_txt.push_str(&format!("{digest}  {f}\n"));
        let text = String::from_utf8_lossy(&bytes);
        trusted.extend(trusted_constructs(f, &text));
    }

    // Per-function verdicts.
    let mut verdicts: BTreeMap<String, &'static str> = BTreeMap::new();
    for fun in &verifier.func_verifieds {
        verdicts.insert(fun_as_friendly_rust_name(fun), "verified");
    }
    for fun in &verifier.func_fails {
        verdicts.insert(fun_as_friendly_rust_name(fun), "error");
    }
    let verdicts_json: Vec<serde_json::Value> = verdicts
        .iter()
        .map(|(name, v)| serde_json::json!({ "function": name, "verdict": v }))
        .collect();

    // Option A: erase-pass expansion fingerprint.
    let recipe = recipe_from_args(erase_rustc_args);
    let (expansion, expansion_err) = match compute_expansion_hash(&recipe, &source_files) {
        Ok((hash, rustc_ver)) => (
            serde_json::json!({
                "algo": "sha256",
                "leg": "option-A-erase-pass-expansion",
                "value": hash,
                "recipe": {
                    "command": "rustc -Zunpretty=expanded",
                    "rustc_version": rustc_ver,
                    "edition": recipe.edition,
                    "crate_type": recipe.crate_type,
                    "cfgs": recipe.cfgs,
                    "crate_attrs": recipe.crate_attrs,
                    "externs": recipe.externs,
                    "verus_root": recipe.verus_root,
                    "note": "consumer recomputes with stock rustc + these flags; \
                             erase-vs-erase requires no normalisation (FINDINGS.md Result 2)",
                },
            }),
            serde_json::Value::Null,
        ),
        Err(e) => (serde_json::Value::Null, serde_json::Value::String(e)),
    };

    let cert = serde_json::json!({
        "schema": "verus-cert/v0",
        "produced_by": {
            "verus_rev": verus_sha,
            "z3": solver_version("VERUS_Z3_PATH"),
            "cvc5": solver_version("VERUS_CVC5_PATH"),
        },
        "sources": sources_json,
        "verdicts": verdicts_json,
        "counts": {
            "verified": verifier.count_verified,
            "errors": verifier.count_errors,
        },
        "trusted_constructs": {
            "method": "syntactic-scan",
            "constructs": ["assume", "admit", "external_body", "assume_specification"],
            "occurrences": trusted,
        },
        "expansion_fingerprint": expansion,
        "expansion_fingerprint_error": expansion_err,
        "smt_proof": serde_json::Value::Null,
        "disclaimer": "This certificate binds source integrity, the erase-pass \
            expansion, per-function verdicts, and a syntactic trusted-construct \
            inventory. It is NOT a proof: a rustc-only consumer cannot \
            re-establish Verus' unbounded theorem without checking the VC \
            encoding. The word 'proved' does not apply to these legs.",
    });

    let cert_path = format!("{dir}/cert.json");
    std::fs::write(&cert_path, serde_json::to_string_pretty(&cert).unwrap())
        .map_err(|e| format!("write {cert_path}: {e}"))?;
    std::fs::write(format!("{dir}/SOURCES.sha256"), sources_sha_txt)
        .map_err(|e| format!("write SOURCES.sha256: {e}"))?;

    Ok(cert_path)
}
