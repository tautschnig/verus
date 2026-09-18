//! `pc-audit` — check emitted records against the model invariants.
//!
//! Usage: pc-audit <record.json>...
//! Exit status 1 if any invariant is violated.

use proof_coverage::audit::{self};
use proof_coverage::record::CoverageRecord as Record;

fn load_record(path: &str) -> Result<Record, String> {
    let text = std::fs::read_to_string(path).map_err(|error| format!("cannot read: {error}"))?;
    let value: serde_json::Value =
        serde_json::from_str(&text).map_err(|error| format!("cannot parse: {error}"))?;
    audit::verify_record_id(&value)?;
    serde_json::from_value(value).map_err(|error| format!("cannot decode record: {error}"))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(|s| s.as_str()) == Some("--interchangeable") {
        let mut records = Vec::new();
        for path in &args[2..] {
            let r = load_record(path)
                .unwrap_or_else(|error| panic!("cannot audit {}: {}", path, error));
            records.push((path.clone(), r));
        }
        let (shared, violations) = proof_coverage::audit::interchangeability(&records);
        println!(
            "fingerprint groups with >1 context: {}; violations: {}",
            shared,
            violations.len()
        );
        for v in &violations {
            println!("  {}", v);
        }
        std::process::exit(if violations.is_empty() { 0 } else { 1 });
    }
    if args.get(1).map(|s| s.as_str()) == Some("--recursion") {
        let mut bad = 0;
        for path in &args[2..] {
            let r = load_record(path)
                .unwrap_or_else(|error| panic!("cannot audit {}: {}", path, error));
            println!("{}", path);
            for scc in proof_coverage::audit::observed_sccs(&r) {
                println!("  observed SCC: {:?}", scc.members);
                for (caller, callee, node, guarded) in &scc.internal_calls {
                    println!(
                        "    {} -> {} at {} [{}]",
                        caller,
                        callee,
                        node,
                        if *guarded { "guarded" } else { "UNGUARDED" }
                    );
                }
            }
            for v in proof_coverage::audit::audit_recursive_joins(&r) {
                println!("  JOIN VIOLATION: {}", v);
                bad += 1;
            }
        }
        std::process::exit(if bad == 0 { 0 } else { 1 });
    }
    if args.get(1).map(|s| s.as_str()) == Some("--rules") {
        for r in proof_coverage::rules::RULES {
            println!(
                "{}\t{:?}\t{}\t{}\t{}\t{}\t{}",
                r.id,
                r.strength,
                r.producer,
                r.signals,
                r.conclusion,
                r.constructs,
                r.negative_probes
            );
        }
        return;
    }
    if args.get(1).map(|s| s.as_str()) == Some("--families") {
        for path in &args[2..] {
            let r = load_record(path)
                .unwrap_or_else(|error| panic!("cannot audit {}: {}", path, error));
            println!("{}", path);
            print!("{}", proof_coverage::audit::families(&r));
        }
        return;
    }
    let files: Vec<String> = std::env::args().skip(1).collect();
    if files.is_empty() {
        eprintln!("usage: pc-audit <record.json>...");
        std::process::exit(2);
    }
    let mut failed = false;
    for file in &files {
        let record = match load_record(file) {
            Ok(record) => record,
            Err(error) => {
                failed = true;
                println!("{}", file);
                println!("  {:26} VIOLATION: {}", "record identity", error);
                continue;
            }
        };
        let findings = audit::audit(&record, &proof_coverage::rules::lookup);
        println!("{}", file);
        for (k, v) in &findings.stats {
            println!("  {:26} {}", k, v);
        }
        if findings.violations.is_empty() {
            println!("  {:26} all invariants hold", "audit");
        } else {
            failed = true;
            println!("  {:26} {} VIOLATIONS", "audit", findings.violations.len());
            for msg in findings.violations.iter().take(40) {
                println!("    - {}", msg);
            }
            if findings.violations.len() > 40 {
                println!("    ... {} more", findings.violations.len() - 40);
            }
        }
    }
    if failed {
        std::process::exit(1);
    }
}
