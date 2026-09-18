use crate::ast::{
    AssertId, AxiomInfoFilter, Command, CommandX, Commands, Constant, Expr, ExprX, QueryX, Stmt,
    StmtX,
};
use crate::messages::ArcDynMessage;
use std::sync::Arc;

/// Collect labeled assertion sites (those carrying an `AssertId`) that are nested inside at least
/// one `Switch` (i.e. guarded by a branch condition), together with their diagnostic messages.
///
/// The obligation-reachability probe only tests these branch-guarded sites. A *top-level*
/// obligation (not under any branch) is unreachable only when the whole entry context is
/// unsatisfiable, which is exactly what the precondition-satisfiability and ambient-axiom probes
/// already report; probing every top-level obligation as well would multiply the query count by a
/// large factor (prohibitive on a library the size of vstd) while only restating those two probes.
/// Branch-guarded obligations are the genuine "dead code" class (corpus V9,
/// `if false { assert(..) }`).
pub fn collect_assert_ids(stmt: &Stmt, out: &mut Vec<(AssertId, ArcDynMessage)>) {
    collect_assert_ids_rec(stmt, false, out)
}

/// Is `e` the literal boolean constant `false`? This is the asserted expression of a source-level
/// `assert(false)` (see `mk_false`) and, after simplification, of any obligation that Verus lowered
/// to a constant contradiction.
fn is_false_expr(e: &Expr) -> bool {
    matches!(&**e, ExprX::Const(Constant::Bool(false)))
}

/// Does this assertion's `AxiomInfoFilter` name a call to `vstd::pervasive::proof_from_false` or
/// `vstd::pervasive::unreached`?
///
/// The precondition of both is `false`, so their call-site obligation is `assert(req%...)` where
/// the substituted `req%...` unfolds to `false` — it is *not* the literal constant `false`, so
/// `is_false_expr` cannot see it. The filter, however, carries the callee's air-encoded path
/// (e.g. `vstd!pervasive.proof_from_false.`), which lets us recognize the call by construction.
fn filter_is_from_false(filter: &AxiomInfoFilter) -> bool {
    match filter {
        Some(id) => {
            let s: &str = id.as_str();
            s.contains("pervasive.proof_from_false") || s.contains("pervasive.unreached")
        }
        None => false,
    }
}

/// An assertion that is *definitionally* a contradiction: either an `assert(false)` or the
/// precondition check of a `proof_from_false` / `unreached` call. Such a site is the *intended*
/// contradiction that closes a proof-by-contradiction or an impossible match arm, never accidental
/// dead code, so it must not be reported by the reachability probe.
fn is_contradiction_assert(filter: &AxiomInfoFilter, e: &Expr) -> bool {
    is_false_expr(e) || filter_is_from_false(filter)
}

/// Does executing `stmt` (on every path through it) guarantee reaching a contradiction assertion?
/// Used to decide domination: an obligation followed, within the same branch, by a statement for
/// which this holds is discharged only because it flows into that contradiction, i.e. it is an
/// intermediate step of a deliberate proof-by-contradiction rather than dead code.
fn reaches_contradiction(stmt: &Stmt) -> bool {
    match &**stmt {
        StmtX::Assert(_, _, filter, e) => is_contradiction_assert(filter, e),
        StmtX::DeadEnd(s) | StmtX::Breakable(_, s) => reaches_contradiction(s),
        // A block reaches a contradiction if any of its (sequential) statements does.
        StmtX::Block(stmts) => stmts.iter().any(|s| reaches_contradiction(s)),
        // A switch reaches a contradiction only if *every* branch does.
        StmtX::Switch(stmts) => {
            !stmts.is_empty() && stmts.iter().all(|s| reaches_contradiction(s))
        }
        StmtX::Assume(..)
        | StmtX::Havoc(..)
        | StmtX::Assign(..)
        | StmtX::Snapshot(..)
        | StmtX::Break(..) => false,
    }
}

/// Collect the branch-guarded obligation sites that the reachability probe should test, filtering
/// out the two idiom classes that are *definitionally* dead (and therefore always vacuous by
/// design, not by mistake):
///
///   (1a) an obligation whose site is a `proof_from_false` / `unreached` call (recognized via its
///        `AxiomInfoFilter`), and
///   (1b) an `assert(false)` (recognized as the literal-`false` obligation), together with any
///        obligation dominated by a subsequent contradiction assertion in the same branch — those
///        are the intermediate steps of a deliberate proof-by-contradiction.
///
/// Doing this here, before any query is issued, both silences the lint noise and saves the solver
/// the corresponding reachability queries.
fn collect_assert_ids_rec(
    stmt: &Stmt,
    under_switch: bool,
    out: &mut Vec<(AssertId, ArcDynMessage)>,
) {
    match &**stmt {
        StmtX::Assert(Some(assert_id), msg, filter, e) => {
            // (1a)/(1b) self: a contradiction assertion is the intended dead end, not dead code.
            if under_switch && !is_contradiction_assert(filter, e) {
                out.push((assert_id.clone(), msg.clone()));
            }
        }
        StmtX::Assert(None, ..)
        | StmtX::Assume(..)
        | StmtX::Havoc(..)
        | StmtX::Assign(..)
        | StmtX::Snapshot(..)
        | StmtX::Break(..) => {}
        StmtX::DeadEnd(s) | StmtX::Breakable(_, s) => collect_assert_ids_rec(s, under_switch, out),
        StmtX::Block(stmts) => {
            for (i, s) in stmts.iter().enumerate() {
                // (1b) domination: if a *later* statement in this block is guaranteed to reach a
                // contradiction, every obligation in `s` flows into that contradiction and is an
                // intended intermediate step, so skip it.
                let dominated_by_later =
                    stmts[i + 1..].iter().any(|later| reaches_contradiction(later));
                if !dominated_by_later {
                    collect_assert_ids_rec(s, under_switch, out);
                }
            }
        }
        StmtX::Switch(stmts) => {
            for s in stmts.iter() {
                collect_assert_ids_rec(s, true, out);
            }
        }
    }
}

/// Build an obligation-reachability probe query assertion for a single site.
///
/// This focuses the path leading to the assertion identified by `assert_id` (dropping all
/// other assertions, later statements, and unrelated `Switch` branches, exactly as
/// `focus_stmt_on_assert_id` does) and then replaces the asserted expression at that site with
/// `false`. The resulting `CheckValid` query is *valid* exactly when the path condition reaching
/// the site is unsatisfiable together with the entry assumptions — i.e. the obligation is
/// unreachable and therefore only vacuously verified. Returns `None` if the id is not found.
pub fn reachability_probe_assertion(stmt: &Stmt, assert_id: &AssertId) -> Option<Stmt> {
    let (focused, found) = focus_stmt_on_assert_id(stmt, assert_id);
    if !found {
        return None;
    }
    Some(replace_assert_with_false(&focused, assert_id))
}

fn replace_assert_with_false(stmt: &Stmt, assert_id: &AssertId) -> Stmt {
    match &**stmt {
        StmtX::Assert(Some(id), msg, filter, _e) if id == assert_id => Arc::new(StmtX::Assert(
            Some(id.clone()),
            msg.clone(),
            filter.clone(),
            crate::ast_util::mk_false(),
        )),
        StmtX::Assert(..)
        | StmtX::Assume(..)
        | StmtX::Havoc(..)
        | StmtX::Assign(..)
        | StmtX::Snapshot(..)
        | StmtX::Break(..) => stmt.clone(),
        StmtX::DeadEnd(s) => Arc::new(StmtX::DeadEnd(replace_assert_with_false(s, assert_id))),
        StmtX::Breakable(label, s) => {
            Arc::new(StmtX::Breakable(label.clone(), replace_assert_with_false(s, assert_id)))
        }
        StmtX::Block(stmts) => Arc::new(StmtX::Block(Arc::new(
            stmts.iter().map(|s| replace_assert_with_false(s, assert_id)).collect(),
        ))),
        StmtX::Switch(stmts) => Arc::new(StmtX::Switch(Arc::new(
            stmts.iter().map(|s| replace_assert_with_false(s, assert_id)).collect(),
        ))),
    }
}

pub fn focus_commands_on_assert_id(commands: &Commands, assert_id: &AssertId) -> Commands {
    Arc::new(commands.iter().filter_map(|c| focus_command_on_assert_id(c, assert_id)).collect())
}

pub fn focus_command_on_assert_id(command: &Command, assert_id: &AssertId) -> Option<Command> {
    match &**command {
        CommandX::Push | CommandX::Pop | CommandX::SetOption(..) | CommandX::Global(..) => {
            Some(command.clone())
        }
        CommandX::CheckValid(query) => {
            let (assertion, found) = focus_stmt_on_assert_id(&query.assertion, assert_id);
            if !found {
                return None;
            }
            let query = Arc::new(QueryX { local: query.local.clone(), assertion });
            Some(Arc::new(CommandX::CheckValid(query)))
        }
        #[cfg(feature = "singular")]
        CommandX::CheckSingular(..) => {
            // TODO: what should we do here?
            None
        }
    }
}

pub fn focus_stmt_on_assert_id(stmt: &Stmt, assert_id: &AssertId) -> (Stmt, bool) {
    match &**stmt {
        StmtX::Assert(assert_id_opt, _msg, _filter, _e) => {
            if assert_id_opt == &Some(assert_id.clone()) {
                (stmt.clone(), true)
            } else {
                (Arc::new(StmtX::Block(Arc::new(vec![]))), false)
            }
        }
        StmtX::Assume(..) => (stmt.clone(), false),
        StmtX::Havoc(..) | StmtX::Assign(..) | StmtX::Snapshot(..) => (stmt.clone(), false),
        StmtX::DeadEnd(stmt) => {
            let (stmt, found) = focus_stmt_on_assert_id(stmt, assert_id);
            if found {
                (Arc::new(StmtX::DeadEnd(stmt)), true)
            } else {
                (Arc::new(StmtX::Block(Arc::new(vec![]))), false)
            }
        }
        StmtX::Breakable(ident, stmt) => {
            let (stmt, found) = focus_stmt_on_assert_id(stmt, assert_id);
            (Arc::new(StmtX::Breakable(ident.clone(), stmt)), found)
        }
        StmtX::Break(_) => (stmt.clone(), false),
        StmtX::Block(stmts) => {
            let mut v = vec![];
            for stmt in stmts.iter() {
                let (stmt, found) = focus_stmt_on_assert_id(stmt, assert_id);
                if !is_trivial(&stmt) {
                    v.push(stmt);
                }
                if found {
                    // If found in one of the cases, we just drop everything after it
                    return (Arc::new(StmtX::Block(Arc::new(v))), true);
                }
            }
            (Arc::new(StmtX::Block(Arc::new(v))), false)
        }
        StmtX::Switch(stmts) => {
            let mut v = vec![];
            for stmt in stmts.iter() {
                let (stmt, found) = focus_stmt_on_assert_id(stmt, assert_id);
                if found {
                    // If found in one of the cases, we just drop all the other cases
                    return (stmt, true);
                }
                v.push(stmt);
            }
            (Arc::new(StmtX::Switch(Arc::new(v))), false)
        }
    }
}

pub(crate) fn is_trivial(stmt: &Stmt) -> bool {
    match &**stmt {
        StmtX::Block(stmts) => stmts.len() == 0,
        _ => false,
    }
}
