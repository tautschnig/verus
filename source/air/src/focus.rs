use crate::ast::{AssertId, Command, CommandX, Commands, QueryX, Stmt, StmtX};
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

fn collect_assert_ids_rec(
    stmt: &Stmt,
    under_switch: bool,
    out: &mut Vec<(AssertId, ArcDynMessage)>,
) {
    match &**stmt {
        StmtX::Assert(Some(assert_id), msg, _filter, _e) => {
            if under_switch {
                out.push((assert_id.clone(), msg.clone()));
            }
        }
        StmtX::Assert(None, ..)
        | StmtX::Assume(..)
        | StmtX::Havoc(..)
        | StmtX::Assign(..)
        | StmtX::Snapshot(..)
        | StmtX::Break(..) => {}
        StmtX::DeadEnd(s) | StmtX::Breakable(_, s) => {
            collect_assert_ids_rec(s, under_switch, out)
        }
        StmtX::Block(stmts) => {
            for s in stmts.iter() {
                collect_assert_ids_rec(s, under_switch, out);
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
        StmtX::DeadEnd(s) => {
            Arc::new(StmtX::DeadEnd(replace_assert_with_false(s, assert_id)))
        }
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
