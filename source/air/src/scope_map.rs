use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::ops::Index;
#[cfg(verus_only)]
use vstd::prelude::*;

// Verus specifications (attribute syntax, active only when Verus verifies a client such as
// vir's interpreter): the bodies are trusted (`external_body`); the contracts state the scope
// structure the clients rely on.

#[derive(Debug)]
struct Scope<K, V> {
    undo_map: HashMap<K, (Option<V>, usize)>,
    allow_shadowing: bool,
    count: usize,
}

#[derive(Debug)]
#[cfg_attr(verus_only, verus_verify(external_body))]
#[cfg_attr(verus_only, verifier::reject_recursive_types(K))]
#[cfg_attr(verus_only, verifier::reject_recursive_types(V))]
pub struct ScopeMap<K, V> {
    map: HashMap<K, V>,
    cannot_shadow: HashSet<K>,
    scopes: Vec<Scope<K, V>>,
}

#[cfg(verus_only)]
verus! {
impl<K: Eq + Hash + Clone, V> ScopeMap<K, V> {
    /// The keys inserted into each scope, innermost last (`scopes[i].undo_map`'s keys)
    pub uninterp spec fn scope_keys(&self) -> Seq<Set<K>>;

    /// Every scope allows shadowing (then `cannot_shadow` is empty)
    pub uninterp spec fn all_shadowing(&self) -> bool;

    /// The current bindings (`map`)
    pub uninterp spec fn view(&self) -> Map<K, V>;

    /// For each open scope, the bindings when it was pushed, innermost last: popping a scope
    /// restores them, provided every binding made since went into that scope by `insert` (the
    /// only kind of change specified here; `insert` that fails leaves this unspecified, since
    /// the undo map may then be overwritten)
    pub uninterp spec fn saved_views(&self) -> Seq<Map<K, V>>;
}

/// One saved view per scope (both are `scopes`)
pub broadcast axiom fn axiom_saved_views_len<K: Eq + Hash + Clone, V>(m: &ScopeMap<K, V>)
    ensures #[trigger] m.saved_views().len() == m.scope_keys().len();
} // verus!

#[cfg_attr(verus_only, verus_verify)]
impl<K: Eq + Hash + Clone, V> ScopeMap<K, V> {
    #[cfg_attr(verus_only, verus_verify(external_body))]
    #[cfg_attr(verus_only, verus_spec(r =>
        ensures r.scope_keys() == Seq::<Set<K>>::empty(), r.all_shadowing(),
            r.view() == Map::<K, V>::empty(),
    ))]
    pub fn new() -> Self {
        ScopeMap { map: HashMap::new(), cannot_shadow: HashSet::new(), scopes: Vec::new() }
    }

    #[cfg_attr(verus_only, verus_verify(external_body))]
    #[cfg_attr(verus_only, verus_spec(
        ensures
            final(self).scope_keys() == old(self).scope_keys().push(Set::<K>::empty()),
            final(self).all_shadowing() == (old(self).all_shadowing() && allow_shadowing),
            final(self).view() == old(self).view(),
            final(self).saved_views() == old(self).saved_views().push(old(self).view()),
    ))]
    pub fn push_scope(&mut self, allow_shadowing: bool) {
        let scope = Scope { undo_map: HashMap::new(), allow_shadowing, count: 0 };
        self.scopes.push(scope);
    }

    /// panics on an empty stack
    #[cfg_attr(verus_only, verus_verify(external_body))]
    #[cfg_attr(verus_only, verus_spec(
        requires old(self).scope_keys().len() > 0,
        ensures
            final(self).scope_keys() == old(self).scope_keys().drop_last(),
            old(self).all_shadowing() ==> final(self).all_shadowing(),
            final(self).view() == old(self).saved_views().last(),
            final(self).saved_views() == old(self).saved_views().drop_last(),
    ))]
    pub fn pop_scope(&mut self) {
        let scope = self.scopes.pop().expect("internal error: popped empty stack from ScopeMap");
        for (key, (value, _)) in scope.undo_map {
            self.map.remove(&key);
            if !scope.allow_shadowing {
                self.cannot_shadow.remove(&key);
            }
            if let Some(value) = value {
                self.map.insert(key, value);
            }
        }
    }

    #[cfg_attr(verus_only, verus_verify(external_body))]
    pub fn num_scopes(&self) -> usize {
        self.scopes.len()
    }

    #[cfg_attr(verus_only, verus_verify(external_body))]
    pub fn contains_key(&self, key: &K) -> bool {
        self.map.contains_key(key)
    }

    // Which scope, and which index within the scope
    #[cfg_attr(verus_only, verus_verify(external_body))]
    pub fn scope_and_index_of_key(&self, key: &K) -> Option<(usize, usize)> {
        for i in (0..self.scopes.len()).rev() {
            if let Some((_, k)) = self.scopes[i].undo_map.get(key) {
                return Some((i, *k));
            }
        }
        None
    }

    #[cfg_attr(verus_only, verus_verify(external_body))]
    #[cfg_attr(verus_only, verus_spec(r =>
        ensures
            r matches Some(v) ==> self.view().contains_key(*key) && *v == self.view()[*key],
            r is None ==> !self.view().contains_key(*key),
    ))]
    pub fn get(&self, key: &K) -> Option<&V> {
        self.map.get(key)
    }

    #[cfg_attr(verus_only, verus_verify(external_body))]
    pub fn insert_at(&mut self, scope_index: usize, key: K, value: V) -> Result<(), ()> {
        if self.cannot_shadow.contains(&key) {
            return Err(());
        }
        let scope = &mut self.scopes[scope_index];
        let prev = self.map.insert(key.clone(), value);
        if !scope.allow_shadowing {
            self.cannot_shadow.insert(key.clone());
        }
        let undo_prev = scope.undo_map.insert(key, (prev, scope.count));
        scope.count += 1;
        if undo_prev.is_none() { Ok(()) } else { Err(()) }
    }

    /// panics without a scope; fails if `key` is already in the innermost scope, or (only when
    /// some scope disallows shadowing) shadows a key of such a scope
    #[cfg_attr(verus_only, verus_verify(external_body))]
    #[cfg_attr(verus_only, verus_spec(r =>
        requires old(self).scope_keys().len() > 0,
        ensures
            final(self).scope_keys() == old(self).scope_keys().update(
                old(self).scope_keys().len() - 1, old(self).scope_keys().last().insert(key)),
            final(self).all_shadowing() == old(self).all_shadowing(),
            old(self).all_shadowing() && !old(self).scope_keys().last().contains(key) ==> r is Ok,
            r is Ok ==> final(self).view() == old(self).view().insert(key, value),
            r is Ok ==> final(self).saved_views() == old(self).saved_views(),
    ))]
    pub fn insert(&mut self, key: K, value: V) -> Result<(), ()> {
        if self.scopes.len() == 0 {
            panic!("internal error: must push at least one scope in ScopeMap")
        } else {
            self.insert_at(self.scopes.len() - 1, key, value)
        }
    }

    #[cfg_attr(verus_only, verus_verify(external_body))]
    pub fn replace(&mut self, key: K, value: V) -> Result<(), ()> {
        if self.contains_key(&key) {
            self.map.insert(key, value).expect("replace");
            Ok(())
        } else {
            Err(())
        }
    }

    #[cfg_attr(verus_only, verus_verify(external_body))]
    pub fn map(&self) -> &HashMap<K, V> {
        &self.map
    }
}

impl<K: Eq + Hash + Clone, V> Index<&K> for ScopeMap<K, V> {
    type Output = V;
    fn index(&self, key: &K) -> &V {
        &self.map[key]
    }
}

/// Evidence for the specifications above (`view`, `saved_views`): every sequence of up to 7
/// operations over 3 keys, checked against the model they state. `get` is the current view;
/// `push_scope` saves it; a successful `insert` updates it; `pop_scope` restores the saved view
/// (after successful inserts only, as specified).
#[cfg(test)]
mod spec_tests {
    use super::ScopeMap;
    use std::collections::HashMap;

    #[derive(Clone, Copy, Debug)]
    enum Op {
        Push,
        Pop,
        Insert(u8, u8),
    }

    fn check(ops: &[Op]) {
        let mut m: ScopeMap<u8, u8> = ScopeMap::new();
        let mut view: HashMap<u8, u8> = HashMap::new();
        let mut saved: Vec<HashMap<u8, u8>> = Vec::new();
        for op in ops {
            match *op {
                Op::Push => {
                    m.push_scope(true);
                    saved.push(view.clone());
                }
                Op::Pop => {
                    if saved.is_empty() {
                        continue; // precondition
                    }
                    m.pop_scope();
                    view = saved.pop().unwrap();
                }
                Op::Insert(k, v) => {
                    if saved.is_empty() {
                        continue; // precondition
                    }
                    if m.insert(k, v).is_err() {
                        return; // unspecified from here on
                    }
                    view.insert(k, v);
                }
            }
            for k in 0..3u8 {
                assert_eq!(m.get(&k).copied(), view.get(&k).copied(), "{ops:?} key {k}");
            }
            assert_eq!(m.num_scopes(), saved.len(), "{ops:?}");
        }
    }

    #[test]
    fn scope_map_follows_its_specification() {
        let mut alphabet = vec![Op::Push, Op::Pop];
        for k in 0..3u8 {
            for v in 0..2u8 {
                alphabet.push(Op::Insert(k, v));
            }
        }
        let mut seqs: Vec<Vec<Op>> = vec![vec![]];
        let mut n = 0usize;
        for _ in 0..7 {
            let mut next = Vec::new();
            for s in &seqs {
                for op in &alphabet {
                    let mut t = s.clone();
                    t.push(*op);
                    check(&t);
                    n += 1;
                    next.push(t);
                }
            }
            seqs = next;
        }
        assert_eq!(n, (1..=7).map(|i| 8usize.pow(i)).sum::<usize>()); // 2,396,744 sequences
    }
}
