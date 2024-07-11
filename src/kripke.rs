use biodivine_lib_bdd::{Bdd, BddValuation, BddVariable, BddVariableSet};
use core::iter::zip;
use std::collections::{HashMap, HashSet};

use crate::ctl::CTL;

/// FIXME: BddVariableSet::new_anonymous expects a u16 argument
pub type WorldId = u64;

/// Symbolic representation of Kripke frame
pub struct SymbolicKripkeFrame {
    /// Set of all Boolean variables
    ctx_all: BddVariableSet,
    /// Set of Boolean variables used to encode states
    ctx_vars: BddVariableSet,
    /// Set of auxiliary Boolean variables used to encode transitions
    aux_vars: Vec<BddVariable>,
    /// Mapping between variables and auxiliary variables
    aux_map: HashMap<BddVariable, BddVariable>,
    /// Boolean encoding of all worlds
    enc: HashMap<WorldId, BddValuation>,
    /// Transition relation
    accessible: Bdd,
}

impl SymbolicKripkeFrame {
    /// Create symbolic Kripke frame from explicit one
    pub fn from(worlds: HashSet<WorldId>, accs: HashMap<WorldId, HashSet<WorldId>>) -> Self {
        // Note: Need +1 for odd cases
        let num_vars = ((worlds.len() + 1) / 2) as u16;

        // Create boolean encoding of all worlds
        let ctx_vars = BddVariableSet::new_anonymous(num_vars);
        let enc: HashMap<WorldId, BddValuation> =
            zip(worlds.clone(), ctx_vars.mk_true().sat_valuations()).collect();

        // Auxiliary variables are needed to express transition relation
        let ctx_all = BddVariableSet::new_anonymous(num_vars * 2);
        let mut vars = ctx_all.variables();
        let aux_vars = vars.split_off(num_vars as usize);
        let aux_map: HashMap<BddVariable, BddVariable> = zip(vars, aux_vars.clone()).collect();

        // Create transition relation
        let accessible = accs
            .iter()
            .map(|(from, tos)| {
                tos.iter()
                    .map(|to| {
                        let prev =
                            ctx_all.mk_conjunctive_clause(&enc.get(from).cloned().unwrap().into());
                        let mut next =
                            ctx_all.mk_conjunctive_clause(&enc.get(to).cloned().unwrap().into());
                        unsafe {
                            next.rename_variables(&aux_map);
                        }
                        prev.and(&next)
                    })
                    .reduce(|lhs, rhs| lhs.or(&rhs))
                    // Note: If a deadlock exists, tos will become empty
                    .unwrap_or(ctx_all.mk_false())
            })
            .reduce(|lhs, rhs| lhs.or(&rhs))
            // Note: accs might be empty
            .unwrap_or(ctx_all.mk_false());

        SymbolicKripkeFrame {
            ctx_all,
            ctx_vars,
            aux_vars,
            aux_map,
            enc,
            accessible,
        }
    }

    /// Sat(EX(f)) = \exists v'. f(v') /\ R(v, v')
    fn bdd_check_ex(&self, f: &Bdd) -> Bdd {
        let mut f = f.clone();
        unsafe {
            f.rename_variables(&self.aux_map);
        }
        f.and(&self.accessible).exists(&self.aux_vars)
    }

    /// Sat(EG(f)) = vZ. f /\ EX(Z)
    ///
    /// The existence of the greatest fixpoint is guaranteed by the Tarski-Knaster theorem.
    /// Additionally, since the set of states is finite, termination is also ensured.
    fn bdd_check_eg(&self, f: &Bdd) -> Bdd {
        let mut g = self.ctx_all.mk_true();
        let mut h = f.and(&Self::bdd_check_ex(self, &g));
        loop {
            if g == h {
                return g;
            }
            g = h.clone();
            h = f.and(&Self::bdd_check_ex(self, &h))
        }
    }

    /// Sat(E(f1 U f2)) = uZ. f2 \/ (f1 /\ EX Z)
    ///
    /// The existence of the least fixpoint is guaranteed by the Tarski-Knaster theorem.
    /// Additionally, since the set of states is finite, termination is also ensured.
    fn bdd_check_eu(&self, f1: &Bdd, f2: &Bdd) -> Bdd {
        let mut g = self.ctx_all.mk_false();
        let mut h = f2.or(&f1.and(&Self::bdd_check_ex(self, &g)));
        loop {
            if g == h {
                return g;
            }
            g = h.clone();
            h = f2.or(&f1.and(&Self::bdd_check_ex(self, &h)));
        }
    }

    /// Sat(EF(f)) = Sat(E(true U f))
    fn bdd_check_ef(&self, f: &Bdd) -> Bdd {
        Self::bdd_check_eu(self, &self.ctx_all.mk_true(), f)
    }

    /// Sat(EG(f)) = Sat(!EF(!f))
    fn bdd_check_ag(&self, f: &Bdd) -> Bdd {
        Self::bdd_check_ef(self, &f.not()).not()
    }

    /// Convert a set of world ids to Bdd
    fn to_bdd(&self, set: &HashSet<WorldId>) -> Bdd {
        set.iter()
            .map(|id| {
                self.ctx_all
                    .mk_conjunctive_clause(&self.enc.get(id).cloned().unwrap().into())
            })
            .reduce(|lhs, rhs| lhs.or(&rhs))
            // Note: sat might be empty
            .unwrap_or(self.ctx_all.mk_false())
    }

    /// Convert Bdd to a set of world ids
    /// Note: Bdd::sat_clauses cannot be used since there is no guarantee that it is a subset of dom(enc).
    fn to_ids(&self, bdd: &Bdd) -> HashSet<WorldId> {
        let enc_rev: HashMap<_, _> = self.enc.clone().into_iter().map(|(k, v)| (v, k)).collect();
        // Assert: The resulting BDD does not include Boolean variables with '
        let bdd = self.ctx_vars.transfer_from(bdd, &self.ctx_all).unwrap();
        bdd.sat_valuations()
            .map(|k| enc_rev.get(&k).cloned().unwrap())
            .collect()
    }

    fn check_internal<P, F>(&self, f: &CTL<P>, sat: &F) -> Bdd
    where
        F: Fn(&P) -> HashSet<WorldId>,
    {
        match f {
            CTL::AP(p) => self.to_bdd(&sat(p)),
            CTL::EX(f) => self.bdd_check_ex(&self.check_internal(f, sat)),
            CTL::EG(f) => self.bdd_check_eg(&self.check_internal(f, sat)),
            CTL::EU(f1, f2) => {
                self.bdd_check_eu(&self.check_internal(f1, sat), &self.check_internal(f2, sat))
            }
            CTL::EF(f) => self.bdd_check_ef(&self.check_internal(f, sat)),
            CTL::AG(f) => self.bdd_check_ag(&self.check_internal(f, sat)),
        }
    }

    /// Verify the CTL formula f and return Sat(f)
    pub fn check<P, F>(&self, f: &CTL<P>, sat: &F) -> HashSet<WorldId>
    where
        F: Fn(&P) -> HashSet<WorldId>,
    {
        self.to_ids(&self.check_internal(f, sat))
    }
}

#[cfg(test)]
mod test {
    use super::{SymbolicKripkeFrame, WorldId};
    use crate::ctl::CTL::*;
    use std::collections::{HashMap, HashSet};

    struct P(HashSet<WorldId>);
    fn sat(p: &P) -> HashSet<WorldId> {
        p.0.clone()
    }

    #[test]
    fn test_check_ex() {
        // Consider Kripke frame (S, R) where S = {s0, s1}, R = {(s0, s1), (s1, s0)}
        let frame = SymbolicKripkeFrame::from(
            HashSet::from([0, 1]),
            HashMap::from([(0, HashSet::from([0, 1])), (1, HashSet::from([0]))]),
        );

        // P = {s1}
        let p = P(HashSet::from([1]));

        // EX(p) should be {s0}
        assert_eq!(frame.check(&EX(Box::new(AP(p))), &sat), HashSet::from([0]));
    }

    #[test]
    fn test_check_eg() {
        // Consider Kripke frame (S, R) where S = {s0, s1}, R = {(s1, s0), (s1, s1)}
        let frame = SymbolicKripkeFrame::from(
            HashSet::from([0, 1]),
            HashMap::from([(1, HashSet::from([0, 1]))]),
        );

        // P = {s1}
        let p = P(HashSet::from([1]));

        // EG(p) shuold be {s1}
        assert_eq!(frame.check(&EG(Box::new(AP(p))), &sat), HashSet::from([1]));
    }

    #[test]
    fn test_check_eu() {
        // Consider Kripke frame (S, R) where S = {s0, s1}, R = {(s0, s1), (s1, s0)}
        let frame = SymbolicKripkeFrame::from(
            HashSet::from([0, 1]),
            HashMap::from([(0, HashSet::from([1])), (1, HashSet::from([0]))]),
        );

        // P = {s0}, Q = {s1}
        let p = P(HashSet::from([0]));
        let q = P(HashSet::from([1]));

        // E(p U q) should be {s0, s1}
        assert_eq!(
            frame.check(&EU(Box::new(AP(p)), Box::new(AP(q))), &sat),
            HashSet::from([0, 1])
        );
    }

    #[test]
    fn test_check_ef() {
        // Consider Kripke frame (S, R) where S = {s0, s1}, R = {(s0, s1), (s1, s0)}
        let frame = SymbolicKripkeFrame::from(
            HashSet::from([0, 1]),
            HashMap::from([(0, HashSet::from([1])), (1, HashSet::from([0]))]),
        );

        // P = {s1}
        let p = P(HashSet::from([1]));

        // EF(p) should be {s0, s1}
        assert_eq!(
            frame.check(&EF(Box::new(AP(p))), &sat),
            HashSet::from([0, 1])
        );
    }

    #[test]
    fn test_check_ag() {
        // Consider Kripke frame (S, R) where S = {s0, s1}, R = {(s1, s0), (s1, s1)}
        let frame = SymbolicKripkeFrame::from(
            HashSet::from([0, 1]),
            HashMap::from([(1, HashSet::from([0, 1]))]),
        );

        // P = {s1}
        let p = P(HashSet::from([1]));

        // EG(p) shuold be {}
        assert_eq!(frame.check(&AG(Box::new(AP(p))), &sat), HashSet::from([]));
    }
}
