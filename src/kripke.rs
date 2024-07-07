use biodivine_lib_bdd::{Bdd, BddValuation, BddVariable, BddVariableSet};
use core::iter::zip;
use std::collections::{HashMap, HashSet};

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
                    .unwrap()
            })
            .reduce(|lhs, rhs| lhs.or(&rhs))
            .unwrap();

        SymbolicKripkeFrame {
            ctx_all,
            ctx_vars,
            aux_vars,
            aux_map,
            enc,
            accessible,
        }
    }

    /// EX(f) = \exists v'. f(v') /\ R(v, v')
    pub fn bdd_check_ex(&self, f: &Bdd) -> Bdd {
        let mut f = f.clone();
        unsafe {
            f.rename_variables(&self.aux_map);
        }
        f.and(&self.accessible).exists(&self.aux_vars)
    }

    /// EG(f) = vZ. f /\ EX(Z)
    ///
    /// The existence of the greatest fixpoint is guaranteed by the Tarski-Knaster theorem.
    /// Additionally, since the set of states is finite, termination is also ensured.
    pub fn bdd_check_eg(&self, f: &Bdd) -> Bdd {
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

    /// E(f1 U f2) = uZ. f2 \/ (f1 /\ EX Z)
    ///
    /// The existence of the least fixpoint is guaranteed by the Tarski-Knaster theorem.
    /// Additionally, since the set of states is finite, termination is also ensured.
    pub fn bdd_check_eu(&self, f1: &Bdd, f2: &Bdd) -> Bdd {
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

    /// Convert a set of world ids to Bdd
    pub fn to_bdd(&self, set: &HashSet<WorldId>) -> Bdd {
        set.iter()
            .map(|id| {
                self.ctx_all
                    .mk_conjunctive_clause(&self.enc.get(id).cloned().unwrap().into())
            })
            .reduce(|lhs, rhs| lhs.or(&rhs))
            .unwrap()
    }

    /// Convert Bdd to a set of world ids
    /// Note: Bdd::sat_clauses cannot be used since there is no guarantee that it is a subset of dom(enc).
    pub fn to_ids(&self, bdd: &Bdd) -> HashSet<WorldId> {
        let enc_rev: HashMap<_, _> = self.enc.clone().into_iter().map(|(k, v)| (v, k)).collect();
        // Assert: The resulting BDD does not include Boolean variables with '
        let bdd = self.ctx_vars.transfer_from(bdd, &self.ctx_all).unwrap();
        bdd.sat_valuations()
            .map(|k| enc_rev.get(&k).cloned().unwrap())
            .collect()
    }
}

#[cfg(test)]
mod test {
    use super::{SymbolicKripkeFrame, WorldId};
    use crate::ctl::CTL::{self, *};
    use biodivine_lib_bdd::Bdd;
    use std::collections::{HashMap, HashSet};

    struct P(HashSet<WorldId>);
    struct KripkeModel {
        frame: SymbolicKripkeFrame,
    }

    impl KripkeModel {
        fn new(worlds: HashSet<WorldId>, accs: HashMap<WorldId, HashSet<WorldId>>) -> KripkeModel {
            KripkeModel {
                frame: SymbolicKripkeFrame::from(worlds, accs),
            }
        }

        pub fn check_internal(&self, f: &CTL<P>) -> Bdd {
            match f {
                CTL::AP(p) => self.frame.to_bdd(&p.0),
                CTL::EX(f) => self.frame.bdd_check_ex(&Self::check_internal(self, f)),
                CTL::EG(f) => self.frame.bdd_check_eg(&Self::check_internal(self, f)),
                CTL::EU(f1, f2) => self.frame.bdd_check_eu(
                    &Self::check_internal(self, f1),
                    &Self::check_internal(self, f2),
                ),
                _ => unimplemented!(),
            }
        }

        pub fn check(&self, f: &CTL<P>) -> HashSet<WorldId> {
            self.frame.to_ids(&Self::check_internal(self, f))
        }
    }

    #[test]
    fn test_check_ex() {
        // Consider Kripke model (S, R) where S = {s0, s1}, R = {(s0, s1), (s1, s0)}
        let frame = KripkeModel::new(
            HashSet::from([0, 1]),
            HashMap::from([(0, HashSet::from([0, 1])), (1, HashSet::from([0]))]),
        );

        // P = {s1}
        let p = P(HashSet::from([1]));

        // EX(p) should be {s0}
        assert_eq!(frame.check(&EX(Box::new(AP(p)))), HashSet::from([0]));
    }

    #[test]
    fn test_check_eg() {
        // Consider Kripke model (S, R) where S = {s0, s1}, R = {(s0, s1), (s1, s1)}
        let frame = KripkeModel::new(
            HashSet::from([0, 1]),
            HashMap::from([(0, HashSet::from([1])), (1, HashSet::from([1]))]),
        );

        // P = {s1}
        let p = P(HashSet::from([1]));

        // EG(p) shuold be {s1}
        assert_eq!(frame.check(&EG(Box::new(AP(p)))), HashSet::from([1]));
    }

    #[test]
    fn test_check_eu() {
        // Consider Kripke model (S, R) where S = {s0, s1}, R = {(s0, s1), (s1, s0)}
        let model = KripkeModel::new(
            HashSet::from([0, 1]),
            HashMap::from([(0, HashSet::from([1])), (1, HashSet::from([0]))]),
        );

        // P = {s0}, Q = {s1}
        let p = P(HashSet::from([0]));
        let q = P(HashSet::from([1]));

        // E(p U q) should be {s0, s1}
        assert_eq!(
            model.check(&EU(Box::new(AP(p)), Box::new(AP(q)))),
            HashSet::from([0, 1])
        );
    }
}
