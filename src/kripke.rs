use biodivine_lib_bdd::{Bdd, BddPartialValuation, BddVariable, BddVariableSet};
use core::iter::zip;
use std::collections::{HashMap, HashSet};

/// FIXME: BddVariableSet::new_anonymous expects a u16 argument
pub type WorldId = u64;

/// Symbolic representation of Kripke frame
pub struct SymbolicKripkeFrame {
    /// All worlds
    worlds: HashSet<WorldId>,
    /// Set of all variables
    ctx: BddVariableSet,
    /// Boolean encoding of all worlds
    enc: HashMap<WorldId, BddPartialValuation>,
    /// Transition relation
    accessible: Bdd,
    /// Set of variables introduced to represent transition relation
    aux_vars: Vec<BddVariable>,
    /// Mapping between variables and auxiliary variables
    aux_map: HashMap<BddVariable, BddVariable>,
}

impl SymbolicKripkeFrame {
    /// Create symbolic Kripke frame from explicit one
    pub fn from(worlds: HashSet<WorldId>, accs: HashMap<WorldId, HashSet<WorldId>>) -> Self {
        // Generate all possible boolean assignments
        fn all_assignments(num_vars: u16) -> Vec<Vec<bool>> {
            fn bits_to_vec_bool(bits: usize, n: u16) -> Vec<bool> {
                (0..n).map(|i| (bits & (1 << i)) != 0).collect()
            }

            (0..(1 << num_vars))
                .map(|bits| bits_to_vec_bool(bits, num_vars))
                .collect()
        }

        assert_eq!(worlds.len() % 2, 0);

        // Auxiliary variables are needed to express transition relation
        let num_vars = (worlds.len() / 2) as u16;
        let ctx = BddVariableSet::new_anonymous(num_vars * 2);
        let vars: Vec<_> = ctx
            .variables()
            .into_iter()
            .filter(|v| v.to_index() < num_vars.into())
            .collect();
        let aux_vars: Vec<_> = ctx
            .variables()
            .into_iter()
            .filter(|v| v.to_index() >= num_vars.into())
            .collect();
        let aux_map = zip(vars, aux_vars.clone()).collect();

        // Create boolean encoding of all worlds
        let mut enc = HashMap::new();
        for (id, assignment) in zip(worlds.clone(), all_assignments(num_vars)) {
            let vals: Vec<(BddVariable, bool)> = zip(ctx.variables(), assignment).collect();
            enc.insert(id, BddPartialValuation::from_values(&vals));
        }

        // Create transition relation
        let accessible = accs.iter().fold(ctx.mk_false(), |bdd, (from, tos)| {
            Bdd::or(
                &bdd,
                &tos.iter()
                    .map(|to| {
                        let prev = ctx.mk_conjunctive_clause(enc.get(from).unwrap());
                        let mut next = ctx.mk_conjunctive_clause(enc.get(to).unwrap());
                        unsafe {
                            next.rename_variables(&aux_map);
                        }
                        prev.and(&next)
                    })
                    .fold(ctx.mk_false(), |acc, bdd| acc.or(&bdd)),
            )
        });

        SymbolicKripkeFrame {
            worlds,
            ctx,
            enc,
            accessible,
            aux_vars,
            aux_map,
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
        let mut g = self.ctx.mk_true();
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
        let mut g = self.ctx.mk_false();
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
        set.iter().fold(self.ctx.mk_false(), |bdd, id| {
            bdd.or(&self.ctx.mk_conjunctive_clause(self.enc.get(id).unwrap()))
        })
    }

    /// Convert Bdd to a set of world ids
    /// Note: If bdd is constant true, then Bdd::sat_clause returns BddPartialValuation([])
    pub fn to_ids(&self, bdd: &Bdd) -> HashSet<WorldId> {
        let enc_rev: HashMap<_, _> = self.enc.clone().into_iter().map(|(k, v)| (v, k)).collect();
        if bdd.eq(&self.ctx.mk_true()) {
            self.worlds.clone()
        } else {
            bdd.sat_clauses()
                .map(|k| enc_rev.get(&k).cloned().unwrap())
                .collect()
        }
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
