use biodivine_lib_bdd::{Bdd, BddVariable, BddVariableSet};
use std::collections::HashMap;

/// CTL formulas
#[derive(Clone)]
pub enum CTL {
    AP(&'static str),
    Not(Box<CTL>),
    Or(Box<CTL>, Box<CTL>),
    EX(Box<CTL>),
    EG(Box<CTL>),
    EU(Box<CTL>, Box<CTL>),
}

/// Symbolic representation of KripkeModel
pub struct KripkeModel {
    /// Set of all variables
    variables: BddVariableSet,
    /// Set of variables introduced to represent state transitions
    auxiliary_variables: Vec<BddVariable>,
    /// Mapping between variables and auxiliary variables
    auxiliary_map: HashMap<BddVariable, BddVariable>,
    /// Initial state
    initial_state: Bdd,
    /// Transition relation
    transition_relation: Bdd,
    /// Set of all atomic propositions
    atomic_propositions: HashMap<&'static str, Bdd>,
}

impl KripkeModel {
    /// EX(f) = \exists v'. f(v') /\ R(v, v')
    fn bdd_check_ex(&self, f: &Bdd) -> Bdd {
        let mut f = f.clone();
        unsafe {
            f.rename_variables(&self.auxiliary_map);
        }
        f.and(&self.transition_relation)
            .exists(&self.auxiliary_variables)
    }

    /// EG(f) = vZ. f /\ EX(Z)
    ///
    /// The existence of the greatest fixpoint is guaranteed by the Tarski-Knaster theorem.
    /// Additionally, since the set of states is finite, termination is also ensured.
    fn bdd_check_eg(&self, f: &Bdd) -> Bdd {
        let mut g = self.variables.mk_true();
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
    fn bdd_check_eu(&self, f1: &Bdd, f2: &Bdd) -> Bdd {
        let mut g = self.variables.mk_false();
        let mut h = f2.or(&f1.and(&Self::bdd_check_ex(self, &g)));

        loop {
            if g == h {
                return g;
            }
            g = h.clone();
            h = f2.or(&f1.and(&Self::bdd_check_ex(self, &h)));
        }
    }

    /// Verify CTL formula
    pub fn check(&self, f: &CTL) -> Bdd {
        match f {
            CTL::AP(p) => self.atomic_propositions.get(p).cloned().unwrap(),
            CTL::EX(f) => Self::bdd_check_ex(self, &Self::check(self, f)),
            CTL::EG(f) => Self::bdd_check_eg(self, &Self::check(self, f)),
            CTL::EU(f1, f2) => {
                Self::bdd_check_eu(self, &Self::check(self, f1), &Self::check(self, f2))
            }
            _ => unimplemented!(),
        }
    }
}

#[test]
fn test_check_ex() {
    use CTL::{AP, EX};

    // Consider Kripke structure (S, I, R, P) where S = {s0, s1}, I = {s0}, R = {(s0, s0), (s0, s1), (s1, s0)}, P = {s1}
    let states = BddVariableSet::new(&["x", "x'"]);
    let initial_state = states.eval_expression_string("!x");
    let transition_relation = states.eval_expression_string("!x | !x'");
    let p = states.eval_expression_string("x");

    let model = KripkeModel {
        variables: states.clone(),
        auxiliary_variables: vec![BddVariable::from_index(1)],
        auxiliary_map: HashMap::from([(BddVariable::from_index(0), BddVariable::from_index(1))]),
        initial_state,
        transition_relation,
        atomic_propositions: HashMap::from([("p", p)]),
    };

    // Verify CTL formula EX(p)
    let result = model.check(&EX(Box::new(AP("p"))));

    // EX(p) should be {s0}
    assert_eq!(result, states.eval_expression_string("!x"));
}

#[test]
fn test_check_eg() {
    use CTL::{AP, EG};

    // Consider Kripke structure (S, I, R, P) where S = {s0, s1}, I = {s0}, R = {(s0, s1), (s1, s0), (s1, s1)}, P = {s1}
    let vars = BddVariableSet::new(&["x", "x'"]);
    let initial_state = vars.eval_expression_string("!x");
    let transition_relation = vars.eval_expression_string("x | x'");
    let p = vars.eval_expression_string("x");

    let model = KripkeModel {
        variables: vars.clone(),
        auxiliary_variables: vec![BddVariable::from_index(1)],
        auxiliary_map: HashMap::from([(BddVariable::from_index(0), BddVariable::from_index(1))]),
        initial_state,
        transition_relation,
        atomic_propositions: HashMap::from([("p", p)]),
    };

    // Verify CTL formula EG(p)
    let result = model.check(&EG(Box::new(AP("p"))));

    // EG(p) shuold be {s0, s1}
    assert_eq!(result, vars.eval_expression_string("x"));
}

#[test]
fn test_check_eu() {
    use CTL::{AP, EU};

    // Consider Kripke structure (S, I, R, P) where S = {s0, s1}, I = {s0}, R = {(s0, s1), (s1, s0)}, P = {s0}, Q = {s1}
    let vars = BddVariableSet::new(&["x", "x'"]);
    let initial_state = vars.eval_expression_string("!x");
    let transition_relation = vars.eval_expression_string("(!x & x') | (x & !x')");
    let p = vars.eval_expression_string("!x");
    let q = vars.eval_expression_string("x");

    let model = KripkeModel {
        variables: vars.clone(),
        auxiliary_variables: vec![BddVariable::from_index(1)],
        auxiliary_map: HashMap::from([(BddVariable::from_index(0), BddVariable::from_index(1))]),
        initial_state,
        transition_relation,
        atomic_propositions: HashMap::from([("p", p), ("q", q)]),
    };

    // Verify CTL formula E(p U q)
    let result = model.check(&EU(Box::new(AP("p")), Box::new(AP("q"))));

    // E(p U q) should be {s0, s1}
    assert_eq!(result, vars.mk_true());
}
