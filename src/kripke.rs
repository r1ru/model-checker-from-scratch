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
    EU(Box<CTL>),
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
    /// Intermediate procedures to verify CTL formulas
    fn bdd_check_ex(&self, f: &Bdd) -> Bdd {
        let mut f = f.clone();
        unsafe {
            f.rename_variables(&self.auxiliary_map);
        }
        f.and(&self.transition_relation)
            .exists(&self.auxiliary_variables)
    }

    /// Verify CTL formula
    pub fn check(&self, f: &CTL) -> Bdd {
        match f {
            CTL::AP(p) => self.atomic_propositions.get(p).cloned().unwrap(),
            CTL::EX(f) => Self::bdd_check_ex(self, &Self::check(self, f)),
            _ => unimplemented!(),
        }
    }
}

#[test]
fn test() {
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
