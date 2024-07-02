//! Modeling language

use std::hash::Hash;
use std::{
    collections::{hash_map::DefaultHasher, BTreeMap, HashMap},
    hash::Hasher,
};

/// System
#[derive(Debug)]
pub struct System {
    processes: Vec<Process>,
    variables: Variables,
}

impl System {
    /// Convert to explicit kripke model
    pub fn to_kripke_model(&self) -> KripkeModel {
        let init = World::initial_world(self);

        let mut stack = vec![init.clone()];
        let mut visited = HashMap::from([(init.id(), init.clone())]);
        let mut accs = HashMap::new();

        while let Some(current) = stack.pop() {
            let mut acc = Vec::new();
            if let Some(nexts) = current.step_global() {
                for next in nexts {
                    acc.push(next.id());

                    if visited.insert(next.id(), next.clone()).is_none() {
                        stack.push(next);
                    }
                }
            }
            accs.insert(current.id(), acc);
        }

        KripkeModel {
            worlds: visited,
            initial_id: init.id(),
            accessible: accs,
        }
    }
}

/// Process
#[derive(Debug)]
pub struct Process {
    name: &'static str,
    statements: Vec<Statement>,
}

/// Variables (All variables are global and shared)
type Variables = BTreeMap<&'static str, i64>;

/// Integer Expression
#[derive(Debug, Clone, Hash)]
pub enum IntegerExpression {
    Int(i64),
}

impl IntegerExpression {
    pub fn eval(&self) -> i64 {
        match self {
            Self::Int(v) => *v,
        }
    }
}

/// Boolean Expression
#[derive(Debug, Clone, Hash)]
pub enum BooleanExpression {
    True,
    False,
}

impl BooleanExpression {
    pub fn eval(&self) -> bool {
        match self {
            Self::True => true,
            Self::False => false,
        }
    }
}

/// GuardStatement
#[derive(Debug, Clone, Hash)]
pub enum GuardStatement {
    When(BooleanExpression),
}

impl GuardStatement {
    pub fn exec(&self) -> bool {
        match self {
            Self::When(cond) => cond.eval(),
        }
    }
}

/// GuardedCase
#[derive(Debug, Clone, Hash)]
pub struct GuardedCase {
    guard: GuardStatement,
    statements: Vec<Statement>,
}

/// Statement
#[derive(Debug, Clone, Hash)]
pub enum Statement {
    Assign(&'static str, IntegerExpression),
    For(Vec<GuardedCase>),
}

/// Environment
#[derive(Debug, Clone, Hash)]
pub struct Environment {
    variables: Variables,
}

impl Environment {
    /// Set the value panic if not exist
    pub fn var_set(&mut self, name: &'static str, val: i64) {
        if self.variables.insert(name, val).is_none() {
            panic!("variable does not exists: {}", name);
        }
    }

    /// Get the value panic if not exist
    pub fn var_get(&self, name: &str) -> i64 {
        self.variables
            .get(name)
            .cloned()
            .unwrap_or_else(|| panic!("variable does not exists: {}", name))
    }
}

#[test]
fn test_environment_should_success() {
    let mut env = Environment {
        variables: Variables::from([("x", 0)]),
    };
    assert_eq!(env.var_get("x"), 0);
    env.var_set("x", 1);
    assert_eq!(env.var_get("x"), 1);
}

#[test]
#[should_panic(expected = "variable does not exists: y")]
fn test_environment_var_get_should_fail() {
    let env = Environment {
        variables: Variables::from([("x", 0)]),
    };
    env.var_get("y");
}

#[test]
#[should_panic(expected = "variable does not exists: y")]
fn test_environment_var_set_should_fail() {
    let mut env = Environment {
        variables: Variables::from([("x", 0)]),
    };
    env.var_set("y", 1);
}

/// LocalState
pub struct LocalState {
    environment: Environment,
    statements: Vec<Statement>,
}

impl Statement {
    /// Return all possible worlds after execution
    pub fn exec(&self, env: &Environment, cont: &[Statement]) -> Option<Vec<LocalState>> {
        match self {
            Self::Assign(var_name, expr) => {
                // Create new environment
                let mut new_env = env.clone();
                new_env.var_set(var_name, expr.eval());
                Some(vec![LocalState {
                    environment: new_env,
                    statements: cont.to_vec(),
                }])
            }
            Self::For(cases) => {
                let mut states = Vec::new();

                for case in cases {
                    if case.guard.exec() {
                        let mut stmts = case.statements.clone();
                        stmts.push(self.clone());
                        stmts.extend(cont.to_vec());

                        states.push(LocalState {
                            environment: env.clone(),
                            statements: stmts,
                        });
                    }
                }

                if states.is_empty() {
                    None
                } else {
                    Some(states)
                }
            }
        }
    }
}

/// Explicit kripke model
#[derive(Debug)]
pub struct KripkeModel {
    worlds: HashMap<u64, World>,
    initial_id: u64,
    accessible: HashMap<u64, Vec<u64>>,
}

impl KripkeModel {
    /// Convert to .dot string
    pub fn to_dot_string(&self) -> String {
        let mut s = String::from("digraph {\n");
        for (id, world) in &self.worlds {
            s.push_str(&format!("\t{} [ label = \"{}\" ];\n", id, world.label()));
            if *id == self.initial_id {
                s.push_str(&format!("\t{} [ penwidth = 5 ];\n", id));
            }
        }

        for (from, tos) in &self.accessible {
            for to in tos {
                s.push_str(&format!("\t{} -> {};\n", from, to));
            }
        }

        s.push('}');
        s
    }
}

/// World
#[derive(Debug, Clone, Hash)]
pub struct World {
    environment: Environment,
    /// Use BTreeMap to implement Hash trait
    program_counters: BTreeMap<&'static str, Vec<Statement>>,
}

impl World {
    /// Create a new world
    pub fn new(env: Environment, pcs: BTreeMap<&'static str, Vec<Statement>>) -> World {
        World {
            environment: env,
            program_counters: pcs,
        }
    }

    // Return the label of the world
    pub fn label(&self) -> String {
        let mut label = String::new();
        for (var_name, val) in &self.environment.variables {
            label.push_str(&format!("{}={}\n", var_name, val))
        }
        label
    }

    /// Return the initial world of the system
    pub fn initial_world(system: &System) -> World {
        World {
            environment: Environment {
                variables: system.variables.clone(),
            },
            program_counters: system
                .processes
                .iter()
                .map(|p| (p.name, p.statements.clone()))
                .collect(),
        }
    }

    /// Return the unique id of the world
    pub fn id(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }

    /// Return all possible worlds that can be transitioned to in one step
    pub fn step_global(&self) -> Option<Vec<World>> {
        let mut worlds = Vec::new();

        for (proc_name, stmts) in &self.program_counters {
            if let Some(nexts) = stmts[0].exec(&self.environment, &stmts[1..]) {
                for next in nexts {
                    let mut pcs = self.program_counters.clone();
                    pcs.insert(proc_name, next.statements.clone());
                    worlds.push(World::new(next.environment, pcs));
                }
            }
        }

        if !worlds.is_empty() {
            Some(worlds)
        } else {
            None
        }
    }
}

#[test]
fn test() {
    use {
        BooleanExpression::True,
        GuardStatement::When,
        IntegerExpression::Int,
        Statement::{Assign, For},
    };

    let system = System {
        variables: Variables::from([("x", 0)]),
        processes: vec![Process {
            name: "P0",
            statements: vec![For(vec![GuardedCase {
                guard: When(True),
                statements: vec![Assign("x", Int(1))],
            }])],
        }],
    };

    let model = system.to_kripke_model();
    println!("{}", model.to_dot_string());
}
