//! Modeling language

use std::hash::Hash;
use std::{
    collections::{hash_map::DefaultHasher, BTreeMap},
    hash::Hasher,
};

/// System
#[derive(Debug)]
pub struct System {
    processes: Vec<Process>,
}

impl System {
    /// Convert to explicit kripke model
    pub fn to_kripke_model(&self) -> KripkeModel {
        let init = World::initial_world(self);

        let mut stack = vec![init.clone()];
        let mut visited = BTreeMap::from([(init.id(), init.clone())]);
        let mut accs = BTreeMap::new();

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

/// Boolean Expression
#[derive(Debug, Clone, Hash)]
pub enum BooleanExpression {
    True,
    False,
}

impl BooleanExpression {
    pub fn eval(&self) -> bool {
        match self {
            BooleanExpression::True => true,
            BooleanExpression::False => false,
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
            GuardStatement::When(cond) => cond.eval(),
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
    For(Vec<GuardedCase>),
}

/// LocalState
pub struct LocalState {
    statements: Vec<Statement>,
}

impl Statement {
    /// Return all possible worlds after execution
    pub fn exec(&self, cont: &[Statement]) -> Option<Vec<LocalState>> {
        match self {
            Statement::For(cases) => {
                let mut states = Vec::new();

                for case in cases {
                    if case.guard.exec() {
                        let mut stmts = case.statements.clone();
                        stmts.push(self.clone());
                        stmts.extend(cont.to_vec());

                        states.push(LocalState { statements: stmts });
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
    worlds: BTreeMap<u64, World>,
    initial_id: u64,
    accessible: BTreeMap<u64, Vec<u64>>,
}

impl KripkeModel {
    /// Convert to .dot string
    pub fn to_dot_string(&self) -> String {
        let mut s = String::from("digraph {\n");
        for id in self.worlds.keys() {
            s.push_str(&format!("\t{} [ label = \"label\" ];\n", id));
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
    program_counters: BTreeMap<&'static str, Vec<Statement>>,
}

impl World {
    /// Return the initial world of the system
    pub fn initial_world(system: &System) -> World {
        World {
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
            if let Some(nexts) = stmts[0].exec(&stmts[1..]) {
                for next in nexts {
                    let mut pcs = self.program_counters.clone();
                    pcs.insert(proc_name, next.statements.clone());
                    worlds.push(World {
                        program_counters: pcs,
                    });
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
    use {BooleanExpression::True, GuardStatement::When, Statement::For};

    let system = System {
        processes: vec![Process {
            name: "P0",
            statements: vec![For(vec![GuardedCase {
                guard: When(True),
                statements: vec![],
            }])],
        }],
    };

    let model = system.to_kripke_model();
    println!("{}", model.to_dot_string());
}
