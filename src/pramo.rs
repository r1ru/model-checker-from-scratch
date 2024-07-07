use crate::ctl::CTL;
use crate::kripke::{SymbolicKripkeFrame, WorldId};
use std::collections::HashSet;
use std::hash::Hash;
use std::{
    collections::{hash_map::DefaultHasher, BTreeMap, HashMap},
    hash::Hasher,
};

/// Kripke model
pub struct KripkeModel {
    worlds: HashMap<WorldId, World>,
    accs: HashMap<WorldId, HashSet<WorldId>>,
    frame: SymbolicKripkeFrame,
}

impl KripkeModel {
    /// Verify a CTL formula and return counterexamples
    pub fn check(&self, f: &CTL<BooleanExpression>) -> HashSet<WorldId> {
        let sat = |p: &BooleanExpression| -> HashSet<WorldId> {
            self.worlds
                .iter()
                .filter_map(|(id, w)| if w.eval(p) { Some(*id) } else { None })
                .collect()
        };

        let sat = self.frame.check(f, &sat);

        self.worlds
            .keys()
            .filter_map(|id| if !sat.contains(id) { Some(*id) } else { None })
            .collect()
    }

    /// Convert to .dot string
    pub fn to_dot_string(&self, unsat: &HashSet<WorldId>) -> String {
        let mut s = String::from("digraph {\n");
        for (id, wld) in &self.worlds {
            s.push_str(&format!("\t{} [ label = \"{}\" ];\n", id, wld.label()));
        }
        for (from, tos) in &self.accs {
            for to in tos {
                s.push_str(&format!("\t{} -> {};\n", from, to));
            }
        }
        for id in unsat {
            s.push_str(&format!(
                "\t{} [ style=\"filled\", fillcolor=\"lightcoral\" ];\n",
                id
            ));
        }
        s.push('}');
        s
    }
}

/// System
pub struct System {
    variables: Variables,
    processes: Vec<Process>,
}

impl System {
    // Crate new system
    pub fn new(variables: Variables, processes: Vec<Process>) -> System {
        System {
            processes,
            variables,
        }
    }

    /// Convert to symbolic kripke model
    pub fn to_kripke_model(&self) -> KripkeModel {
        let init = World::initial_world(self);

        let mut stack = vec![init.clone()];
        let mut visited = HashMap::from([(init.id(), init.clone())]);
        let mut accs = HashMap::new();

        while let Some(current) = stack.pop() {
            let mut acc = HashSet::new();
            for next in current.step_global() {
                acc.insert(next.id());

                if visited.insert(next.id(), next.clone()).is_none() {
                    stack.push(next);
                }
            }
            accs.insert(current.id(), acc);
        }

        KripkeModel {
            worlds: visited.clone(),
            accs: accs.clone(),
            frame: SymbolicKripkeFrame::from(visited.keys().cloned().collect(), accs),
        }
    }
}

/// Process
pub struct Process {
    name: &'static str,
    statements: Vec<Statement>,
}

impl Process {
    /// Create new process
    pub fn new(name: &'static str, statements: Vec<Statement>) -> Process {
        Process { name, statements }
    }
}

/// Variables (All variables are global and shared)
pub type Variables = BTreeMap<&'static str, i64>;

/// Environment
#[derive(Clone, Hash)]
struct Environment {
    variables: Variables,
}

impl Environment {
    /// Set the value panic if not exist
    fn var_set(&mut self, name: &'static str, val: i64) {
        if self.variables.insert(name, val).is_none() {
            panic!("variable does not exists: {}", name);
        }
    }

    /// Get the value panic if not exist
    fn var_get(&self, name: &str) -> i64 {
        self.variables
            .get(name)
            .cloned()
            .unwrap_or_else(|| panic!("variable does not exists: {}", name))
    }
}

/// LocalState
struct LocalState {
    environment: Environment,
    statements: Vec<Statement>,
}

/// Integer Expression
#[derive(Clone, Hash)]
pub enum IntegerExpression {
    Int(i64),
    Var(&'static str),
    Add(Box<IntegerExpression>, Box<IntegerExpression>),
    Sub(Box<IntegerExpression>, Box<IntegerExpression>),
}

impl IntegerExpression {
    fn eval(&self, env: &Environment) -> i64 {
        match self {
            Self::Int(v) => *v,
            Self::Var(name) => env.var_get(name),
            Self::Add(lhs, rhs) => lhs.eval(env) + rhs.eval(env),
            Self::Sub(lhs, rhs) => lhs.eval(env) - rhs.eval(env),
        }
    }
}

/// Boolean Expression
#[derive(Clone, Hash)]
pub enum BooleanExpression {
    True,
    False,
    Lt(Box<IntegerExpression>, Box<IntegerExpression>),
}

impl BooleanExpression {
    fn eval(&self, env: &Environment) -> bool {
        match self {
            Self::True => true,
            Self::False => false,
            Self::Lt(lhs, rhs) => lhs.eval(env) < rhs.eval(env),
        }
    }
}

/// GuardStatement
#[derive(Clone, Hash)]
pub enum GuardStatement {
    When(BooleanExpression),
}

impl GuardStatement {
    fn exec(&self, env: &Environment) -> bool {
        match self {
            Self::When(cond) => cond.eval(env),
        }
    }
}

/// Statement
#[derive(Clone, Hash)]
pub enum Statement {
    Assign(&'static str, IntegerExpression),
    For(Vec<(GuardStatement, Vec<Statement>)>),
}

impl Statement {
    /// Return all possible worlds after execution
    fn exec(&self, env: &Environment, cont: &[Statement]) -> Vec<LocalState> {
        match self {
            Self::Assign(var_name, expr) => {
                // Create new environment
                let mut new_env = env.clone();
                new_env.var_set(var_name, expr.eval(env));
                vec![LocalState {
                    environment: new_env,
                    statements: cont.to_vec(),
                }]
            }
            Self::For(cases) => {
                let mut states = Vec::new();

                for (guard, stmts) in cases {
                    if guard.exec(env) {
                        let mut stmts = stmts.clone();
                        stmts.push(self.clone());
                        stmts.extend(cont.to_vec());

                        states.push(LocalState {
                            environment: env.clone(),
                            statements: stmts,
                        });
                    }
                }
                states
            }
        }
    }
}

/// World
#[derive(Clone, Hash)]
struct World {
    environment: Environment,
    /// Use BTreeMap to implement Hash trait
    program_counters: BTreeMap<&'static str, Vec<Statement>>,
}

impl World {
    fn eval(&self, f: &BooleanExpression) -> bool {
        f.eval(&self.environment)
    }

    // Return the label of the world
    fn label(&self) -> String {
        let mut label = Vec::new();
        for (var_name, val) in &self.environment.variables {
            label.push(String::from(&format!("{}={}", var_name, val)));
        }
        label.join("\n")
    }

    /// Return the initial world of the system
    fn initial_world(system: &System) -> World {
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
    fn id(&self) -> WorldId {
        let mut hasher = DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }

    /// Return all possible worlds that can be transitioned to in one step
    fn step_global(&self) -> Vec<World> {
        let mut worlds = Vec::new();

        for (proc_name, stmts) in &self.program_counters {
            for next in stmts[0].exec(&self.environment, &stmts[1..]) {
                let mut pcs = self.program_counters.clone();
                pcs.insert(proc_name, next.statements.clone());
                worlds.push(World {
                    environment: next.environment,
                    program_counters: pcs,
                })
            }
        }

        worlds
    }
}
