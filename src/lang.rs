use crate::ctl::CTL;
use crate::kripke::{SymbolicKripkeFrame, WorldId};
use core::panic;
use std::collections::HashSet;
use std::hash::Hash;
use std::{
    collections::{hash_map::DefaultHasher, BTreeMap, HashMap},
    hash::Hasher,
};

/// Kripke model
pub struct KripkeModel {
    worlds: HashMap<WorldId, World>,
    initial: WorldId,
    accs: HashMap<WorldId, HashSet<WorldId>>,
    frame: SymbolicKripkeFrame,
}

impl KripkeModel {
    /// Verify a CTL formula
    pub fn check(&self, f: &CTL<BooleanExpression>) -> HashSet<WorldId> {
        let sat = |p: &BooleanExpression| -> HashSet<WorldId> {
            self.worlds
                .iter()
                .filter_map(|(id, w)| if w.eval(p) { Some(*id) } else { None })
                .collect()
        };
        self.frame.check(f, &sat)
    }

    /// Convert to .dot string
    pub fn to_dot_string(&self, sat: &HashSet<WorldId>) -> String {
        let mut s = String::from("digraph {\n");
        for (id, wld) in &self.worlds {
            s.push_str(&format!("\t{} [ label = \"{}\" ];\n", id, wld.label()));
            if *id == self.initial {
                s.push_str(&format!("\t{} [ penwidth = 5 ];\n", id));
            }
            if sat.contains(id) {
                s.push_str(&format!(
                    "\t{} [ style=filled, fillcolor=\"#ADD8E6AA\", fontcolor=black ];\n",
                    id
                ));
            }
        }
        for (from, tos) in &self.accs {
            for to in tos {
                s.push_str(&format!("\t{} -> {};\n", from, to));
            }
        }
        s.push('}');
        s
    }
}

/// System
pub struct System {
    pub variables: Variables,
    pub locks: Locks,
    pub processes: Vec<Process>,
}

impl System {
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
            initial: init.id(),
            accs: accs.clone(),
            frame: SymbolicKripkeFrame::from(visited.keys().cloned().collect(), accs),
        }
    }
}

/// Process
pub struct Process {
    pub name: &'static str,
    pub statements: Vec<Statement>,
}

/// Variables (All variables are global and shared)
pub type Variables = BTreeMap<&'static str, i64>;

/// Locks
pub type Locks = BTreeMap<&'static str, Option<&'static str>>;

/// Environment
#[derive(Clone, Hash)]
struct Environment {
    variables: Variables,
    locks: Locks,
}

/// LocalState
struct LocalState(Environment, Vec<Statement>);

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
            Self::Var(name) => env
                .variables
                .get(name)
                .cloned()
                .unwrap_or_else(|| panic!("variable does not exists: {}", name)),
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
    Lt(IntegerExpression, IntegerExpression),
    Eq(IntegerExpression, IntegerExpression),
}

impl BooleanExpression {
    fn eval(&self, env: &Environment) -> bool {
        match self {
            Self::True => true,
            Self::False => false,
            Self::Lt(lhs, rhs) => lhs.eval(env) < rhs.eval(env),
            Self::Eq(lhs, rhs) => lhs.eval(env) == rhs.eval(env),
        }
    }
}

/// Statement
#[derive(Clone, Hash)]
pub enum Statement {
    Assign(&'static str, IntegerExpression),
    Lock(&'static str),
    Unlock(&'static str),
    Await(BooleanExpression),
    If(BooleanExpression, Vec<Statement>, Vec<Statement>),
    While(BooleanExpression, Vec<Statement>),
}

impl Statement {
    /// Return all possible worlds after execution
    fn exec(
        &self,
        env: &Environment,
        proc_name: &'static str,
        cont: &[Statement],
    ) -> Option<LocalState> {
        match self {
            Self::Assign(var_name, expr) => {
                // Create new environment
                let mut new_env = env.clone();
                if new_env.variables.insert(var_name, expr.eval(env)).is_none() {
                    panic!("variable does not exists: {}", var_name);
                }
                Some(LocalState(new_env, cont.to_vec()))
            }
            Self::Lock(lock_name) => {
                match env
                    .locks
                    .get(lock_name)
                    .unwrap_or_else(|| panic!("lock does not exists: {}", lock_name))
                {
                    Some(_) => None,
                    None => {
                        let mut new_env = env.clone();
                        new_env.locks.insert(lock_name, Some(proc_name));
                        Some(LocalState(new_env, cont.to_vec()))
                    }
                }
            }
            Self::Unlock(lock_name) => {
                match env
                    .locks
                    .get(lock_name)
                    .cloned()
                    .unwrap_or_else(|| panic!("lock does not exists: {}", lock_name))
                {
                    Some(owner) if owner == proc_name => {
                        // Unlock
                        let mut new_env = env.clone();
                        new_env.locks.insert(lock_name, None);
                        Some(LocalState(new_env, cont.to_vec()))
                    }
                    _ => unimplemented!(),
                }
            }
            Self::Await(cond) => {
                if !cond.eval(env) {
                    None
                } else {
                    Some(LocalState(env.clone(), cont.to_vec()))
                }
            }
            Self::If(cond, then_stmts, else_stmts) => {
                if cond.eval(env) {
                    let mut stmts = then_stmts.clone();
                    stmts.extend(cont.to_vec());
                    Some(LocalState(env.clone(), stmts))
                } else {
                    let mut stmts = else_stmts.clone();
                    stmts.extend(cont.to_vec());
                    Some(LocalState(env.clone(), stmts))
                }
            }
            Self::While(cond, stmts) => {
                if !cond.eval(env) {
                    Some(LocalState(env.clone(), cont.to_vec()))
                } else {
                    let mut stmts = stmts.clone();
                    stmts.push(self.clone());
                    stmts.extend(cont.to_vec());
                    Some(LocalState(env.clone(), stmts))
                }
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
        for (lock_name, proc_name) in &self.environment.locks {
            if let Some(proc_name) = proc_name {
                label.push(String::from(&format!("{}[{}]", lock_name, proc_name)));
            }
        }
        label.join("\n")
    }

    /// Return the initial world of the system
    fn initial_world(system: &System) -> World {
        World {
            environment: Environment {
                variables: system.variables.clone(),
                locks: system.locks.clone(),
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
            if !stmts.is_empty() {
                match stmts[0].exec(&self.environment, proc_name, &stmts[1..]) {
                    Some(LocalState(env, cont)) => {
                        let mut pcs = self.program_counters.clone();
                        pcs.insert(proc_name, cont);
                        worlds.push(World {
                            environment: env,
                            program_counters: pcs,
                        })
                    }
                    None => {
                        worlds.push(self.clone());
                    }
                }
            }
        }

        worlds
    }
}
