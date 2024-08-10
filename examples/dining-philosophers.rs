use model_checker_from_scratch::{
    ctl::CTL::{AP, EF, EG},
    lang::{
        BooleanExpression::{Eq, Lt, True},
        IntegerExpression::{Add, Int, Sub, Var},
        Locks, Process,
        Statement::{Assign, Lock, Unlock, While},
        System, Variables,
    },
};

fn process(name: &'static str, flag: &'static str) -> Process {
    Process {
        name,
        statements: vec![
            While(
                True,
                vec![
                    Lock("fork1"),
                    Lock("fork2"),
                    Assign("critical", Add(Box::new(Var("critical")), Box::new(Int(1)))),
                    Assign(flag, Int(1)),
                    Assign(flag, Int(0)),
                    Assign("critical", Sub(Box::new(Var("critical")), Box::new(Int(1)))),
                    Unlock("fork2"),
                    Unlock("fork1"),
                ],
            )
        ],
    }
}

fn main() {
    let system = System {
        variables: Variables::from([("critical", 0), ("csp", 0), ("csq", 0)]),
        locks: Locks::from([("fork1", None), ("fork2", None)]),
        processes: vec![process("p", "csp"), process("q", "csq")],
    };

    // There is no deadlock and mutual exclusion holds but, starvation exists
    let model = system.to_kripke_model();
    let sat = model.check(&EF(Box::new(AP(Lt(Int(1), Var("critical"))))));
    assert_eq!(sat.len(), 0);

    let sat = model.check(&EG(Box::new(AP(Eq(Var("csp"), Int(0))))));
    assert_ne!(sat.len(), 0);
    println!("{}", model.to_dot_string(&sat));
}
