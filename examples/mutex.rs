use model_checker_from_scratch::{
    ctl::CTL::{AP, EF, EG},
    pramo::{
        BooleanExpression::{Eq, Lt, True},
        GuardStatement::{Lock, When},
        GuardedCase::Case,
        IntegerExpression::{Add, Int, Sub, Var},
        Locks, Process,
        Statement::{Assign, For, Unlock},
        System, Variables,
    },
};

fn bad_process(name: &'static str) -> Process {
    Process {
        name,
        statements: vec![For(vec![Case(
            When(True),
            vec![
                Assign("critical", Add(Box::new(Var("critical")), Box::new(Int(1)))),
                Assign("critical", Sub(Box::new(Var("critical")), Box::new(Int(1)))),
            ],
        )])],
    }
}

fn good_process(name: &'static str, flag: &'static str) -> Process {
    Process {
        name,
        statements: vec![For(vec![Case(
            Lock("mutex"),
            vec![
                Assign("critical", Add(Box::new(Var("critical")), Box::new(Int(1)))),
                Assign(flag, Int(1)),
                Assign(flag, Int(0)),
                Assign("critical", Sub(Box::new(Var("critical")), Box::new(Int(1)))),
                Unlock("mutex"),
            ],
        )])],
    }
}

fn main() {
    let system = System {
        variables: Variables::from([("critical", 0)]),
        locks: Locks::new(),
        processes: vec![bad_process("p"), bad_process("q")],
    };

    // There is no deadlock but mutual exclusion does not hold
    let model = system.to_kripke_model();
    let sat = model.check(&EF(Box::new(AP(Lt(Int(1), Var("critical"))))));
    assert_ne!(sat.len(), 0);
    println!("{}", model.to_dot_string(&sat));

    let system = System {
        variables: Variables::from([("critical", 0), ("csp", 0), ("csq", 0)]),
        locks: Locks::from([("mutex", None)]),
        processes: vec![good_process("p", "csp"), good_process("q", "csq")],
    };

    // There is no deadlock and mutual exclusion holds but, starvation exists
    let model = system.to_kripke_model();
    let sat = model.check(&EF(Box::new(AP(Lt(Int(1), Var("critical"))))));
    assert_eq!(sat.len(), 0);

    let sat = model.check(&EG(Box::new(AP(Eq(Var("csp"), Int(0))))));
    assert_ne!(sat.len(), 0);
    println!("{}", model.to_dot_string(&sat));
}
