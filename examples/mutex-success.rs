use model_checker_from_scratch::{
    ctl::CTL::{AG, AP},
    pramo::{
        BooleanExpression::Lt,
        GuardStatement::Lock,
        GuardedCase::Case,
        IntegerExpression::{Add, Int, Sub, Var},
        Locks, Process,
        Statement::{Assign, For, Unlock},
        System, Variables,
    },
};

fn process(name: &'static str) -> Process {
    Process {
        name,
        statements: vec![For(vec![Case(
            Lock("mutex"),
            vec![
                Assign("critical", Add(Box::new(Var("critical")), Box::new(Int(1)))),
                Assign("critical", Sub(Box::new(Var("critical")), Box::new(Int(1)))),
                Unlock("mutex"),
            ],
        )])],
    }
}

fn main() {
    let system = System {
        variables: Variables::from([("critical", 0)]),
        locks: Locks::from([("mutex", None)]),
        processes: vec![process("A"), process("B"), process("C")],
    };

    let model = system.to_kripke_model();
    let res = model.check(&AG(Box::new(AP(Lt(Var("critical"), Int(2))))));
    println!("{}", model.to_dot_string(&res));
}
