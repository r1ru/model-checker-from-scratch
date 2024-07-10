use model_checker_from_scratch::{
    ctl::CTL::{AP, EG, EX},
    pramo::{
        BooleanExpression::{Lt, True},
        GuardStatement::Lock,
        GuardedCase::Case,
        IntegerExpression::{Add, Int, Var},
        Locks, Process,
        Statement::{Assign, For, Switch, Unlock},
        System, Variables,
    },
};

fn thread(
    name: &'static str,
    left: &'static str,
    right: &'static str,
    hold: &'static str,
) -> Process {
    Process::new(
        name,
        vec![For(vec![Case(
            Lock(left),
            vec![
                Assign(hold, Add(Box::new(Var(hold)), Box::new(Int(1)))),
                Switch(vec![Case(
                    Lock(right),
                    vec![
                        Assign(hold, Add(Box::new(Var(hold)), Box::new(Int(1)))),
                        Assign(hold, Int(0)),
                        Unlock(right),
                        Unlock(left),
                    ],
                )]),
            ],
        )])],
    )
}

fn main() {
    let system = System::new(
        Variables::from([("hold1", 0), ("hold2", 0)]),
        Locks::from([("fork1", None), ("fork2", None)]),
        vec![
            thread("A", "fork1", "fork2", "hold1"),
            thread("B", "fork1", "fork2", "hold2"),
        ],
    );

    let model = system.to_kripke_model();
    let res = model.check(&Box::new(EX(Box::new(AP(True)))));
    println!("{}", model.to_dot_string(&res));

    // There exists an execution path that falls into starvation
    // To eliminate this, we need the notion of fairness
    let res = model.check(&EG(Box::new(AP(Lt(Var("hold2"), Int(2))))));
    println!("{}", model.to_dot_string(&res));
}
