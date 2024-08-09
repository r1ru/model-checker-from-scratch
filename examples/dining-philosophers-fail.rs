use model_checker_from_scratch::{
    ctl::CTL::{AP, EX},
    pramo::{
        BooleanExpression::{Eq, True},
        GuardStatement::{Lock, When},
        GuardedCase::Case,
        IntegerExpression::{Add, Int, Var},
        Locks, Process,
        Statement::{Assign, For, Unlock},
        System, Variables,
    },
};

fn process(
    name: &'static str,
    left: &'static str,
    right: &'static str,
    hold: &'static str,
) -> Process {
    Process {
        name,
        statements: vec![For(vec![
            Case(
                Lock(left),
                vec![Assign(hold, Add(Box::new(Var(hold)), Box::new(Int(1))))],
            ),
            Case(
                Lock(right),
                vec![Assign(hold, Add(Box::new(Var(hold)), Box::new(Int(1))))],
            ),
            Case(
                When(Eq(Var(hold), Int(2))),
                vec![Assign(hold, Int(0)), Unlock(left), Unlock(right)],
            ),
        ])],
    }
}

fn main() {
    let system = System {
        variables: Variables::from([("hold1", 0), ("hold2", 0)]),
        locks: Locks::from([("fork1", None), ("fork2", None)]),
        processes: vec![
            process("A", "fork1", "fork2", "hold1"),
            process("B", "fork2", "fork1", "hold2"),
        ],
    };

    let model = system.to_kripke_model();
    // TODO: Consider the case where the for loop is not used in the process
    let sat = model.check(&Box::new(EX(Box::new(AP(True)))));
    println!("{}", model.to_dot_string(&sat));
}
