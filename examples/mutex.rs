use model_checker_from_scratch::{
    ctl::CTL::{AG, AP},
    pramo::{
        BooleanExpression::{Lt, True},
        GuardStatement::When,
        IntegerExpression::{Add, Int, Sub, Var},
        Statement::{Assign, For},
        {Process, System, Variables},
    },
};

fn bad_thread(name: &'static str) -> Process {
    Process::new(
        name,
        vec![For(vec![(
            When(True),
            vec![
                Assign("critical", Add(Box::new(Var("critical")), Box::new(Int(1)))),
                Assign("critical", Sub(Box::new(Var("critical")), Box::new(Int(1)))),
            ],
        )])],
    )
}

fn main() {
    let system = System::new(
        Variables::from([("critical", 0)]),
        vec![bad_thread("A"), bad_thread("B"), bad_thread("C")],
    );

    let model = system.to_kripke_model();
    let unsat = model.check(&AG(Box::new(AP(Lt(
        Box::new(Var("critical")),
        Box::new(Int(2)),
    )))));
    println!("{}", model.to_dot_string(&unsat));
}
