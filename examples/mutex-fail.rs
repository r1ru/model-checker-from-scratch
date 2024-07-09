use model_checker_from_scratch::{
    ctl::CTL::{AG, AP},
    pramo::{
        BooleanExpression::{Lt, True},
        GuardStatement::When,
        GuardedCase::Case,
        IntegerExpression::{Add, Int, Sub, Var},
        Locks, Process,
        Statement::{Assign, For},
        System, Variables,
    },
};

fn thread(name: &'static str) -> Process {
    Process::new(
        name,
        vec![For(vec![Case(
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
        Locks::from([]),
        vec![thread("A"), thread("B"), thread("C")],
    );

    let model = system.to_kripke_model();
    let res = model.check(&AG(Box::new(AP(Lt(Var("critical"), Int(2))))));
    println!("{}", model.to_dot_string(&res));
}
