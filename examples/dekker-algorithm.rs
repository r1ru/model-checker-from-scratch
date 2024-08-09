use model_checker_from_scratch::{
    ctl::CTL::{AP, EF, EG},
    pramo::{
        BooleanExpression::{Eq, Lt, True},
        IntegerExpression::{Add, Int, Sub, Var},
        Locks, Process,
        Statement::{Assign, Await, If, While},
        System, Variables,
    },
};

fn main() {
    let p = Process {
        name: "p",
        statements: vec![While(
            True,
            vec![
                Assign("wantp", Int(1)),
                While(
                    Eq(Var("wantq"), Int(1)),
                    vec![If(
                        Eq(Var("turn"), Int(1)),
                        vec![
                            Assign("wantp", Int(0)),
                            Await(Eq(Var("turn"), Int(0))),
                            Assign("wantp", Int(1)),
                        ],
                        vec![],
                    )],
                ),
                Assign("critical", Add(Box::new(Var("critical")), Box::new(Int(1)))),
                Assign("csp", Int(1)),
                Assign("csp", Int(0)),
                Assign("critical", Sub(Box::new(Var("critical")), Box::new(Int(1)))),
                Assign("turn", Int(1)),
                Assign("wantp", Int(0)),
            ],
        )],
    };

    let q = Process {
        name: "q",
        statements: vec![While(
            True,
            vec![
                Assign("wantq", Int(1)),
                While(
                    Eq(Var("wantp"), Int(1)),
                    vec![If(
                        Eq(Var("turn"), Int(0)),
                        vec![
                            Assign("wantq", Int(0)),
                            Await(Eq(Var("turn"), Int(1))),
                            Assign("wantq", Int(1)),
                        ],
                        vec![],
                    )],
                ),
                Assign("critical", Add(Box::new(Var("critical")), Box::new(Int(1)))),
                Assign("critical", Sub(Box::new(Var("critical")), Box::new(Int(1)))),
                Assign("turn", Int(0)),
                Assign("wantq", Int(0)),
            ],
        )],
    };

    let system = System {
        variables: Variables::from([
            ("turn", 0),
            ("wantp", 0),
            ("wantq", 0),
            ("critical", 0),
            ("csp", 0),
        ]),
        locks: Locks::new(),
        processes: vec![p, q],
    };

    // There is no deadlock and mutal exclusion holds but, starvation exists
    let model = system.to_kripke_model();
    let sat = model.check(&EF(Box::new(AP(Lt(Int(1), Var("critical"))))));
    assert_eq!(sat.len(), 0);

    let sat = model.check(&EG(Box::new(AP(Eq(Var("csp"), Int(0))))));
    assert_ne!(sat.len(), 0);
    println!("{}", model.to_dot_string(&sat));
}
