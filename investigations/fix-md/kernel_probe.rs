use kernel::{
    check::Checker,
    environment::{Environment, InductiveSpec},
    ids::{InductiveId, SymbolId},
    metavariables::MetaContext,
    reduction::convertible,
    sort::{BaseSort, Sort},
    syntax::{Arena, Binding, Expression, Mode, Node},
};

fn lambda(a: &Arena, domain: Expression, body: Expression) -> Expression {
    a.alloc(Node::Lambda {
        mode: Mode::Pure,
        var: SymbolId::ANONYMOUS,
        domain,
        body,
    })
}

fn main() {
    let mut env = Environment::new();
    let a = env.arena.clone();
    let set_sort = Sort::Base(BaseSort::Set(0));
    let set = a.sort(set_sort);
    let prop = a.sort(Sort::Base(BaseSort::Prop));
    let unit_id = InductiveId(0);
    let unit = a.alloc(Node::IndType {
        inductive: unit_id,
        parameters: vec![],
    });
    env.register_inductive(
        unit_id,
        InductiveSpec {
            parameters: vec![],
            arity: set,
            constructors: vec![unit],
            sort: set_sort,
        },
    )
    .unwrap();
    let value = a.alloc(Node::IndCtor {
        inductive: unit_id,
        constructor: 0,
        parameters: vec![],
    });
    let proposition = a.alloc(Node::Equal {
        left: value,
        right: value,
    });
    let motive = lambda(&a, unit, prop);
    let error = Checker::new(&env, &mut MetaContext::new(), vec![])
        .infer(motive)
        .unwrap_err();
    assert!(error.to_string().contains("upper sort has no classifier"));
    println!("ordinary motive lambda: rejected (upper sort has no classifier)");
    let elimination = a.alloc(Node::IndElim {
        inductive: unit_id,
        scrutinee: value,
        motive,
        cases: vec![proposition],
    });
    let ty = Checker::new(&env, &mut MetaContext::new(), vec![])
        .infer(elimination)
        .unwrap();
    assert!(convertible(&env, ty, prop).unwrap());
    assert!(convertible(&env, elimination, proposition).unwrap());
    println!("direct IndElim with Prop-valued motive: accepted and reduces to proposition");

    let record_id = InductiveId(1);
    let record = a.alloc(Node::IndType {
        inductive: record_id,
        parameters: vec![],
    });
    let ctor_ty = a.alloc(Node::Product {
        var: SymbolId::ANONYMOUS,
        domain: unit,
        body: record,
    });
    env.register_inductive(
        record_id,
        InductiveSpec {
            parameters: vec![],
            arity: set,
            constructors: vec![ctor_ty],
            sort: set_sort,
        },
    )
    .unwrap();
    let constructor = a.alloc(Node::IndCtor {
        inductive: record_id,
        constructor: 0,
        parameters: vec![],
    });
    let s = a.bound(0);
    let projection = a.alloc(Node::Case {
        inductive: record_id,
        scrutinee: s,
        motive: lambda(&a, record, unit),
        branches: vec![lambda(&a, unit, a.bound(0))],
    });
    let repacked = a.alloc(Node::App {
        mode: Mode::Pure,
        function: constructor,
        argument: projection,
    });
    let context = vec![Binding {
        var: SymbolId::ANONYMOUS,
        ty: record,
    }];
    Checker::new(&env, &mut MetaContext::new(), context.clone())
        .check(repacked, record)
        .unwrap();
    assert!(!convertible(&env, s, repacked).unwrap());
    let eta = a.alloc(Node::Equal {
        left: s,
        right: repacked,
    });
    assert!(
        Checker::new(&env, &mut MetaContext::new(), context.clone())
            .check(a.alloc(Node::IdRefl { element: s }), eta)
            .is_err()
    );
    println!("record eta for a variable: not definitionally equal; refl rejected");
    let branch_value = a.alloc(Node::App {
        mode: Mode::Pure,
        function: constructor,
        argument: a.bound(0),
    });
    let proof = a.alloc(Node::IndElim {
        inductive: record_id,
        scrutinee: s,
        motive: lambda(&a, record, eta),
        cases: vec![lambda(
            &a,
            unit,
            a.alloc(Node::IdRefl {
                element: branch_value,
            }),
        )],
    });
    Checker::new(&env, &mut MetaContext::new(), context)
        .check(proof, eta)
        .unwrap();
    println!("record eta as a propositional equality: proved by direct IndElim");

    let mut metas = MetaContext::new();
    let function_type = metas.fresh(&a, vec![], None);
    let context = vec![
        Binding {
            var: SymbolId::ANONYMOUS,
            ty: function_type,
        },
        Binding {
            var: SymbolId::ANONYMOUS,
            ty: unit,
        },
    ];
    let application = a.alloc(Node::App {
        mode: Mode::Pure,
        function: a.bound(1),
        argument: a.bound(0),
    });
    let error = metas.infer(&env, context, application).unwrap_err();
    assert!(error.to_string().contains("occurs check failed"));
    println!("application of a local with unknown type: occurs check failed");
}
