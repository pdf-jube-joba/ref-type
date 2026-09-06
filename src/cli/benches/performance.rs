//! Run with `cargo bench -p cli --bench performance -- --help`.
mod support;

use front::{elaborator::GlobalEnvironment, syntax::Module};
use kernel::{
    calculus::normalize,
    environment::{CrateEnv, DefinedConstant, ModuleItem},
    exp::ExpNode,
    program::{ComputationNode, ValueNode},
    program_calculus::{Evaluation, evaluate_computation},
    sort::Sort,
};
use std::{hint::black_box, path::Path, time::Duration};
use support::{Case, timed};

const MCCARTHY: &str = include_str!("../../../tests/ok/general-recursion/mccarthy-91.ref");

fn elaborate(modules: &[Module]) -> GlobalEnvironment {
    let mut global = GlobalEnvironment::default();
    for module in modules {
        global
            .add_new_module_to_root(module)
            .unwrap_or_else(|error| {
                panic!(
                    "benchmark input failed: {}",
                    front::metavariables::format_elaboration_error(global.crate_env(), &error)
                )
            });
    }
    assert!(
        !global
            .outputs()
            .iter()
            .any(|output| matches!(output, front::output::Output::OutOfFuel(_))),
        "benchmark exhausted evaluation fuel"
    );
    global
}

fn parse_program() -> Duration {
    let (elapsed, modules) =
        timed(|| front::parse::str_parse_modules(black_box(MCCARTHY)).unwrap());
    assert_eq!(modules.len(), 1);
    elapsed
}

fn load_library() -> Duration {
    let (elapsed, modules) =
        timed(|| front::module_loader::load_modules_from_root(Path::new("lib/root.ref")).unwrap());
    assert!(!modules.is_empty());
    elapsed
}

fn check_library(modules: &[Module]) -> Duration {
    // A fresh environment prevents cross-iteration caches and arena growth.
    let (elapsed, _global) = timed(|| elaborate(black_box(modules)));
    elapsed
}

fn pipeline(path: &str) -> Duration {
    let (elapsed, _global) = timed(|| {
        let modules = front::module_loader::load_modules_from_root(Path::new(path)).unwrap();
        elaborate(&modules)
    });
    elapsed
}

fn beta_chain(depth: usize) -> Duration {
    let mut env = CrateEnv::new();
    let var = env.intern("x");
    let arena = env.arena();
    let expected = arena.sort(Sort::Set(0));
    let identity = arena.alloc(ExpNode::Lam {
        var,
        ty: arena.sort(Sort::SetKind(0)),
        body: arena.exp_bound(0),
    });
    let mut term = expected;
    for _ in 0..depth {
        term = arena.alloc(ExpNode::App {
            func: identity,
            arg: term,
        });
    }
    let (elapsed, result) = timed(|| normalize(black_box(&env), black_box(term)));
    assert_eq!(arena.get(result), arena.get(expected));
    elapsed
}

fn countdown_modules(size: usize) -> Vec<Module> {
    let mut number_definitions = String::from("\\vdefinition n0: Nat := Nat::zero;\n");
    for index in 1..=size {
        use std::fmt::Write;
        writeln!(
            number_definitions,
            "\\vdefinition n{index}: Nat := Nat::succ n{};",
            index - 1
        )
        .unwrap();
    }
    let source = format!(
        r"\module Countdown {{
  \inductive Nat: \VType :=
  | zero: Nat;
  | succ: Nat -> Nat;
  ;
  \vdefinition step: \U(\CFun(Nat, \F(\PRunStep(Nat, Nat)))) :=
    \thunk(\clam(n, Nat,
      \vcase(Nat, n) {{
      | zero() => \return(\Pfinish(Nat, Nat, Nat::zero));
      | succ(rest) => \return(\Pcontinue(Nat, Nat, rest));
      }}));
  {number_definitions}
  \cdefinition main: \F(Nat) := \Prun(Nat, Nat, step, n{size});
}}"
    );
    front::parse::str_parse_modules(&source).unwrap()
}

fn countdown(modules: &[Module]) -> Duration {
    // Parsing and elaboration are setup, outside the evaluation timer.
    let global = elaborate(modules);
    let env = global.crate_env();
    let module = env.module(env.root_module()).children()[0];
    let Some(ModuleItem::Definition { definition, .. }) = env.module(module).item("main") else {
        panic!("missing countdown main")
    };
    let DefinedConstant::ProgramComputation { body, .. } = env.definition(*definition) else {
        panic!("countdown main is not a computation")
    };
    let (elapsed, result) = timed(|| evaluate_computation(black_box(env), black_box(*body)));
    let Evaluation::Normal(result) = result else {
        panic!("countdown exhausted evaluation fuel")
    };
    let ComputationNode::Return { value } = env.arena().get(result) else {
        panic!("countdown did not return a value")
    };
    assert!(
        matches!(env.arena().get(value), ValueNode::InductiveConstructor { idx: 0, fields, .. } if fields.is_empty())
    );
    elapsed
}

fn main() -> anyhow::Result<()> {
    std::env::set_current_dir(Path::new(env!("CARGO_MANIFEST_DIR")).join("../.."))?;
    // Initialize fixtures lazily: filtering to a kernel case need not load the library.
    let library = std::cell::OnceCell::new();
    let small = std::cell::OnceCell::new();
    let large = std::cell::OnceCell::new();
    let cases = vec![
        Case::new("parse/mccarthy91", parse_program),
        Case::new("load/library", load_library),
        Case::new("check/library", || {
            check_library(library.get_or_init(|| {
                front::module_loader::load_modules_from_root(Path::new("lib/root.ref")).unwrap()
            }))
        }),
        Case::new("pipeline/library", || pipeline("lib/root.ref")),
        Case::new("pipeline/mccarthy91", || {
            pipeline("tests/ok/general-recursion/mccarthy-91.ref")
        }),
        Case::new("normalize/beta256", || beta_chain(256)),
        Case::new("evaluate/countdown32", || {
            countdown(small.get_or_init(|| countdown_modules(32)))
        }),
        Case::new("evaluate/countdown128", || {
            countdown(large.get_or_init(|| countdown_modules(128)))
        }),
    ];
    support::run(cases)
}
