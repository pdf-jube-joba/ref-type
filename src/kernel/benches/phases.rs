use std::hint::black_box;
use std::time::{Duration, Instant};

use kernel::calculus::{convertible, exp_is_alpha_eq, instantiate, normalize, whnf};
use kernel::derivation::infer;
use kernel::exp::{Arena, Context, Exp, Node, Sort, Var};

const WARMUP_ITERATIONS: u64 = 64;
const SAMPLE_COUNT: usize = 25;
const TARGET_SAMPLE_TIME: Duration = Duration::from_millis(20);
const MAX_ITERATIONS_PER_SAMPLE: u64 = 1 << 30;

fn main() {
    let mut arena = Arena::new();
    let binder = Var::new("x");
    let substitution_body = balanced_application(&arena, 8, None);
    let substitution_argument = beta_chain(&arena, 8);
    let expected_substitution = balanced_application(&arena, 8, Some(substitution_argument));
    let reducible = beta_chain(&arena, 48);
    let normal_form = arena.sort(Sort::Set(0));
    let reducible_leaf = beta_chain(&arena, 8);
    let under_constructors = product_tree(&arena, 6, reducible_leaf, "n");
    let normalized_constructors = product_tree(&arena, 6, normal_form, "n");
    let alpha_left = nested_products(&arena, 64, "left");
    let alpha_right = nested_products(&arena, 64, "right");
    let inferred_term = nested_lambdas(&arena, 16);
    let empty_context = Context::new();
    let inputs = arena.mark();

    let substituted = instantiate(&arena, substitution_body, &binder, substitution_argument);
    assert!(exp_is_alpha_eq(&arena, substituted, expected_substitution));
    arena.rewind(inputs);
    let reduced = whnf(&arena, reducible);
    assert!(exp_is_alpha_eq(&arena, reduced, normal_form));
    arena.rewind(inputs);
    let normalized = normalize(&arena, under_constructors);
    assert!(exp_is_alpha_eq(&arena, normalized, normalized_constructors));
    arena.rewind(inputs);
    assert!(convertible(&arena, reducible, normal_form));
    arena.rewind(inputs);
    assert!(exp_is_alpha_eq(&arena, alpha_left, alpha_right));
    assert!(infer(&arena, &empty_context, inferred_term).is_ok());
    arena.rewind(inputs);

    println!("kernel phase benchmarks");
    println!(
        "{:32} {:>12} {:>12} {:>12} {:>12}",
        "benchmark", "median", "min", "p95", "iter/sample"
    );

    run_benchmark("substitution/instantiate", || {
        let result = instantiate(
            &arena,
            black_box(substitution_body),
            &binder,
            black_box(substitution_argument),
        );
        black_box(result);
        arena.rewind(inputs);
    });
    run_benchmark("reduction/whnf", || {
        black_box(whnf(&arena, black_box(reducible)));
        arena.rewind(inputs);
    });
    run_benchmark("reduction/normalize", || {
        black_box(normalize(&arena, black_box(under_constructors)));
        arena.rewind(inputs);
    });
    run_benchmark("conversion/convertible", || {
        black_box(convertible(
            &arena,
            black_box(reducible),
            black_box(normal_form),
        ));
        arena.rewind(inputs);
    });
    run_benchmark("equality/alpha_eq", || {
        black_box(exp_is_alpha_eq(
            &arena,
            black_box(alpha_left),
            black_box(alpha_right),
        ));
    });
    run_benchmark("typing/infer", || {
        black_box(infer(
            &arena,
            black_box(&empty_context),
            black_box(inferred_term),
        ))
        .expect("benchmark term should infer");
        arena.rewind(inputs);
    });
}

fn run_benchmark<R>(name: &str, mut operation: impl FnMut() -> R) {
    for _ in 0..WARMUP_ITERATIONS {
        black_box(operation());
    }
    let iterations = calibrate(&mut operation);
    let mut samples = Vec::with_capacity(SAMPLE_COUNT);
    for _ in 0..SAMPLE_COUNT {
        let started = Instant::now();
        for _ in 0..iterations {
            black_box(operation());
        }
        samples.push(started.elapsed().as_secs_f64() * 1_000_000_000.0 / iterations as f64);
    }
    samples.sort_by(f64::total_cmp);
    println!(
        "{name:32} {:>12} {:>12} {:>12} {iterations:>12}",
        format_duration(samples[SAMPLE_COUNT / 2]),
        format_duration(samples[0]),
        format_duration(samples[(SAMPLE_COUNT * 95).div_ceil(100) - 1]),
    );
}

fn calibrate<R>(operation: &mut impl FnMut() -> R) -> u64 {
    let mut iterations = 1;
    loop {
        let started = Instant::now();
        for _ in 0..iterations {
            black_box(operation());
        }
        if started.elapsed() >= TARGET_SAMPLE_TIME || iterations >= MAX_ITERATIONS_PER_SAMPLE {
            return iterations;
        }
        iterations *= 2;
    }
}

fn format_duration(nanoseconds: f64) -> String {
    if nanoseconds < 1_000.0 {
        format!("{nanoseconds:.1} ns")
    } else if nanoseconds < 1_000_000.0 {
        format!("{:.2} us", nanoseconds / 1_000.0)
    } else {
        format!("{:.2} ms", nanoseconds / 1_000_000.0)
    }
}

fn balanced_application(arena: &Arena, depth: usize, leaf: Option<Exp>) -> Exp {
    if depth == 0 {
        return leaf.unwrap_or_else(|| arena.bound(0));
    }
    let func = balanced_application(arena, depth - 1, leaf);
    let arg = balanced_application(arena, depth - 1, leaf);
    arena.alloc(Node::App { func, arg })
}

fn beta_chain(arena: &Arena, depth: usize) -> Exp {
    let mut term = arena.sort(Sort::Set(0));
    for index in 0..depth {
        let identity = arena.alloc(Node::Lam {
            var: Var::new(&format!("beta{index}")),
            ty: arena.sort(Sort::Set(0)),
            body: arena.bound(0),
        });
        term = arena.alloc(Node::App {
            func: identity,
            arg: term,
        });
    }
    term
}

fn product_tree(arena: &Arena, depth: usize, leaf: Exp, prefix: &str) -> Exp {
    if depth == 0 {
        return leaf;
    }
    let ty = product_tree(arena, depth - 1, leaf, prefix);
    let body = product_tree(arena, depth - 1, leaf, prefix);
    arena.alloc(Node::Prod {
        var: Var::new(&format!("{prefix}{depth}")),
        ty,
        body,
    })
}

fn nested_products(arena: &Arena, depth: usize, prefix: &str) -> Exp {
    let mut term = arena.bound(0);
    for index in 0..depth {
        term = arena.alloc(Node::Prod {
            var: Var::new(&format!("{prefix}{index}")),
            ty: arena.sort(Sort::Set(0)),
            body: term,
        });
    }
    term
}

fn nested_lambdas(arena: &Arena, depth: usize) -> Exp {
    let mut term = arena.bound(0);
    for index in 0..depth {
        term = arena.alloc(Node::Lam {
            var: Var::new(&format!("arg{index}")),
            ty: arena.sort(Sort::Set(0)),
            body: term,
        });
    }
    term
}
