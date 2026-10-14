use elaboration::Checker;
#[test]
fn scoped_macro_exports_preserve_private_template_bindings() {
    use syntax::syntax::{Identifier, ModuleBody, ModuleItem};
    let mut modules = syntax::parse::str_parse_modules(
        r"\module M(A: \Set, a, b: A) {
      \definition before: b = b := \refl(wrapped!{});
      \macro value() := a;
      \definition outside: a = a := \refl(value!{});
      \macro wrapped() := value!{};
      \macro value() := b;
    }",
    )
    .unwrap();
    let ModuleBody::Inline(items) = &mut modules[0].body else {
        unreachable!()
    };
    let local = items.split_off(3);
    items.push(ModuleItem::Scoped {
        exports: vec![Identifier("wrapped".into())],
        items: local,
    });
    modules[0].declaration_spans.truncate(4);
    let project = resolve::resolve(&modules).unwrap();
    Checker::default().check(&project).unwrap();
}

#[test]
fn generated_block_math_priority_is_stable_after_lazy_preparation() {
    use syntax::syntax::{ModuleBody, ModuleItem};
    let mut modules = syntax::parse::str_parse_modules(
        r"\module M(A: \Set, a, b: A) {
      \math-macro first($x, \+, $y) := $x;
      \math-macro second($x, \+, $y) := $y;
      \definition one: a = a := \refl(\(a + b\));
      \definition two: a = a := \refl(\(a + b\));
    }",
    )
    .unwrap();
    let ModuleBody::Inline(items) = &mut modules[0].body else {
        unreachable!()
    };
    let local = std::mem::take(items);
    items.push(ModuleItem::Scoped {
        exports: Vec::new(),
        items: local,
    });
    modules[0].declaration_spans.truncate(1);
    let project = resolve::resolve(&modules).unwrap();
    Checker::default().check(&project).unwrap();
}
