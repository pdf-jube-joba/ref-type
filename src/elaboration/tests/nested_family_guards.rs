use elaboration::Checker;

const SOURCE: &str = include_str!("fixtures/nested_family_guards.ref");

fn check(source: &str) -> Result<(), String> {
    let modules = syntax::parse::str_parse_modules(source).map_err(|error| error.to_string())?;
    let project = resolve::resolve(&modules).map_err(|error| error.to_string())?;
    let mut checker = Checker::default();
    checker
        .check(&project)
        .map_err(|error| format!("module {:?}: {error}", checker.active_module_path()))
}

#[test]
fn imported_factory_specializes_nested_family_guards() {
    check(SOURCE.split_once("\\module Use").unwrap().0).expect("generic factory");
    check(SOURCE).unwrap();
}

#[test]
fn imported_factory_preserves_distinct_ambient_parameters() {
    let (templates, caller) = SOURCE.split_once("\\module Use").unwrap();
    let caller = caller
        .replace("(R: \\Set)", "(R, S: \\Set)")
        .replace("\\root.Chains[R := R]", "\\root.Chains[R := S]")
        .replace(
            "\\root.Resolutions[R := R].Of",
            "\\root.Resolutions[R := S].Of",
        );
    let error = check(&format!("{templates}\\module Use{caller}")).unwrap_err();
    assert!(
        error.contains("types are not convertible")
            || error.contains("incompatible rigid expressions"),
        "{error}"
    );
}

fn with_fixed_index() -> String {
    let indices = r"\module Indices { \inductive Index: \Set := | point: Index; }";
    let source = SOURCE
        .replace("Carrier: R -> \\Set", "Carrier: Indices.Index -> \\Set")
        .replace("\\forall (n: R)", "\\forall (n: Indices.Index)")
        .replace(
            "\\module Chains(R: \\Set) {",
            "\\module Chains(R: \\Set) { \\import \\root.Indices[] \\as Indices;",
        )
        .replace(
            "\\module Resolutions(R: \\Set) {",
            "\\module Resolutions(R: \\Set) { \\import \\root.Indices[] \\as Indices;",
        );
    format!("{indices}\n{source}")
}

#[test]
fn imported_factory_specializes_space_guards_with_fixed_indices() {
    check(&with_fixed_index()).unwrap();
}

#[test]
fn fixed_index_factory_rejects_spaces_over_a_different_ambient_type() {
    let source = with_fixed_index();
    let (templates, caller) = source.split_once("\\module Use").unwrap();
    let caller = caller
        .replace("(R: \\Set)", "(R, S: \\Set)")
        .replace("\\root.Chains[R := R]", "\\root.Chains[R := S]")
        .replace(
            "\\root.Resolutions[R := R].Of",
            "\\root.Resolutions[R := S].Of",
        );
    let error = check(&format!("{templates}\\module Use{caller}")).unwrap_err();
    assert!(
        error.contains("types are not convertible")
            || error.contains("incompatible rigid expressions"),
        "{error}"
    );
}

#[test]
fn imported_factory_fields_can_be_projected_after_specialization() {
    let source = SOURCE.replace(
        "\\definition sequence: Sequences.Sequence := Sequences.make P p;",
        "\\definition sequence: Sequences.Sequence := Sequences.make P p;\n\\definition recovered: \\root.Resolutions[R := R].Of[P := P].Data := sequence.data;",
    );
    check(&source).unwrap();
}

#[test]
fn imported_factory_specializes_a_structure_dependent_type_alias() {
    let source = SOURCE
        .replace("\\structure Complex { family: Family }", r"\structure Complex { family: Family }
            \module Pair(A, B: Complex) {
                \definition Data: \Set := \forall (n: R) -> A.family.Carrier n -> B.family.Carrier n;
            }")
        .replace("\\structure Sequence {", r"\definition ChainData(P, Q: Chains.Complex): \Set := \root.Chains[R := R].Pair[A := P, B := Q].Data;
            \structure Sequence {")
        .replace("data: Resolutions.Of[P := complex].Data", "data: ChainData complex complex")
        .replace("(p: Resolutions.Of[P := P].Data)", "(p: ChainData P P)")
        .replace("p: \\root.Resolutions[R := R].Of[P := P].Data", "p: Chains.Pair[A := P, B := P].Data");
    for source in [
        source.clone(),
        source.replace(r"\root.Chains[R := R].Pair", "Chains.Pair"),
    ] {
        check(&source).unwrap();
        let (templates, caller) = source.split_once(r"\module Use").unwrap();
        let caller = caller
            .replace(r"(R: \Set)", r"(R, S: \Set)")
            .replace(r"\root.Chains[R := R]", r"\root.Chains[R := S]");
        let error = check(&format!(r"{templates}\module Use{caller}")).unwrap_err();
        assert!(
            error.contains("types are not convertible")
                || error.contains("incompatible rigid expressions"),
            "{error}"
        );
    }
}

#[test]
fn specialized_factory_fields_can_be_record_type_arguments() {
    let source = SOURCE
        .replace(r"\structure Complex { family: Family }", r"\structure Complex { family: Family }
            \structure Data[family: Family]: \Set { read: \forall (n: R) -> family.Carrier n }")
        .replace(r"\structure Sequence {", r"\definition makeFamily(P: Chains.Complex): Chains.Family := Chains.Family {
                Carrier := P.family.Carrier, space := P.family.space,
            };
            \structure Sequence {")
        .replace(r"\definition sequence: Sequences.Sequence := Sequences.make P p;", r"\definition sequence: Sequences.Sequence := Sequences.make P p;
            \definition data: Chains.Data[Sequences.makeFamily P] := Chains.Data[Sequences.makeFamily P] { read := p };");
    check(&source).unwrap();
}

#[test]
fn specialized_factory_fields_can_be_module_arguments() {
    let source = SOURCE
        .replace(
            r"\structure Complex { family: Family }",
            r"\structure Complex { family: Family }
            \module Consume(family: Family) {
                \definition Data: \Set := \forall (n: R) -> family.Carrier n;
            }",
        )
        .replace(
            r"\structure Sequence {",
            r"\definition makeFamily(P: Chains.Complex): Chains.Family := Chains.Family {
                Carrier := P.family.Carrier, space := P.family.space,
            };
            \structure Sequence {",
        )
        .replace(
            r"\definition sequence: Sequences.Sequence := Sequences.make P p;",
            r"\definition sequence: Sequences.Sequence := Sequences.make P p;
            \import Chains.Consume[family := Sequences.makeFamily P] \as Consumed;
            \definition data: Consumed.Data := p;",
        );
    check(&source).unwrap();
}
