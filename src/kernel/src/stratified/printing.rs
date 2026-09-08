//! Diagnostic rendering includes syntax family, sort index, and product labels.
use super::{environment::Environment, syntax::*};

pub fn format_expression(env: &Environment, expression: impl Into<Expression>) -> String {
    fn render(
        arena: &Arena,
        expression: Expression,
        depth: usize,
        remaining: &mut usize,
    ) -> String {
        if *remaining == 0 {
            return "…".into();
        }
        *remaining -= 1;
        let data = arena.data(expression);
        if depth == 0 {
            return format!("{:?}@{:?}", expression.family(), data.sort);
        }
        let fields = data
            .fields
            .iter()
            .map(|field| {
                field
                    .iter()
                    .map(|child| render(arena, child.expression, depth - 1, remaining))
                    .collect::<Vec<_>>()
                    .join(", ")
            })
            .collect::<Vec<_>>()
            .join("; ");
        format!("{:?}@{:?}({fields})", data.op, data.sort)
    }
    render(&env.arena, expression.into(), 6, &mut 128)
}
