//! Simultaneous, capture-avoiding instantiation of checked open declarations.
use crate::{calculus, check::Checker, environment::*, ids::GlobalId, syntax::Expression};
use std::collections::HashMap;

impl Environment {
    /// Arguments live in `context`. The template's own local telescope is
    /// appended to it; substitution reaches both body and classifier, including
    /// Program reflection, without introducing any product rule.
    pub fn instantiate_template(
        &mut self,
        id: GlobalId,
        arguments: &HashMap<usize, Expression>,
        context: Context,
    ) -> Result<Definition, String> {
        let template = self
            .definition_template(id)
            .ok_or("unknown declaration template")?
            .clone();
        Checker::new(self, context.clone()).check_context()?;
        let program_context = context
            .first()
            .is_some_and(|b| self.arena().sort(b.classifier).is_program());
        for (&level, &argument) in arguments {
            let binding = self
                .ambient_context()
                .get(level)
                .ok_or("argument outside ambient context")?;
            let classifier = calculus::substitute_ambient(self, binding.classifier, arguments)?;
            let argument_context = if program_context && !self.arena().sort(argument).is_program() {
                crate::reflection::reflect_context(self, &context)?
            } else {
                context.clone()
            };
            Checker::new(self, argument_context).check(argument, classifier)?;
        }
        let substitute = |term: Expression, depth| -> Result<Expression, String> {
            let shifted = arguments
                .iter()
                .map(|(&level, &argument)| {
                    Ok((level, calculus::shift(self.arena(), argument, depth, 0)?))
                })
                .collect::<Result<HashMap<_, _>, String>>()?;
            calculus::substitute_ambient(self, term, &shifted)
        };
        let mut result_context = context;
        for (depth, binding) in template.context.iter().enumerate() {
            result_context.push(Binding {
                var: binding.var,
                classifier: substitute(binding.classifier, depth)?,
            });
        }
        let depth = template.context.len();
        let definition = Definition {
            context: result_context,
            body: substitute(template.body, depth)?,
            classifier: match template.classifier {
                Classifier::Expression(ty) => substitute(ty, depth)?.into(),
                upper => upper,
            },
        };
        self.check_definition(&definition)?;
        Ok(definition)
    }
}
