//! Rehome a checked environment, preserving sharing but rechecking declarations.
use crate::{environment::*, ids::*, structure, syntax::*};
use std::collections::HashMap;

#[derive(Debug, Default)]
pub struct Relocation {
    pub stats: TransferStats,
    pub globals: HashMap<GlobalId, GlobalId>,
    pub inductives: HashMap<InductiveId, InductiveId>,
    pub datatypes: HashMap<ProgramInductiveId, ProgramInductiveId>,
    expressions: HashMap<Expression, Expression>,
}

#[derive(Debug, Default, Clone, Copy)]
pub struct TransferStats {
    pub copy_time: std::time::Duration,
    pub check_time: std::time::Duration,
    pub copied_nodes: usize,
    pub declarations: usize,
}

impl Relocation {
    pub fn expression(&self, original: Expression) -> Option<Expression> {
        self.expressions.get(&original).copied()
    }

    fn copy(
        &mut self,
        source: &Arena,
        target: &Arena,
        term: Expression,
    ) -> Result<Expression, String> {
        if let Some(&term) = self.expressions.get(&term) {
            return Ok(term);
        }
        // Iterative postorder avoids using the Rust stack for long term spines.
        let mut pending = vec![(term, false)];
        while let Some((node, ready)) = pending.pop() {
            crate::control::checkpoint();
            if self.expressions.contains_key(&node) {
                continue;
            }
            if !source.owns(node) {
                return Err("source expression belongs to another arena".into());
            }
            if !ready {
                pending.push((node, true));
                structure::visit_children(source, node, |child, _| pending.push((child, false)));
                continue;
            }
            let copied = structure::map_children_into(
                source,
                target,
                node,
                structure::Traversal::All,
                |child, _| Ok(self.expressions[&child]),
            )?;
            let copied =
                structure::remap_references(target, copied, &self.inductives, &self.datatypes);
            self.expressions.insert(node, copied);
        }
        Ok(self.expressions[&term])
    }

    fn context(
        &mut self,
        source: &Arena,
        target: &Arena,
        context: &[Binding],
    ) -> Result<Context, String> {
        context
            .iter()
            .map(|binding| {
                Ok(Binding {
                    var: binding.var,
                    classifier: self.copy(source, target, binding.classifier)?,
                })
            })
            .collect()
    }

    fn definition(
        &mut self,
        source: &Arena,
        target: &Arena,
        definition: &Definition,
    ) -> Result<Definition, String> {
        Ok(Definition {
            context: self.context(source, target, &definition.context)?,
            body: self.copy(source, target, definition.body)?,
            classifier: match definition.classifier {
                Classifier::Expression(ty) => self.copy(source, target, ty)?.into(),
                upper => upper,
            },
        })
    }
}

impl Environment {
    /// The returned environment owns every handle it uses. The source can be
    /// dropped immediately; failure discards the entire destination transaction.
    pub fn transfer(&self) -> Result<(Environment, Relocation), String> {
        let mut target = Environment::new();
        let mut relocation = Relocation::default();
        for declaration in &self.publication_order {
            crate::control::checkpoint();
            match *declaration {
                Declaration::Definition(id) | Declaration::Template(id) => {
                    relocation.globals.insert(id, target.fresh_global_id());
                }
                Declaration::Inductive(id) => {
                    relocation
                        .inductives
                        .insert(id, target.fresh_inductive_id());
                }
                Declaration::Datatype(id) => {
                    relocation.datatypes.insert(id, target.fresh_datatype_id());
                }
                Declaration::Binding(_) => {}
            }
        }
        for declaration in &self.publication_order {
            let source = self.arena();
            let arena = target.arena();
            let copying = std::time::Instant::now();
            macro_rules! check {
                ($operation:expr) => {{
                    relocation.stats.copy_time += copying.elapsed();
                    let checking = std::time::Instant::now();
                    let result = $operation;
                    relocation.stats.check_time += checking.elapsed();
                    result
                }};
            }
            match *declaration {
                Declaration::Binding(level) => {
                    let binding = &self.ambient[level];
                    let binding = Binding {
                        var: binding.var,
                        classifier: relocation.copy(source, arena, binding.classifier)?,
                    };
                    let copied = check!(target.push_binding(binding))?;
                    debug_assert_eq!(copied, level);
                }
                Declaration::Definition(id) | Declaration::Template(id) => {
                    let definition = self
                        .definition(id)
                        .or_else(|| self.definition_template(id))
                        .unwrap();
                    let copied = relocation.definition(source, arena, definition)?;
                    let id = relocation.globals[&id];
                    match declaration {
                        Declaration::Definition(_) => {
                            check!(target.register_definition(id, copied))?
                        }
                        _ => check!(target.register_definition_template(id, copied))?,
                    }
                }
                Declaration::Inductive(id) => {
                    let spec = self.inductive(id).unwrap();
                    let copied = InductiveSpec {
                        parameters: relocation.context(source, arena, &spec.parameters)?,
                        arity: relocation.copy(source, arena, spec.arity)?,
                        constructors: spec
                            .constructors
                            .iter()
                            .map(|&ty| relocation.copy(source, arena, ty))
                            .collect::<Result<_, _>>()?,
                        sort: spec.sort,
                    };
                    check!(target.register_inductive(relocation.inductives[&id], copied))?;
                }
                Declaration::Datatype(id) => {
                    let spec = self.datatype(id).unwrap();
                    let copied = ProgramDatatype {
                        parameters: relocation.context(source, arena, &spec.parameters)?,
                        constructors: spec
                            .constructors
                            .iter()
                            .map(|fields| {
                                fields
                                    .iter()
                                    .map(|&(var, ty)| {
                                        Ok((
                                            var,
                                            relocation
                                                .copy(source, arena, ty.into())?
                                                .try_into()?,
                                        ))
                                    })
                                    .collect::<Result<_, String>>()
                            })
                            .collect::<Result<_, _>>()?,
                        level: spec.level,
                        reflected: relocation.inductives[&spec.reflected],
                    };
                    check!(target.register_datatype(relocation.datatypes[&id], copied))?;
                }
            }
        }
        target.clear_caches();
        relocation.stats.copied_nodes = relocation.expressions.len();
        relocation.stats.declarations = self.publication_order.len();
        Ok((target, relocation))
    }
}
