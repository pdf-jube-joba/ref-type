//! Declaration expansion and reflected views of Program type templates.
use super::*;

impl Resolver {
    pub(super) fn process_declaration(
        &mut self,
        mut item: ModuleItem,
        output: &mut Vec<ModuleItem>,
    ) -> Result<(), Diagnostic> {
        if std::env::var_os("REF_TYPE_PROFILE_RESOLVE").is_some() {
            let name = match &item {
                ModuleItem::Definition { name, .. } | ModuleItem::Structure { name, .. } => {
                    Some(name.as_str())
                }
                _ => None,
            };
            if let Some(name) = name {
                eprintln!(
                    "resolve declaration={}.{}",
                    self.path(self.current).join("."),
                    name
                );
            }
        }
        if let Some(location) = self.location.clone() {
            let source = location
                .source
                .text
                .get(location.span.start..location.span.end)
                .unwrap_or("");
            let declaration = match &item {
                ModuleItem::Structure { name, fields, .. } => Some((
                    name,
                    "structure",
                    fields.iter().map(|(name, _, _)| name).collect::<Vec<_>>(),
                )),
                ModuleItem::Definition {
                    owner: None,
                    name,
                    binders,
                    ty,
                    ..
                } if self.needs_front_definition(binders, ty) => {
                    Some((name, "definition", Vec::new()))
                }
                _ => None,
            };
            if let Some((name, kind, fields)) = declaration
                && !name.as_str().starts_with('<')
            {
                self.declarations.push(Declaration {
                    module: self.path(self.current),
                    name: name.0.clone(),
                    kind,
                    location: location.clone(),
                    ty: Some(source.to_owned()),
                });
                for field in fields {
                    let mut field_location = location.clone();
                    let needle = format!("{}:", field.0);
                    if let Some(offset) = source.find(&needle) {
                        field_location.span.start += offset;
                        field_location.span.end = field_location.span.start + field.0.len();
                    }
                    self.declarations.push(Declaration {
                        module: self.path(self.current),
                        name: format!("{}::{}", name.0, field.0),
                        kind: "field",
                        location: field_location,
                        ty: Some(source.to_owned()),
                    });
                }
            }
        }
        if let ModuleItem::Definition {
            owner: None,
            name,
            binders,
            ty,
            body,
        } = &item
            && self.needs_front_definition(binders, ty)
        {
            return self.compile_structure_definition(
                name.clone(),
                binders.clone(),
                ty.clone(),
                body.clone(),
                output,
            );
        }
        if let ModuleItem::Structure {
            name,
            kind,
            parameters,
            fields,
            field_spans,
        } = item
        {
            if let Some(kind) = kind {
                let defaults = fields.iter().any(|(_, _, default)| default.is_some());
                if defaults {
                    if !matches!(kind, InductiveKind::Pts(syntax::sort::Sort::Prop)) {
                        return Err(self.error(crate::error::Error::Invalid(
                            crate::error::Invalid::DefaultFieldsInASortedStructureRequireProp,
                        )));
                    }
                    self.process_declaration(
                        ModuleItem::Record {
                            type_name: name.clone(),
                            parameters: parameters.clone(),
                            kind,
                            fields: fields
                                .iter()
                                .map(|(name, ty, _)| (name.clone(), ty.clone()))
                                .collect(),
                        },
                        output,
                    )?;
                    let mut preceding = Vec::new();
                    for (field, ty, default) in fields {
                        if let Some(body) = default {
                            self.process_declaration(
                                ModuleItem::Definition {
                                    owner: Some(AssociatedOwner {
                                        type_name: name.clone(),
                                        parameters: parameters.clone(),
                                    }),
                                    name: Identifier(format!("<default:{}>", field.0)),
                                    binders: preceding.clone(),
                                    ty: ty.clone(),
                                    body,
                                },
                                output,
                            )?;
                        }
                        preceding.push(RightBind {
                            vars: vec![field],
                            ty: Box::new(ty),
                        });
                    }
                    return Ok(());
                }
                if let InductiveKind::Pts(sort @ syntax::sort::Sort::Set(_)) = kind {
                    let fields = fields.into_iter().map(|(name, ty, _)| (name, ty)).collect();
                    return self.process_declaration(
                        ModuleItem::SetStructure {
                            name,
                            parameters,
                            sort,
                            fields,
                        },
                        output,
                    );
                }
                let fields = fields.into_iter().map(|(name, ty, _)| (name, ty)).collect();
                return self.process_declaration(
                    ModuleItem::Record {
                        type_name: name,
                        parameters,
                        kind,
                        fields,
                    },
                    output,
                );
            }
            return self.compile_structure(name, parameters, fields, field_spans, output);
        }
        self.item(&mut item)?;
        if matches!(
            item,
            ModuleItem::MathMacro { .. } | ModuleItem::UserMacro { .. }
        ) {
            return Ok(());
        }
        if matches!(item, ModuleItem::UseMacro { .. }) {
            let Some(import) = self.pending_macro_import.take() else {
                return Ok(());
            };
            item = import;
        }
        if !matches!(item, ModuleItem::ChildModule { .. }) {
            self.order.push(CheckStep::Declaration {
                module: self.current,
                index: *self.declaration_counts.entry(self.current).or_default(),
            });
        }
        *self.declaration_counts.entry(self.current).or_default() += 1;
        output.push(item);
        Ok(())
    }

    pub(super) fn reflect_type(&self, ty: SExp) -> Result<SExp, Diagnostic> {
        Ok(match ty {
            SExp::Checked { checks, body } => SExp::Checked {
                checks,
                body: Box::new(self.reflect_type(*body)?),
            },
            SExp::AccessPath {
                mut access,
                parameters,
            } => {
                let name = match &mut access {
                    LocalAccess::Current { access, .. } | LocalAccess::Resolved { access, .. } => {
                        access
                    }
                    LocalAccess::Named { child, .. } => child,
                    LocalAccess::Instantiated { child, .. } => child,
                };
                name.0.push('^');
                SExp::AccessPath {
                    access,
                    parameters: parameters
                        .into_iter()
                        .map(|p| self.reflect_type(p))
                        .collect::<Result<_, _>>()?,
                }
            }
            SExp::ThunkType { computation_ty } => self.reflect_type(*computation_ty)?,
            SExp::ReturnType { value_ty } => self.reflect_type(*value_ty)?,
            SExp::ComputationFunction { domain, codomain } => SExp::Prod {
                bind: Bind::Named(RightBind {
                    vars: vec![Identifier("_".into())],
                    ty: Box::new(self.reflect_type(*domain)?),
                }),
                body: Box::new(self.reflect_type(*codomain)?),
            },
            SExp::Prod {
                bind: Bind::Named(mut bind),
                body,
            } => {
                bind.ty = Box::new(self.reflect_type(*bind.ty)?);
                SExp::Prod {
                    bind: Bind::Named(bind),
                    body: Box::new(self.reflect_type(*body)?),
                }
            }
            SExp::RunStep {
                state_ty,
                result_ty,
            } => SExp::RunStep {
                state_ty: Box::new(self.reflect_type(*state_ty)?),
                result_ty: Box::new(self.reflect_type(*result_ty)?),
            },
            SExp::Meta { .. } => {
                return Err(self.error(crate::error::Error::Invalid(
                    crate::error::Invalid::BundleProgramTypesRequireAnExplicitType,
                )));
            }
            _ => {
                return Err(self.error(crate::error::Error::Invalid(
                    crate::error::Invalid::ExpectedProgramTypeInBundle,
                )));
            }
        })
    }
}
