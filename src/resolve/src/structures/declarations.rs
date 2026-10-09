use super::*;

impl Resolver {
    pub(in crate::resolver) fn needs_front_definition(
        &self,
        binders: &[RightBind],
        ty: &SExp,
    ) -> bool {
        self.is_structure_type(ty)
            || self.declaration_signature(ty).is_some()
            || matches!(ty, SExp::ValueType)
            || binders.iter().any(|bind| {
                self.is_structure_type(&bind.ty)
                    || self.declaration_signature(&bind.ty).is_some()
                    || matches!(bind.ty.as_ref(), SExp::ValueType)
                    || computation_type(&bind.ty)
            })
    }

    pub(in crate::resolver) fn is_structure_type(&self, ty: &SExp) -> bool {
        matches!(ty, SExp::AccessPath { access, .. }
            if self.front_binding(access, &[]).is_some_and(|id| self.structures.contains_key(&id)))
    }

    pub(in crate::resolver) fn compile_structure_definition(
        &mut self,
        mut name: Identifier,
        binders: Vec<RightBind>,
        mut ty: SExp,
        mut body: SExp,
        output: &mut Vec<ModuleItem>,
    ) -> Result<(), Diagnostic> {
        let mut binders = binders;
        // Generated declaration modules must retain the source module's paths.
        for binder in &mut binders {
            self.anchor_module_expressions(&mut binder.ty)?;
        }
        self.anchor_module_expressions(&mut ty)?;
        self.anchor_module_expressions(&mut body)?;
        if let Some((domain, result)) = self.declaration_signature(&ty) {
            for bind in &domain {
                for name in &bind.vars {
                    body = SExp::App {
                        func: Box::new(body),
                        arg: Box::new(variable(name.clone())),
                    };
                }
            }
            binders.extend(domain);
            ty = result;
        }
        let location = self.location.clone();
        let span = location.as_ref().map_or(SourceSpan::default(), |l| l.span);
        let parent = self.current;
        let mut module = Module {
            id: ModuleId::default(),
            name: Identifier(format!("<definition:{}>", name.0)),
            parameter_sources: binders
                .iter()
                .flat_map(|bind| &bind.vars)
                .map(|parameter| {
                    (
                        parameter.0.clone(),
                        ParameterSource {
                            subject: ParameterSubject::DefinitionParameter {
                                definition: name.0.clone(),
                                name: parameter.0.clone(),
                            },
                            span,
                        },
                    )
                })
                .collect(),
            parameters: binders,
            parameter_checks: Vec::new(),
            declaration_spans: Vec::new(),
            body: ModuleBody::Inline(Vec::new()),
            span,
            source: location.as_ref().map(|l| l.source.clone()),
            header_source: location.as_ref().map(|l| l.source.clone()),
        };
        self.reserve(parent, &mut module);
        self.module(module.id)?;
        self.current = module.id;
        self.location = location.clone();
        self.expression(&mut ty, &mut Vec::new())?;
        self.expression(&mut body, &mut Vec::new())?;
        if !self.is_structure_type(&ty) {
            let item = if matches!(ty, SExp::ValueType) {
                ModuleItem::ValueTypeCheck {
                    ty: body.clone().try_into().map_err(|e| self.error(e))?,
                }
            } else {
                ModuleItem::Definition {
                    owner: None,
                    name: Identifier("<body>".into()),
                    binders: Vec::new(),
                    ty: ty.clone(),
                    body: body.clone(),
                }
            };
            let mut items = Vec::new();
            self.scoped_item(item, &mut items)?;
            let checked = self.output.get_mut(&module.id).unwrap();
            checked.declaration_spans = vec![span; items.len()];
            checked.body = ModuleBody::Inline(items);
            let parameters = checked.parameters.clone();
            let bindings = parameters
                .iter()
                .flat_map(|bind| &bind.vars)
                .filter_map(|name| name.1)
                .collect();
            self.expose_namespace_arguments(&mut body, &bindings);
            self.expose_namespace_arguments(&mut ty, &bindings);
            let definition = Definition {
                parameters,
                inputs: self.module_inputs[&module.id].clone(),
                ty,
                body,
            };
            self.current = parent;
            self.location = location;
            self.publish(&mut name);
            self.front_definitions.insert(name.1.unwrap(), definition);
            output.push(ModuleItem::ChildModule {
                module: Box::new(module),
            });
            return Ok(());
        }
        let (signature, shape, mut substitutions) =
            self.structure_type(&ty, &[])?.ok_or_else(|| {
                self.error(crate::error::Error::Invalid(
                    crate::error::Invalid::ExpectedAStructureResultSignature,
                ))
            })?;
        let mut value = self
            .structure_value(&body, &[])?
            .filter(|value| value.signature == signature)
            .ok_or_else(|| {
                self.error(crate::error::Error::Invalid(
                    crate::error::Invalid::DefinitionDoesNotSatisfyStructureResultSignature,
                ))
            })?;
        let mut checked_items = Vec::new();
        for (value, ty) in &value.checks {
            self.scoped_item(
                ModuleItem::MemberCheck {
                    value: value.clone(),
                    ty: ty.clone(),
                },
                &mut checked_items,
            )?;
        }
        for (id, expected) in ordered_arguments(&substitutions) {
            let actual = value
                .arguments
                .get(&id)
                .ok_or_else(|| {
                    self.error(crate::error::Error::Invalid(
                        crate::error::Invalid::StructureSignatureParameterMismatch,
                    ))
                })?
                .clone();
            self.scoped_item(
                ModuleItem::MemberCheck {
                    value: actual,
                    ty: SExp::ConversionTarget {
                        expression: Box::new(expected.clone()),
                    },
                },
                &mut checked_items,
            )?;
        }
        for (value, ty) in self.signature_checks(&shape, &substitutions) {
            self.scoped_item(ModuleItem::MemberCheck { value, ty }, &mut checked_items)?;
        }
        for (field, expected, _) in &shape.fields {
            let expression = value
                .fields
                .iter()
                .find(|(name, _)| name == field.as_str().trim_end_matches('^'))
                .unwrap()
                .1
                .clone();
            let expected = substitute(expected, &substitutions);
            if self.structure_type(&expected, &[])?.is_some() {
                let nested = self.structure_value(&expression, &[])?.ok_or_else(|| {
                    self.error(crate::error::Error::Invalid(
                        crate::error::Invalid::ExpectedNestedStructure,
                    ))
                })?;
                for (value, ty) in nested.checks {
                    self.scoped_item(
                        ModuleItem::MemberCheck {
                            value: value.clone(),
                            ty: ty.clone(),
                        },
                        &mut checked_items,
                    )?;
                }
                self.bind_structure_field(field.1.unwrap(), expression, &mut substitutions)?;
                continue;
            }
            let item = if matches!(expected, SExp::ValueType) {
                ModuleItem::ValueTypeCheck {
                    ty: expression.clone().try_into().map_err(|e| self.error(e))?,
                }
            } else {
                ModuleItem::MemberCheck {
                    value: expression.clone(),
                    ty: expected,
                }
            };
            self.scoped_item(item, &mut checked_items)?;
            self.bind_structure_field(field.1.unwrap(), expression, &mut substitutions)?;
        }
        let checked = self.output.get_mut(&module.id).unwrap();
        checked.declaration_spans = vec![span; checked_items.len()];
        checked.body = ModuleBody::Inline(checked_items);
        value.parameters = checked.parameters.clone();
        value.inputs = self.module_inputs[&module.id].clone();
        value.checks.clear();
        let bindings = value
            .parameters
            .iter()
            .flat_map(|bind| &bind.vars)
            .filter_map(|name| name.1)
            .collect();
        for (_, field) in &mut value.fields {
            self.expose_namespace_arguments(field, &bindings);
        }
        for argument in value.arguments.values_mut() {
            self.expose_namespace_arguments(argument, &bindings);
        }
        self.current = parent;
        self.location = location;
        self.publish(&mut name);
        self.structure_values.insert(name.1.unwrap(), value);
        output.push(ModuleItem::ChildModule {
            module: Box::new(module),
        });
        Ok(())
    }

    pub(in crate::resolver) fn compile_structure(
        &mut self,
        mut name: Identifier,
        parameters: Vec<RightBind>,
        fields: Vec<(Identifier, SExp, Option<SExp>)>,
        field_spans: Vec<SourceSpan>,
        output: &mut Vec<ModuleItem>,
    ) -> Result<(), Diagnostic> {
        let location = self.location.clone();
        let span = location.as_ref().map_or(SourceSpan::default(), |l| l.span);
        let mut telescope = parameters.clone();
        let mut parameter_sources: HashMap<_, _> = parameters
            .iter()
            .flat_map(|bind| &bind.vars)
            .map(|parameter| {
                (
                    parameter.0.clone(),
                    ParameterSource {
                        subject: ParameterSubject::StructureParameter {
                            structure: name.0.clone(),
                            name: parameter.0.clone(),
                        },
                        span,
                    },
                )
            })
            .collect();
        parameter_sources.extend(fields.iter().enumerate().map(|(index, (field, _, _))| {
            (
                field.0.clone(),
                ParameterSource {
                    subject: ParameterSubject::StructureField {
                        structure: name.0.clone(),
                        name: field.0.clone(),
                    },
                    span: field_spans.get(index).copied().unwrap_or(span),
                },
            )
        }));
        for (field, ty, _) in &fields {
            telescope.push(RightBind {
                vars: vec![field.clone()],
                ty: Box::new(ty.clone()),
            });
        }
        let mut module = Module {
            id: ModuleId::default(),
            name: Identifier(format!("<structure:{}>", name.as_str())),
            parameters: telescope,
            parameter_checks: Vec::new(),
            parameter_sources,
            declaration_spans: Vec::new(),
            body: ModuleBody::Inline(Vec::new()),
            span,
            source: location.as_ref().map(|l| l.source.clone()),
            header_source: location.as_ref().map(|l| l.source.clone()),
        };
        self.reserve(self.current, &mut module);
        self.module(module.id)?;
        self.location = location;
        let mut field_scope = Vec::new();
        let mut checked_fields = fields;
        let mut checked_parameters = parameters;
        self.parameters(&mut checked_parameters, &mut field_scope, false)?;
        let inputs = self.last_inputs.clone();
        let checks = self.last_parameter_checks.clone();
        for (field, ty, default) in &mut checked_fields {
            self.expression(ty, &mut field_scope)?;
            if let Some(body) = default {
                self.expression(body, &mut field_scope)?;
            }
            let mut declaration = vec![RightBind {
                vars: vec![field.clone()],
                ty: Box::new(ty.clone()),
            }];
            self.parameters(&mut declaration, &mut field_scope, false)?;
            *field = field_scope
                .iter()
                .rev()
                .find_map(|scope| scope.get(field.as_str()))
                .unwrap()
                .clone();
        }
        let local_ids: HashSet<_> = field_scope
            .iter()
            .flat_map(|scope| scope.values())
            .filter_map(|name| name.1)
            .collect();
        let unresolve = |expression: &SExp| {
            let mut expression = expression.clone();
            macros::walk_sexp_mut(&mut expression, &mut |node| {
                if let SExp::AccessPath {
                    access: LocalAccess::Current { access, .. },
                    ..
                }
                | SExp::ProgramValueReference {
                    access: LocalAccess::Current { access, .. },
                } = node
                    && access.1.is_some_and(|id| local_ids.contains(&id))
                {
                    access.1 = None;
                }
            });
            expression
        };
        let mut defaults = HashMap::new();
        let mut required = checked_parameters
            .iter()
            .map(|bind| RightBind {
                vars: bind
                    .vars
                    .iter()
                    .map(|name| Identifier(name.0.clone()))
                    .collect(),
                ty: Box::new(unresolve(&bind.ty)),
            })
            .collect::<Vec<_>>();
        for (field, ty, default) in &checked_fields {
            let ty = substitute(ty, &defaults);
            if let Some(body) = default {
                let body = substitute(body, &defaults);
                let item = if self.is_structure_type(&ty) {
                    ModuleItem::Definition {
                        owner: None,
                        name: Identifier("<default>".into()),
                        binders: Vec::new(),
                        ty: unresolve(&ty),
                        body: unresolve(&body),
                    }
                } else {
                    ModuleItem::MemberCheck {
                        value: unresolve(&body),
                        ty: unresolve(&ty),
                    }
                };
                let mut checker = Module {
                    id: ModuleId::default(),
                    name: Identifier(format!("<default:{}.{}>", name.0, field.0)),
                    parameters: required.clone(),
                    parameter_checks: Vec::new(),
                    parameter_sources: module.parameter_sources.clone(),
                    declaration_spans: vec![span],
                    body: ModuleBody::Inline(vec![item]),
                    span,
                    source: module.source.clone(),
                    header_source: module.header_source.clone(),
                };
                self.reserve(self.current, &mut checker);
                self.module(checker.id)?;
                self.location = module.source.as_ref().map(|source| SourceLocation {
                    source: source.clone(),
                    span,
                });
                output.push(ModuleItem::ChildModule {
                    module: Box::new(checker),
                });
                let body = if self.is_structure_type(&ty) || matches!(ty, SExp::ValueType) {
                    body
                } else {
                    SExp::Ascribe {
                        term: Box::new(body),
                        ty: Box::new(ty),
                    }
                };
                self.bind_structure_field(field.1.unwrap(), body, &mut defaults)?;
            } else {
                required.push(RightBind {
                    vars: vec![Identifier(field.0.clone())],
                    ty: Box::new(unresolve(&ty)),
                });
            }
        }
        let mut ambient = HashMap::new();
        let mut owner = Some(self.current);
        while let Some(module) = owner {
            if let Some(parameters) = self.module_parameters.get(&module) {
                for name in parameters.iter().flat_map(|bind| &bind.vars) {
                    if let Some(id) = name.1 {
                        ambient.insert(
                            id,
                            SExp::AccessPath {
                                access: LocalAccess::Resolved {
                                    module,
                                    access: name.clone(),
                                    display: name.0.clone(),
                                    span: SourceSpan::default(),
                                },
                                parameters: Vec::new(),
                            },
                        );
                    }
                }
            }
            owner = self.scopes[module.0 as usize].parent;
        }
        self.publish(&mut name);
        self.structures.insert(
            name.1.unwrap(),
            Structure {
                ambient,
                parameters: checked_parameters,
                inputs,
                checks,
                fields: checked_fields,
            },
        );
        output.push(ModuleItem::ChildModule {
            module: Box::new(module),
        });
        Ok(())
    }
}
