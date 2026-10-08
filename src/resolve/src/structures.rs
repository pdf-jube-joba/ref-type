//! Structure signatures share the module telescope checker, while their
//! public bindings denote frontend declarations rather than kernel terms.
use super::*;

#[path = "structures/declarations.rs"]
mod declarations;
#[path = "structures/existence.rs"]
mod existence;
#[path = "structures/normalization.rs"]
mod normalization;
#[path = "structures/parameters.rs"]
mod parameters;

#[derive(Clone)]
pub(super) struct Structure {
    pub ambient: HashMap<BindingId, SExp>,
    pub parameters: Vec<RightBind>,
    pub inputs: Vec<Input>,
    pub checks: Vec<(SExp, SExp)>,
    pub fields: Vec<(Identifier, SExp, Option<SExp>)>,
}

#[derive(Clone)]
pub(super) struct ParameterSignature {
    pub parameters: Vec<RightBind>,
    pub inputs: Vec<Input>,
    pub checks: Vec<(SExp, SExp)>,
}

#[derive(Clone)]
pub(super) struct Value {
    pub arguments: HashMap<BindingId, SExp>,
    pub signature: BindingId,
    pub parameters: Vec<RightBind>,
    pub fields: Vec<(String, SExp)>,
    pub inputs: Vec<Input>,
    pub checks: Vec<(SExp, SExp)>,
}

#[derive(Clone)]
pub(super) struct Definition {
    pub parameters: Vec<RightBind>,
    pub inputs: Vec<Input>,
    pub ty: SExp,
    pub body: SExp,
}

#[derive(Clone)]
pub(super) struct Input {
    pub callback_parameters: Vec<RightBind>,
    pub arguments: HashMap<BindingId, SExp>,
    pub name: String,
    pub callback: bool,
    pub signature: Option<BindingId>,
    pub fields: Vec<String>,
    pub computation: bool,
    pub thunks: HashSet<String>,
}

pub(super) fn variable(name: Identifier) -> SExp {
    SExp::AccessPath {
        access: LocalAccess::Current {
            span: SourceSpan::default(),
            access: name,
        },
        parameters: Vec::new(),
    }
}

fn ordered_arguments(values: &HashMap<BindingId, SExp>) -> Vec<(BindingId, SExp)> {
    let mut values: Vec<_> = values
        .iter()
        .map(|(id, value)| (*id, value.clone()))
        .collect();
    values.sort_by_key(|(id, _)| *id);
    values
}

pub(in crate::resolver) fn substitute(
    expression: &SExp,
    values: &HashMap<BindingId, SExp>,
) -> SExp {
    let mut expression = expression.clone();
    macros::walk_sexp_control(&mut expression, &mut |node| {
        if let SExp::AccessPath {
            access:
                LocalAccess::Named {
                    access,
                    child,
                    span,
                },
            parameters,
        } = node
            && let Some(value) = access.1.and_then(|id| values.get(&id))
        {
            *node = SExp::MemberAccess {
                base: Box::new(value.clone()),
                field: child.clone(),
                parameters: parameters.clone(),
                span: *span,
            };
            return false;
        }
        if let SExp::ProgramValueReference {
            access: LocalAccess::Current { access, .. } | LocalAccess::Resolved { access, .. },
        } = node
            && let Some(value) = access.1.and_then(|id| values.get(&id))
        {
            *node = value.clone();
            return false;
        }
        if let SExp::AccessPath {
            access: LocalAccess::Current { access, .. } | LocalAccess::Resolved { access, .. },
            parameters,
        } = node
            && parameters.is_empty()
            && let Some(value) = access.1.and_then(|id| values.get(&id))
        {
            *node = if access.as_str().ends_with('^') {
                SExp::ReflectTerm {
                    expression: Box::new(value.clone()),
                }
            } else {
                value.clone()
            };
            return false;
        }
        true
    });
    expression
}

fn abstract_parameters(parameters: &[RightBind], mut expression: SExp) -> SExp {
    for bind in parameters.iter().rev() {
        expression = SExp::Lam {
            bind: Bind::Named(bind.clone()),
            body: Box::new(expression),
        };
    }
    let local_ids: HashSet<_> = parameters
        .iter()
        .flat_map(|bind| bind.vars.iter())
        .filter_map(|name| name.1)
        .collect();
    macros::walk_sexp_mut(&mut expression, &mut |node| {
        if let SExp::AccessPath { access, .. } | SExp::ProgramValueReference { access } = node
            && let LocalAccess::Resolved {
                access: name, span, ..
            } = access
            && name.1.is_some_and(|id| local_ids.contains(&id))
        {
            *access = LocalAccess::Current {
                access: name.clone(),
                span: *span,
            };
        }
    });
    expression
}

fn computation_type(ty: &SExp) -> bool {
    matches!(
        ty,
        SExp::ReturnType { .. } | SExp::ComputationFunction { .. }
    )
}
fn thunk(value: SExp) -> SExp {
    SExp::Thunk {
        computation: Box::new(value),
    }
}
fn force_reference(name: Identifier) -> SExp {
    SExp::Force {
        value: Box::new(SExp::ProgramValueReference {
            access: LocalAccess::Current {
                access: name,
                span: SourceSpan::default(),
            },
        }),
    }
}

impl Resolver {
    pub(super) fn front_binding(
        &self,
        access: &LocalAccess,
        locals: &[HashMap<String, Identifier>],
    ) -> Option<BindingId> {
        if let LocalAccess::Current { access: name, .. }
        | LocalAccess::Resolved { access: name, .. } = access
            && name.1.is_some()
        {
            return name.1;
        }
        if let LocalAccess::Current { access: name, .. } = access
            && let Some(name) = locals.iter().rev().find_map(|s| s.get(name.as_str()))
        {
            return name.1;
        }
        let mut access = access.clone();
        self.access(self.current, &mut access).ok()?;
        match access {
            LocalAccess::Current { access, .. } | LocalAccess::Resolved { access, .. } => access.1,
            LocalAccess::Named { .. } | LocalAccess::Instantiated { .. } => None,
        }
    }

    fn instantiate_front_expression(&self, expression: &SExp, access: &LocalAccess) -> SExp {
        let mut resolved = access.clone();
        let module = if self.access(self.current, &mut resolved).is_ok()
            && let LocalAccess::Resolved { module, .. } = resolved
        {
            module
        } else {
            self.current
        };
        let scope = &self.scopes[module.0 as usize];
        let mut expression = substitute(expression, &scope.substitutions);
        macros::walk_sexp_mut(&mut expression, &mut |node| {
            let module = match node {
                SExp::ProgramValueReference {
                    access: LocalAccess::Resolved { module, .. },
                }
                | SExp::AccessPath {
                    access: LocalAccess::Resolved { module, .. },
                    ..
                }
                | SExp::RecordTypeCtor {
                    access: LocalAccess::Resolved { module, .. },
                    ..
                }
                | SExp::IndCase {
                    path: LocalAccess::Resolved { module, .. },
                    ..
                }
                | SExp::ProgramCase {
                    path: LocalAccess::Resolved { module, .. },
                    ..
                } => Some(module),
                _ => None,
            };
            if let Some(module) = module {
                *module = scope.remapping.get(module).copied().unwrap_or(*module);
            }
        });
        expression
    }

    fn instantiate_input(&self, input: &mut Input, access: &LocalAccess) {
        for argument in input.arguments.values_mut() {
            *argument = self.instantiate_front_expression(argument, access);
        }
        for bind in &mut input.callback_parameters {
            *bind.ty = self.instantiate_front_expression(&bind.ty, access);
        }
    }

    fn structure_type(
        &self,
        expression: &SExp,
        locals: &[HashMap<String, Identifier>],
    ) -> Result<Option<(BindingId, Structure, HashMap<BindingId, SExp>)>, Diagnostic> {
        let SExp::AccessPath { access, parameters } = expression else {
            return Ok(None);
        };
        let Some(mut signature) = self
            .front_binding(access, locals)
            .and_then(|id| self.structures.get(&id))
            .cloned()
        else {
            return Ok(None);
        };
        let id = self.front_binding(access, locals).unwrap();
        for bind in &mut signature.parameters {
            *bind.ty = self.instantiate_front_expression(&bind.ty, access);
        }
        for (_, ty, default) in &mut signature.fields {
            *ty = self.instantiate_front_expression(ty, access);
            if let Some(body) = default {
                *body = self.instantiate_front_expression(body, access);
            }
        }
        for (value, ty) in &mut signature.checks {
            *value = self.instantiate_front_expression(value, access);
            *ty = self.instantiate_front_expression(ty, access);
        }
        let (parameters, checks) = self.expand_type_arguments(
            &signature.parameters,
            &signature.inputs,
            parameters,
            access,
            locals,
        )?;
        signature.checks.extend(checks);
        let names = signature
            .parameters
            .iter()
            .flat_map(|b| &b.vars)
            .collect::<Vec<_>>();
        let mut substitutions: HashMap<_, _> = names
            .into_iter()
            .zip(parameters)
            .map(|(n, v)| (n.1.unwrap(), v))
            .collect();
        for (id, expression) in &signature.ambient {
            substitutions.insert(*id, self.instantiate_front_expression(expression, access));
        }
        Ok(Some((id, signature, substitutions)))
    }

    fn bind_structure_field(
        &self,
        field: BindingId,
        value: SExp,
        substitutions: &mut HashMap<BindingId, SExp>,
    ) -> Result<(), Diagnostic> {
        if let Some(abstract_value) = self.structure_values.get(&field)
            && let Some(actual) = self.structure_value(&value, &[])?
        {
            for (name, expression) in &abstract_value.fields {
                if let SExp::AccessPath {
                    access: LocalAccess::Current { access, .. },
                    ..
                } = expression
                    && let Some(id) = access.1
                    && let Some((_, expression)) =
                        actual.fields.iter().find(|(path, _)| path == name)
                {
                    substitutions.insert(id, expression.clone());
                }
                if let SExp::Force { value } = expression
                    && let SExp::ProgramValueReference {
                        access: LocalAccess::Current { access, .. },
                    } = value.as_ref()
                    && let Some(id) = access.1
                    && let Some((_, expression)) =
                        actual.fields.iter().find(|(path, _)| path == name)
                {
                    substitutions.insert(id, thunk(expression.clone()));
                }
            }
        }
        substitutions.insert(
            field,
            if self.computation_bindings.contains(&field) {
                thunk(value)
            } else {
                value
            },
        );
        Ok(())
    }

    fn signature_checks(
        &self,
        shape: &Structure,
        arguments: &HashMap<BindingId, SExp>,
    ) -> Vec<(SExp, SExp)> {
        shape
            .parameters
            .iter()
            .flat_map(|bind| {
                bind.vars.iter().map(|name| {
                    (
                        arguments[&name.1.unwrap()].clone(),
                        substitute(&bind.ty, arguments),
                    )
                })
            })
            .chain(
                shape
                    .checks
                    .iter()
                    .map(|(value, ty)| (substitute(value, arguments), substitute(ty, arguments))),
            )
            .collect()
    }

    fn structure_value(
        &self,
        expression: &SExp,
        locals: &[HashMap<String, Identifier>],
    ) -> Result<Option<Value>, Diagnostic> {
        // Inline module selection preserves argument checks around its value.
        // A structure still denotes its fields inside that wrapper; retain all
        // guards so declaration compilation checks the selected instance too.
        if let SExp::Checked { checks, body } = expression {
            let mut value = self.structure_value(body, locals)?;
            if let Some(value) = &mut value {
                value.checks.extend(checks.iter().cloned());
            }
            return Ok(value);
        }
        let projection = match expression {
            SExp::InferredProjection { value, field, .. } => Some(((**value).clone(), field)),
            SExp::MemberAccess {
                base,
                field,
                parameters,
                ..
            } if parameters.is_empty() => Some(((**base).clone(), field)),
            SExp::AccessPath {
                access: LocalAccess::Named { access, child, .. },
                parameters,
            } if parameters.is_empty() => Some((variable(access.clone()), child)),
            _ => None,
        };
        if let Some((base, field)) = projection
            && let Some(value) = self.structure_value(&base, locals)?
            && let Some((_, field_value)) = value
                .fields
                .iter()
                .find(|(name, _)| name == field.as_str().trim_end_matches('^'))
        {
            let mut result = self.structure_value(field_value, locals)?;
            if let Some(result) = &mut result {
                result.checks.extend(value.checks);
            }
            return Ok(result);
        }
        let mut head = expression;
        let mut arguments = Vec::new();
        while let SExp::App { func, arg } = head {
            arguments.push((**arg).clone());
            head = func;
        }
        arguments.reverse();
        if let SExp::AccessPath { access, parameters } = head
            && let Some(id) = self.front_binding(access, locals)
            && let Some(template) = self.structure_values.get(&id)
        {
            let mut template = template.clone();
            for input in &mut template.inputs {
                self.instantiate_input(input, access);
            }
            for expression in template.arguments.values_mut() {
                *expression = self.instantiate_front_expression(expression, access);
            }
            for bind in &mut template.parameters {
                *bind.ty = self.instantiate_front_expression(&bind.ty, access);
            }
            for (_, expression) in &mut template.fields {
                *expression = self.instantiate_front_expression(expression, access);
            }
            for (value, ty) in &mut template.checks {
                *value = self.instantiate_front_expression(value, access);
                *ty = self.instantiate_front_expression(ty, access);
            }
            let mut supplied = parameters.clone();
            supplied.extend(arguments);
            if supplied.len() > template.inputs.len() {
                return Err(self.error("structure declaration argument count mismatch"));
            }
            let supplied_count = supplied.len();
            let mut actual = Vec::new();
            let mut checks = Vec::new();
            for (input, argument) in template.inputs.iter().zip(supplied) {
                if input.signature.is_some() {
                    let (fields, guards) = self.callback_arguments(input, &argument, locals)?;
                    checks.extend(guards);
                    actual.extend(fields);
                } else {
                    actual.push(if input.computation {
                        thunk(argument)
                    } else {
                        argument
                    });
                }
            }
            let consumed = actual.len();
            let mut substitutions = HashMap::new();
            for (bind, value) in template.parameters.iter().zip(actual) {
                let ty = substitute(&bind.ty, &substitutions);
                checks.push((value.clone(), ty));
                substitutions.insert(bind.vars[0].1.unwrap(), value);
            }
            checks = checks
                .into_iter()
                .map(|(value, ty)| {
                    (
                        substitute(&value, &substitutions),
                        substitute(&ty, &substitutions),
                    )
                })
                .collect();
            checks.extend(template.checks.iter().map(|(value, ty)| {
                (
                    substitute(value, &substitutions),
                    substitute(ty, &substitutions),
                )
            }));
            return Ok(Some(Value {
                arguments: template
                    .arguments
                    .iter()
                    .map(|(id, expression)| (*id, substitute(expression, &substitutions)))
                    .collect(),
                signature: template.signature,
                parameters: template
                    .parameters
                    .iter()
                    .skip(consumed)
                    .map(|bind| RightBind {
                        vars: bind.vars.clone(),
                        ty: Box::new(substitute(&bind.ty, &substitutions)),
                    })
                    .collect(),
                inputs: template.inputs.into_iter().skip(supplied_count).collect(),
                checks,
                fields: template
                    .fields
                    .iter()
                    .map(|(name, value)| (name.clone(), substitute(value, &substitutions)))
                    .collect(),
            }));
        }
        match expression {
            SExp::RecordTypeCtor {
                access,
                parameters,
                fields,
            } => {
                let ty = SExp::AccessPath {
                    access: access.clone(),
                    parameters: parameters.clone(),
                };
                let Some((signature, shape, mut substitutions)) =
                    self.structure_type(&ty, locals)?
                else {
                    return Ok(None);
                };
                let mut supplied = HashMap::new();
                for (name, value) in fields {
                    if supplied.insert(name.0.clone(), value.clone()).is_some() {
                        return Err(self.error(format!("duplicate structure field: {}", name.0)));
                    }
                }
                let mut result = Vec::new();
                let mut checks = self.signature_checks(&shape, &substitutions);
                for (name, ty, default) in &shape.fields {
                    let value = supplied
                        .remove(&name.0)
                        .or_else(|| default.as_ref().map(|v| substitute(v, &substitutions)))
                        .ok_or_else(|| {
                            self.error(format!("missing structure field: {}", name.0))
                        })?;
                    let expected = substitute(ty, &substitutions);
                    if let Some((signature, _, _)) = self.structure_type(&expected, locals)? {
                        let nested = self
                            .structure_value(&value, locals)?
                            .filter(|value| value.signature == signature)
                            .ok_or_else(|| {
                                self.error("nested field does not satisfy structure signature")
                            })?;
                        checks.extend(nested.checks);
                        for (id, expected) in
                            ordered_arguments(&self.structure_type(&expected, locals)?.unwrap().2)
                        {
                            if let Some(actual) = nested.arguments.get(&id) {
                                checks.push((
                                    actual.clone(),
                                    SExp::ConversionTarget {
                                        expression: Box::new(expected),
                                    },
                                ));
                            }
                        }
                        result.extend(nested.fields.into_iter().map(|(path, expression)| {
                            (format!("{}.{}", name.0, path), expression)
                        }));
                    } else {
                        checks.push((value.clone(), expected));
                    }
                    let value = if self
                        .structure_type(&substitute(ty, &substitutions), locals)?
                        .is_some()
                        || matches!(ty, SExp::ValueType)
                    {
                        value
                    } else {
                        let expected = checks.last().unwrap().1.clone();
                        SExp::Ascribe {
                            term: Box::new(value),
                            ty: Box::new(expected),
                        }
                    };
                    self.bind_structure_field(name.1.unwrap(), value.clone(), &mut substitutions)?;
                    result.push((name.0.clone(), value));
                }
                if !supplied.is_empty() {
                    return Err(self.error("unknown structure field"));
                }
                Ok(Some(Value {
                    arguments: self.structure_type(&ty, locals)?.unwrap().2,
                    signature,
                    parameters: Vec::new(),
                    fields: result,
                    inputs: Vec::new(),
                    checks,
                }))
            }
            _ => Ok(None),
        }
    }
}
