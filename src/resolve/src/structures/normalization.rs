use super::*;

impl Resolver {
    fn is_declaration_lambda(&self, expression: &SExp) -> bool {
        match expression {
            SExp::Lam {
                bind: Bind::Named(bind),
                body,
            } => {
                self.is_structure_type(&bind.ty)
                    || self.declaration_signature(&bind.ty).is_some()
                    || self.is_declaration_lambda(body)
            }
            SExp::Block(block) => block
                .as_term()
                .is_ok_and(|body| self.is_declaration_lambda(&body)),
            SExp::Checked { body, .. } => self.is_declaration_lambda(body),
            SExp::MemberLiteral { ty, .. } => self.is_structure_type(ty),
            SExp::RecordTypeCtor { access, .. } => self
                .front_binding(access, &[])
                .is_some_and(|id| self.structures.contains_key(&id)),
            SExp::App { func, .. } => self.is_declaration_lambda(func),
            SExp::AccessPath { access, .. } => self
                .front_binding(access, &[])
                .is_some_and(|id| self.structure_values.contains_key(&id)),
            _ => false,
        }
    }

    fn apply_declaration_lambda(
        &mut self,
        function: &SExp,
        argument: &SExp,
        locals: &[LocalScope],
    ) -> Result<SExp, Diagnostic> {
        // Give inserted arguments and lambda binders distinct lexical identities.
        let mut function = function.clone();
        macros::rename_template_binders(&mut function, self.fresh_hygiene());
        self.lexical(&mut function, &mut locals.to_vec());
        let SExp::Lam {
            bind: Bind::Named(mut bind),
            body,
        } = function
        else {
            unreachable!()
        };
        let name = bind.vars.remove(0);
        let mut argument = argument.clone();
        self.expression(&mut argument, &mut locals.to_vec())?;

        let mut parameters = vec![RightBind {
            vars: vec![name.clone()],
            ty: bind.ty.clone(),
        }];
        let mut scope = locals.to_vec();
        self.expand_structure_parameters(&mut parameters, &mut scope, false)?;
        let input = self.last_inputs[0].clone();
        let (arguments, mut checks) = if input.signature.is_some() {
            self.callback_arguments(&input, &argument, locals)?
        } else {
            (
                vec![if input.computation {
                    thunk(argument.clone())
                } else {
                    argument.clone()
                }],
                Vec::new(),
            )
        };
        let mut substitutions = HashMap::new();
        for (parameter, argument) in parameters.iter().zip(arguments) {
            checks.push((argument.clone(), substitute(&parameter.ty, &substitutions)));
            substitutions.insert(parameter.vars[0].1.unwrap(), argument);
        }
        let mut result = if bind.vars.is_empty() {
            *body
        } else {
            SExp::Lam {
                bind: Bind::Named(bind),
                body,
            }
        };
        result = substitute(&result, &HashMap::from([(name.1.unwrap(), argument)]));
        Ok(SExp::Checked {
            checks,
            body: Box::new(result),
        })
    }

    fn anchor_module_path(&self, path: &mut ModuleInstantiatePath) -> Result<(), Diagnostic> {
        if let ModuleInstantiatePath::FromCurrent { back_parent, calls } = path {
            let mut module = self.current;
            for _ in 0..*back_parent {
                module = self.scopes[module.0 as usize].parent.ok_or_else(|| {
                    self.error(crate::error::Error::Invalid(
                        crate::error::Invalid::AlreadyAtRootModule,
                    ))
                })?;
            }
            *path = ModuleInstantiatePath::FromModule {
                module,
                calls: std::mem::take(calls),
            };
        }
        Ok(())
    }

    pub(in crate::resolver) fn anchor_module_expressions(
        &self,
        expression: &mut SExp,
    ) -> Result<(), Diagnostic> {
        let mut result = Ok(());
        macros::walk_sexp_mut(expression, &mut |node| {
            let access = match node {
                SExp::AccessPath { access, .. }
                | SExp::RecordTypeCtor { access, .. }
                | SExp::ProgramValueReference { access }
                | SExp::IndCase { path: access, .. }
                | SExp::ProgramCase { path: access, .. } => Some(access),
                _ => None,
            };
            if result.is_ok()
                && let Some(LocalAccess::Instantiated { path, .. }) = access
            {
                result = self.anchor_module_path(path);
            }
        });
        result
    }

    pub(in crate::resolver) fn normalize_structures(
        &mut self,
        expression: &mut SExp,
        locals: &[LocalScope],
    ) -> Result<(), Diagnostic> {
        self.normalize_in_scope(expression, &mut locals.to_vec())
    }

    fn normalize_in_scope(
        &mut self,
        expression: &mut SExp,
        locals: &mut Vec<LocalScope>,
    ) -> Result<(), Diagnostic> {
        let _cost = timing::costs::Scope::enter("resolve.structure-normalization");
        let mut error = None;
        macros::walk_sexp_control(expression, &mut |node| {
            if error.is_some() {
                return false;
            }
            if let SExp::Induction {
                binders,
                return_type,
                cases,
            } = node
            {
                let mark = locals.len();
                let result = (|| {
                    for bind in binders {
                        self.normalize_in_scope(&mut bind.ty, locals)?;
                        let mut names = LocalScope::default();
                        for name in &mut bind.vars {
                            if name.1.is_none() {
                                self.binding(name);
                            }
                            names.insert(name.0.clone(), name.clone());
                        }
                        locals.push(names);
                    }
                    self.normalize_in_scope(return_type, locals)
                })();
                locals.truncate(mark);
                if let Err(e) = result {
                    error = Some(e);
                    return false;
                }
                for (_, case) in cases {
                    if let Err(e) = self.normalize_in_scope(case, locals) {
                        error = Some(e);
                        break;
                    }
                }
                return false;
            }
            let head = application_head(node);
            if matches!(node, SExp::App { .. })
                && matches!(head, SExp::Lam { bind: Bind::Named(bind), .. } if !bind.vars.is_empty())
                && self.is_declaration_lambda(head)
            {
                let mut result = head.clone();
                let mut checks = Vec::new();
                for argument in application_arguments(node) {
                    if matches!(&result, SExp::Lam { bind: Bind::Named(bind), .. } if !bind.vars.is_empty())
                    {
                        match self.apply_declaration_lambda(&result, argument, locals) {
                            Ok(SExp::Checked {
                                checks: guards,
                                body,
                            }) => {
                                checks.extend(guards);
                                result = *body;
                            }
                            Ok(_) => unreachable!(),
                            Err(e) => {
                                error = Some(e);
                                return false;
                            }
                        }
                    } else {
                        result = SExp::App {
                            func: Box::new(result),
                            arg: Box::new(argument.clone()),
                        };
                    }
                }
                let mut result = SExp::Checked {
                    checks,
                    body: Box::new(result),
                };
                if let Err(e) = self.normalize_in_scope(&mut result, locals) {
                    error = Some(e);
                } else {
                    *node = result;
                }
                return false;
            }
            let access = match node {
                SExp::AccessPath { access, .. }
                | SExp::RecordTypeCtor { access, .. }
                | SExp::ProgramValueReference { access }
                | SExp::IndCase { path: access, .. }
                | SExp::ProgramCase { path: access, .. } => Some(access),
                _ => None,
            };
            if let Some(access @ LocalAccess::Instantiated { .. }) = access {
                let LocalAccess::Instantiated { span, path, child } = access else {
                    unreachable!()
                };
                if let Err(e) = self.anchor_module_path(path) {
                    error = Some(e);
                    return false;
                }
                let mut import_name = Identifier(format!("<temporary:{}>", self.next_expression));
                let mut checks = Vec::new();
                self.next_expression += 1;
                if let Err(e) =
                    self.resolve_import_in_scope(path, &mut import_name, &mut checks, locals)
                {
                    error = Some(e);
                    return false;
                }
                let mut member = LocalAccess::Named {
                    span: *span,
                    access: import_name.clone(),
                    child: child.clone(),
                };
                if let Err(e) = self.access(self.current, &mut member) {
                    error = Some(e);
                    return false;
                }
                let mut guards = vec![(
                    SExp::ModuleInstance {
                        path: path.clone(),
                        import_name,
                    },
                    SExp::ValueType,
                )];
                guards.extend(checks);
                *access = member;
                *node = SExp::Checked {
                    checks: guards,
                    body: Box::new(node.clone()),
                };
                if let Err(e) = self.normalize_in_scope(node, locals) {
                    error = Some(e);
                }
                return false;
            }
            if let SExp::App { func, arg } = node
                && {
                    let mut head = func.as_ref();
                    while let SExp::App { func, .. } | SExp::AssociatedAccess { base: func, .. } =
                        head
                    {
                        head = func;
                    }
                    matches!(
                        head,
                        SExp::Checked { .. }
                            | SExp::Lam {
                                bind: Bind::Named(_),
                                ..
                            }
                            | SExp::AccessPath {
                                access: LocalAccess::Instantiated { .. },
                                ..
                            }
                    )
                }
            {
                if let Err(e) = self.normalize_in_scope(func, locals) {
                    error = Some(e);
                    return false;
                }
                if let SExp::Checked { checks, body } = func.as_ref() {
                    *node = SExp::Checked {
                        checks: checks.clone(),
                        body: Box::new(SExp::App {
                            func: body.clone(),
                            arg: arg.clone(),
                        }),
                    };
                    if let Err(e) = self.normalize_in_scope(node, locals) {
                        error = Some(e);
                    }
                    return false;
                }
            }
            let expansion = match node {
                SExp::Block(block) => Some(block.as_term().map_err(|e| self.error(e))),
                SExp::Exists {
                    bind: Bind::Named(bind),
                } if self.is_structure_type(&bind.ty) => {
                    Some(Ok(self.structure_existence(&bind.ty)))
                }
                SExp::ExistsIntro { element, set } if self.is_structure_type(set) => {
                    Some(self.structure_exists_intro(set, element, locals))
                }
                SExp::TakeProp {
                    bind: Bind::Named(bind),
                    body,
                    existence,
                } if self.is_structure_type(&bind.ty) => {
                    if bind.vars.len() != 1 {
                        Some(Err(self.error(crate::error::Error::Invalid(
                            crate::error::Invalid::ExistentialEliminationRequiresOneWitness,
                        ))))
                    } else {
                        Some(Ok(self.structure_exists_elim(bind, body, existence)))
                    }
                }
                _ => None,
            };
            if let Some(expansion) = expansion {
                match expansion {
                    Ok(mut expression) => {
                        if let Err(e) = self.normalize_in_scope(&mut expression, locals) {
                            error = Some(e);
                        } else {
                            *node = expression;
                        }
                    }
                    Err(e) => error = Some(e),
                }
                return false;
            }
            if let SExp::Where { exp, clauses, .. } = node {
                let mut scope = locals.to_vec();
                for (name, ty, body) in clauses {
                    if let Err(e) = self
                        .normalize_structures(ty, &scope)
                        .and_then(|()| self.normalize_in_scope(body, &mut scope))
                    {
                        error = Some(e);
                        return false;
                    }
                    if name.1.is_none() {
                        self.binding(name);
                    }
                    scope.push(LocalScope::from_iter([(name.0.clone(), name.clone())]));
                }
                if let Err(e) = self.normalize_in_scope(exp, &mut scope) {
                    error = Some(e);
                }
                return false;
            }
            if let SExp::MemberLiteral { ty, fields } = node {
                let SExp::AccessPath { access, parameters } = ty.as_ref() else {
                    error = Some(self.error(crate::error::Error::Invalid(
                        crate::error::Invalid::ExpectedAStructureTypeBeforeALiteral,
                    )));
                    return false;
                };
                let mut literal = SExp::RecordTypeCtor {
                    access: access.clone(),
                    parameters: parameters.clone(),
                    fields: fields.clone(),
                };
                match self.normalize_in_scope(&mut literal, locals) {
                    Ok(()) => *node = literal,
                    Err(e) => error = Some(e),
                }
                return false;
            }
            if let SExp::AccessPath { access, parameters }
            | SExp::RecordTypeCtor {
                access, parameters, ..
            } = node
                && let Some(id) = self.front_binding(access, locals)
                && (self.structures.contains_key(&id)
                    || self.parameter_signatures.contains_key(&id))
            {
                for argument in parameters.iter_mut() {
                    if let Err(e) = self.normalize_in_scope(argument, locals) {
                        error = Some(e);
                        return false;
                    }
                }
                if self.structures.contains_key(&id) {
                    let ty = SExp::AccessPath {
                        access: access.clone(),
                        parameters: parameters.clone(),
                    };
                    if let Err(e) = self.structure_type(&ty, locals) {
                        error = Some(e);
                        return false;
                    }
                } else if !parameters.is_empty()
                    && let Some(signature) = self.parameter_signatures.get(&id).cloned()
                {
                    let (mut actual, mut checks) = match self.expand_type_arguments(
                        &signature.parameters,
                        &signature.inputs,
                        parameters,
                        access,
                        locals,
                    ) {
                        Ok(result) => result,
                        Err(e) => {
                            error = Some(e);
                            return false;
                        }
                    };
                    let substitutions = signature
                        .parameters
                        .iter()
                        .zip(&actual)
                        .map(|(bind, value)| (bind.vars[0].1.unwrap(), value.clone()))
                        .collect();
                    checks.extend(signature.checks.iter().map(|(value, ty)| {
                        (
                            self.substitute_front_expression(
                                &self.instantiate_front_expression(value, access),
                                &substitutions,
                            ),
                            self.substitute_front_expression(
                                &self.instantiate_front_expression(ty, access),
                                &substitutions,
                            ),
                        )
                    }));
                    // Expanding a declaration argument can introduce captures
                    // specialized from its defining namespace. Their module
                    // expressions need normalization before ordinary resolution.
                    for argument in &mut actual {
                        if let Err(e) = self.normalize_in_scope(argument, locals) {
                            error = Some(e);
                            return false;
                        }
                    }
                    for (value, ty) in &mut checks {
                        if let Err(e) = self
                            .normalize_in_scope(value, locals)
                            .and_then(|()| self.normalize_in_scope(ty, locals))
                        {
                            error = Some(e);
                            return false;
                        }
                    }
                    *parameters = actual;
                    if let SExp::RecordTypeCtor { fields, .. } = node {
                        for (_, value) in fields {
                            if let Err(e) = self.normalize_in_scope(value, locals) {
                                error = Some(e);
                                return false;
                            }
                        }
                    }
                    if !checks.is_empty() {
                        *node = SExp::Checked {
                            checks,
                            body: Box::new(node.clone()),
                        };
                    }
                    // The expanded arguments and literal fields have been normalized.
                    return false;
                }
            }
            if let SExp::AccessPath { access, parameters } = node
                && parameters.is_empty()
                && let Some(id) = self.front_binding(access, locals)
                && self.computation_bindings.contains(&id)
            {
                let mut access = access.clone();
                let reflected = match &mut access {
                    LocalAccess::Current { access, .. } | LocalAccess::Resolved { access, .. } => {
                        let reflected = access.0.ends_with('^');
                        access.0 = access.0.trim_end_matches('^').to_owned();
                        reflected
                    }
                    LocalAccess::Instantiated { .. } => unreachable!(),
                    LocalAccess::Named { child, .. } => {
                        let reflected = child.0.ends_with('^');
                        child.0 = child.0.trim_end_matches('^').to_owned();
                        reflected
                    }
                };
                let value = SExp::Force {
                    value: Box::new(SExp::ProgramValueReference { access }),
                };
                *node = if reflected {
                    SExp::ReflectTerm {
                        expression: Box::new(value),
                    }
                } else {
                    value
                };
                return false;
            }
            if let SExp::AssociatedAccess { base, field, span } = node {
                if let Err(e) = self.normalize_in_scope(base, locals) {
                    error = Some(e);
                    return false;
                }
                let mut body = (**base).clone();
                let mut checks = Vec::new();
                while let SExp::Checked {
                    checks: inner,
                    body: value,
                } = body
                {
                    checks.extend(inner);
                    body = *value;
                }
                let result = SExp::AssociatedAccess {
                    base: Box::new(body),
                    field: field.clone(),
                    span: *span,
                };
                *node = if checks.is_empty() {
                    result
                } else {
                    SExp::Checked {
                        checks,
                        body: Box::new(result),
                    }
                };
            }
            if matches!(
                node,
                SExp::Prod {
                    bind: Bind::Named(_),
                    ..
                } | SExp::Lam {
                    bind: Bind::Named(_),
                    ..
                }
            ) {
                let lambda = matches!(node, SExp::Lam { .. });
                let (SExp::Prod {
                    bind: Bind::Named(bind),
                    body,
                }
                | SExp::Lam {
                    bind: Bind::Named(bind),
                    body,
                }) = node
                else {
                    unreachable!()
                };
                // Ordinary binders keep their tree in place. Rebuilding their
                // bodies would copy every nested subtree once per outer binder.
                if !self.is_structure_type(&bind.ty) {
                    if let Err(e) = self.normalize_in_scope(&mut bind.ty, locals) {
                        error = Some(e);
                        return false;
                    }
                    let mut names = LocalScope::default();
                    for name in &mut bind.vars {
                        if name.1.is_none() {
                            self.binding(name);
                        }
                        names.insert(name.0.clone(), name.clone());
                    }
                    let mark = locals.len();
                    locals.push(names);
                    if let Err(e) = self.normalize_in_scope(body, locals) {
                        error = Some(e);
                    }
                    locals.truncate(mark);
                    return false;
                }
                let mut scope = locals.clone();
                let mut parameters = vec![bind.clone()];
                if let Err(e) = self.expand_structure_parameters(&mut parameters, &mut scope, false)
                {
                    error = Some(e);
                    return false;
                }
                let parameter_checks = self.last_parameter_checks.clone();
                if let Err(e) = self.normalize_in_scope(body, &mut scope) {
                    error = Some(e);
                    return false;
                }
                let (SExp::Prod { body, .. } | SExp::Lam { body, .. }) =
                    std::mem::replace(node, SExp::ValueType)
                else {
                    unreachable!()
                };
                let mut result = *body;
                if !parameter_checks.is_empty() {
                    result = SExp::Checked {
                        checks: parameter_checks,
                        body: Box::new(result),
                    };
                }
                for bind in parameters.into_iter().rev() {
                    result = if lambda {
                        SExp::Lam {
                            bind: Bind::Named(bind),
                            body: Box::new(result),
                        }
                    } else {
                        SExp::Prod {
                            bind: Bind::Named(bind),
                            body: Box::new(result),
                        }
                    };
                }
                *node = result;
                return false;
            }
            let projected = match node {
                SExp::AccessPath {
                    access:
                        LocalAccess::Named {
                            access,
                            child,
                            span,
                        },
                    parameters,
                } => Some((
                    variable(access.clone()),
                    child.clone(),
                    parameters.clone(),
                    *span,
                )),
                SExp::InferredProjection { value, field, span } => {
                    Some(((**value).clone(), field.clone(), Vec::new(), *span))
                }
                SExp::MemberAccess {
                    base,
                    field,
                    parameters,
                    span,
                } => Some(((**base).clone(), field.clone(), parameters.clone(), *span)),
                _ => None,
            };
            if let Some((mut base, field, parameters, span)) = projected {
                if let Err(e) = self.normalize_in_scope(&mut base, locals) {
                    error = Some(e);
                    return false;
                }
                match self.structure_value(&base, locals) {
                    Ok(Some(value)) => {
                        if let Some(location) = &self.location
                            && span.end > span.start
                            && let Some(binding) = self.global_bindings.get(&value.signature)
                        {
                            self.references.borrow_mut().push(Reference {
                                module: self.path(self.current),
                                location: SourceLocation {
                                    source: location.source.clone(),
                                    span,
                                },
                                target_module: self.path(binding.module),
                                target_name: format!(
                                    "{}::{}",
                                    binding.name,
                                    field.as_str().trim_end_matches('^')
                                ),
                            });
                        }
                        if !value.parameters.is_empty() {
                            error = Some(
                                self.error(crate::error::Error::Invalid(crate::error::Invalid::StructureDeclarationNeedsItsRemainingArguments)),
                            );
                            return false;
                        }
                        if let Some((_, expression)) = value
                            .fields
                            .iter()
                            .find(|(name, _)| name == field.as_str().trim_end_matches('^'))
                        {
                            let expression = if field.as_str().ends_with('^') {
                                let is_type =
                                    self.structures.get(&value.signature).is_some_and(|shape| {
                                        shape.fields.iter().any(|(name, ty, _)| {
                                            name.as_str() == field.as_str().trim_end_matches('^')
                                                && matches!(ty, SExp::ValueType)
                                        })
                                    });
                                if is_type {
                                    match self.reflect_type(expression.clone()) {
                                        Ok(expression) => expression,
                                        Err(e) => {
                                            error = Some(e);
                                            return false;
                                        }
                                    }
                                } else {
                                    SExp::ReflectTerm {
                                        expression: Box::new(expression.clone()),
                                    }
                                }
                            } else {
                                expression.clone()
                            };
                            let mut expression = expression;
                            for argument in &parameters {
                                expression = SExp::App {
                                    func: Box::new(expression),
                                    arg: Box::new(argument.clone()),
                                };
                            }
                            *node = if value.checks.is_empty() {
                                expression.clone()
                            } else {
                                SExp::Checked {
                                    checks: value.checks.clone(),
                                    body: Box::new(expression.clone()),
                                }
                            };
                            // Substitution can specialize a captured module in
                            // the selected field. Normalize the replacement's
                            // head too, before resolving its references.
                            if let Err(e) = self.normalize_in_scope(node, locals) {
                                error = Some(e);
                            }
                            return false;
                        } else {
                            error = Some(self.error(crate::error::Error::UnknownStructureField {
                                name: (field.0).to_owned(),
                            }));
                        }
                    }
                    Err(e) => error = Some(e),
                    _ => {
                        if matches!(node, SExp::MemberAccess { .. })
                            || matches!(&base, SExp::AccessPath { access, .. } if self.front_binding(access, locals).is_some())
                        {
                            let mut result = SExp::InferredProjection {
                                value: Box::new(base),
                                field,
                                span,
                            };
                            for argument in parameters {
                                result = SExp::App {
                                    func: Box::new(result),
                                    arg: Box::new(argument),
                                };
                            }
                            *node = result;
                        }
                    }
                }
            }
            let head = application_head(node);
            if let SExp::AccessPath { access, parameters } = head
                && let Some(id) = self.front_binding(access, locals)
                && let Some(definition) = self.front_definitions.get(&id).cloned()
            {
                let mut definition = definition;
                for input in &mut definition.inputs {
                    self.instantiate_input(input, access);
                }
                definition.body = self.instantiate_front_expression(&definition.body, access);
                definition.ty = self.instantiate_front_expression(&definition.ty, access);
                for bind in &mut definition.parameters {
                    *bind.ty = self.instantiate_front_expression(&bind.ty, access);
                }
                let bindings = definition
                    .parameters
                    .iter()
                    .flat_map(|bind| &bind.vars)
                    .filter_map(|name| name.1)
                    .collect();
                self.expose_namespace_arguments(&mut definition.body, &bindings);
                self.expose_namespace_arguments(&mut definition.ty, &bindings);
                for bind in &mut definition.parameters {
                    self.expose_namespace_arguments(&mut bind.ty, &bindings);
                }
                let mut supplied = parameters.clone();
                supplied.extend(application_arguments(node).into_iter().cloned());
                {
                    let mut actual = Vec::new();
                    let mut checks = Vec::new();
                    let mut substitutions = HashMap::new();
                    for (input, argument) in definition.inputs.iter().zip(&supplied) {
                        if input.signature.is_some() {
                            match self.callback_arguments(input, argument, locals) {
                                Ok((fields, guards)) => {
                                    actual.extend(fields);
                                    checks.extend(guards);
                                    if let Err(e) = self.bind_structure_field(
                                        input.binding,
                                        argument.clone(),
                                        &mut substitutions,
                                    ) {
                                        error = Some(e);
                                        return false;
                                    }
                                }
                                Err(e) => {
                                    error = Some(e);
                                    return false;
                                }
                            }
                        } else {
                            actual.push(if input.computation {
                                thunk(argument.clone())
                            } else {
                                argument.clone()
                            });
                        }
                    }
                    let consumed = actual.len();
                    for (bind, value) in definition.parameters.iter().zip(actual) {
                        checks.push((
                            value.clone(),
                            self.substitute_front_expression(&bind.ty, &substitutions),
                        ));
                        substitutions.insert(bind.vars[0].1.unwrap(), value);
                    }
                    checks = checks
                        .into_iter()
                        .map(|(value, ty)| {
                            (
                                self.substitute_front_expression(&value, &substitutions),
                                self.substitute_front_expression(&ty, &substitutions),
                            )
                        })
                        .collect();
                    let remaining: Vec<_> = definition
                        .parameters
                        .iter()
                        .skip(consumed)
                        .map(|bind| RightBind {
                            vars: bind.vars.clone(),
                            ty: Box::new(
                                self.substitute_front_expression(&bind.ty, &substitutions),
                            ),
                        })
                        .collect();
                    let mut body =
                        self.substitute_front_expression(&definition.body, &substitutions);
                    let ty = self.substitute_front_expression(&definition.ty, &substitutions);
                    if matches!(ty, SExp::ValueType) {
                        checks.push((body.clone(), ty));
                    } else {
                        // Keep the declared type on the returned expression;
                        // checking a separate copy would infer its holes again.
                        body = SExp::Ascribe {
                            term: Box::new(body),
                            ty: Box::new(ty),
                        };
                    }
                    let reflected = match access {
                        LocalAccess::Current { access, .. }
                        | LocalAccess::Resolved { access, .. } => access.as_str().ends_with('^'),
                        LocalAccess::Named { child, .. } => child.as_str().ends_with('^'),
                        LocalAccess::Instantiated { .. } => unreachable!(),
                    };
                    let mut result = abstract_parameters(
                        &remaining,
                        SExp::Checked {
                            checks,
                            body: Box::new(body),
                        },
                    );
                    if reflected {
                        result = SExp::ReflectTerm {
                            expression: Box::new(result),
                        };
                    }
                    for argument in supplied.into_iter().skip(definition.inputs.len()) {
                        result = SExp::App {
                            func: Box::new(result),
                            arg: Box::new(argument),
                        };
                    }
                    *node = result;
                    return true;
                }
            }
            true
        });
        error.map_or(Ok(()), Err)
    }
}
