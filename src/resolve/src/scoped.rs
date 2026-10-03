//! Declaration scopes and reflected views of Program type templates.
use super::*;

impl Resolver {
    pub(super) fn scoped_item(
        &mut self,
        mut item: ModuleItem,
        output: &mut Vec<ModuleItem>,
    ) -> Result<(), Diagnostic> {
        let ModuleItem::Scoped { exports, items } = item else {
            self.item(&mut item)?;
            output.push(item);
            return Ok(());
        };
        let saved = self.scopes[self.current.0 as usize].clone();
        let previous = self.declaration_scope;
        let public = std::mem::take(&mut self.public_declarations);
        if previous.is_none() {
            self.public_declarations
                .extend(exports.iter().map(|name| name.0.clone()));
        }
        let scope = self.next_declaration_scope;
        self.next_declaration_scope += 1;
        self.declaration_scope = Some(scope);
        for item in items {
            self.scoped_item(item, output)?;
        }
        let local = std::mem::replace(&mut self.scopes[self.current.0 as usize], saved);
        let scope = &mut self.scopes[self.current.0 as usize];
        for name in exports {
            if let Some(id) = local.names.get(name.as_str()) {
                if scope.names.insert(name.0.clone(), *id).is_some() {
                    return Err(self.error(format!("duplicate declaration: {}", name.0)));
                }
            } else if let Some(template) = local
                .macros
                .iter()
                .find(|d| d.name.as_str() == name.as_str())
            {
                if scope
                    .macros
                    .iter()
                    .any(|d| d.name.as_str() == name.as_str())
                {
                    return Err(self.error(format!("duplicate declaration: {}", name.0)));
                }
                scope.macros.push(template.clone());
            } else {
                return Err(self.error(format!("missing exported member: {}", name.0)));
            }
        }
        self.declaration_scope = previous;
        self.public_declarations = public;
        Ok(())
    }

    pub(super) fn expand_type_member(
        &self,
        access: &LocalAccess,
        parameters: &[SExp],
    ) -> Option<Result<SExp, Diagnostic>> {
        let (scope, name) = match access {
            LocalAccess::Current { access, .. } => (self.current, access),
            LocalAccess::Named { access, child, .. } => {
                (self.import(self.current, access.as_str())?, child)
            }
            LocalAccess::Resolved { .. } => return None,
        };
        let spelling = name.as_str().trim_end_matches('^');
        if !spelling.contains("::[")
            || !self
                .visible(scope)
                .iter()
                .any(|d| d.name.as_str() == spelling)
        {
            return None;
        }
        if !parameters.is_empty() {
            return Some(Err(self.error("bundle type members do not take parameters")));
        }
        Some(
            self.expand_one(scope, Some(&Identifier(spelling.into())), &[], 0, None)
                .and_then(|mut ty| {
                    self.expand(&mut ty)?;
                    if name.as_str().ends_with('^') {
                        self.reflect_type(ty)
                    } else {
                        Ok(ty)
                    }
                }),
        )
    }

    pub(super) fn reflect_type(&self, ty: SExp) -> Result<SExp, Diagnostic> {
        Ok(match ty {
            SExp::AccessPath {
                mut access,
                parameters,
            } => {
                let name = match &mut access {
                    LocalAccess::Current { access, .. } | LocalAccess::Resolved { access, .. } => {
                        access
                    }
                    LocalAccess::Named { child, .. } => child,
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
                return Err(self.error("bundle Program types require an explicit type"));
            }
            _ => return Err(self.error("expected Program type in bundle")),
        })
    }
}
