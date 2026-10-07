use super::*;

mod representation;

impl GlobalEnvironment {
    pub(super) fn elaborate_set_structure(
        &mut self,
        name: &Identifier,
        parameters: &[RightBind],
        sort: syntax::sort::Sort,
        fields: &[(Identifier, SExp)],
    ) -> Result<(), ElaborationError> {
        let mut scope = LocalScope::default();
        scope.elab_telescope_bind_in_decl(parameters, self)?;
        let mut data = Vec::new();
        let mut laws = Vec::new();
        for (field, ty) in fields {
            let elaborated = scope.elab_exp(ty, self)?;
            let classifier = scope.infer_elaborated(elaborated, self)?;
            self.finish_metavariables()?;
            let classifier = self.metavariables.zonk(&self.crate_env, classifier);
            let classifier = crate::kernel_bridge::whnf(&self.crate_env, classifier);
            if matches!(
                self.crate_env.arena().get(classifier),
                ExpNode::Sort(Sort::Prop)
            ) {
                laws.push((field.clone(), ty.clone()));
            } else {
                data.push((field.clone(), ty.clone()));
            }
            let field = self.crate_env.intern_name(field);
            let ty = self.metavariables.zonk(&self.crate_env, elaborated);
            scope.push_typed_decl_var(field, ty);
        }
        let items = if laws.is_empty() {
            vec![ModuleItem::Record {
                type_name: name.clone(),
                parameters: parameters.to_vec(),
                kind: InductiveKind::Pts(sort),
                fields: data,
            }]
        } else {
            representation::structure(name.clone(), parameters.to_vec(), sort, data, laws)
        };
        let location = self.diagnostic_location.clone();
        for item in &items {
            self.elaborate_declaration(item, location.clone())?;
        }
        Ok(())
    }
}
