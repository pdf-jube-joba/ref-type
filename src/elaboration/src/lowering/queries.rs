//! Certify elaborated queries in their explicit kernel contexts.
use super::*;

impl Lowerer<'_> {
    pub(crate) fn check_query(
        &mut self,
        context: &ExpContext,
        module: ModuleId,
        term: Exp,
        ty: Exp,
    ) -> Result<(), String> {
        use crate::raw::traversal::Term;
        let mut roots = vec![Term::Logical(term), Term::Logical(ty)];
        roots.extend(context.iter().map(|b| Term::Logical(b.ty)));
        self.prepare_query(roots);
        let mut raw_context = context.clone();
        let term = self.set(term, &mut raw_context, module)?;
        let expected = self.classifier(ty, &mut raw_context, module)?;
        let context = self.context(context, module)?;
        kernel::check::Checker::new(self.kernel, context).check(term, expected)
    }

    pub(crate) fn check_program_query(
        &mut self,
        context: &raw::program::ProgramContext,
        term: raw::program::ProgramTerm,
        ty: raw::program::ProgramType,
    ) -> Result<(), String> {
        use crate::raw::{
            program::{ProgramContextEntry, ProgramTerm, ProgramType},
            traversal::Term,
        };
        let mut roots = vec![
            match term {
                ProgramTerm::ValueTerm(t) => Term::Value(t),
                ProgramTerm::ComputationTerm(t) => Term::Computation(t),
            },
            match ty {
                ProgramType::ValueType(t) => Term::ValueType(t),
                ProgramType::ComputationType(t) => Term::ComputationType(t),
            },
        ];
        roots.extend(context.iter().filter_map(|b| match b {
            ProgramContextEntry::ValueTerm { ty, .. } => Some(Term::ValueType(*ty)),
            _ => None,
        }));
        self.prepare_query(roots);
        let term = self.program_in_context(term, &mut context.clone())?;
        self.scope.program_depth = context.len();
        let ty = self.program_type(ty)?;
        let context = self.program_context(context)?;
        kernel::check::Checker::new(self.kernel, context).check(term, ty)
    }
}
