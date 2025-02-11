use super::inductive::*;
use super::*;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GlobalContext {
    definitions: Vec<(Var, Exp, Exp)>,       // x := v
    parameters: Vec<(Var, Exp)>,             // x: t
    inductive_definitions: Vec<IndTypeDefs>, // inductive definitions
}
impl GlobalContext {
    pub(crate) fn push_new_defs(&mut self, (x, a, v): (Var, Exp, Exp)) {
        self.definitions.push((x, a, v));
    }
    pub(crate) fn push_new_assum(&mut self, (x, a): (Var, Exp)) {
        self.parameters.push((x, a));
    }
    pub(crate) fn push_new_ind(&mut self, defs: IndTypeDefs) {
        self.inductive_definitions.push(defs);
    }
    pub fn type_of_indtype(&self, ind_type_name: &TypeName) -> Option<Exp> {
        let indtype_def = self.indtype_def(ind_type_name)?;
        Some(indtype_def.arity_as_exp())
    }
    pub fn indtype_def(&self, type_name: &TypeName) -> Option<&IndTypeDefs> {
        self.inductive_definitions
            .iter()
            .find(|defs| defs.name() == type_name)
    }
    pub fn indtype_defs(&self) -> &Vec<IndTypeDefs> {
        &self.inductive_definitions
    }
    pub fn type_of_cst(
        &self,
        ind_type_name: &TypeName,
        constructor_name: &ConstructorName,
    ) -> Option<Exp> {
        let defs = self.indtype_def(ind_type_name)?;
        let constructor_def = defs.constructor(constructor_name)?;
        let constructor_exp: Exp = constructor_def.clone().into();
        Some(constructor_exp)
    }
    pub fn ind_type_return_type(&self, ind_type_name: &TypeName, sort: Sort) -> Option<Exp> {
        let inddefs = self.indtype_def(ind_type_name)?;
        Some(inddefs.return_type(sort))
    }
    pub fn induction_principal(&self, ind_type_name: &TypeName, sort: Sort) -> Option<Exp> {
        let inddefs = self.indtype_def(ind_type_name)?;
        Some(inddefs.induction_scheme(sort))
    }
    pub fn search_var_defined(&self, y: Var) -> Option<(&Exp, &Exp)> {
        self.definitions
            .iter()
            .find_map(|(x, a, e)| if *x == y { Some((a, e)) } else { None })
    }
    pub fn search_var_assum(&self, y: Var) -> Option<&Exp> {
        self.parameters
            .iter()
            .find_map(|(x, a)| if *x == y { Some(a) } else { None })
    }
}
