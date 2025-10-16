// "interactive" type checker

use crate::exp::{Context, Derivation, Exp, Judgement, Provable, Sort, Var};

#[derive(Debug, Clone)]
pub enum ProveTree {
    Leaf(Provable),
    Node(Vec<ProveTree>),
}

pub fn collect_goals_from_derivation(der: &Derivation) -> Vec<ProveTree> {
    let mut goals = vec![];
    let Derivation {
        conclusion,
        premises,
        rule: _,
        meta: _,
    } = der;
    if let Judgement::Provable(prop) = conclusion {
        goals.push(ProveTree::Leaf(prop.clone()));
    }
    for prem in premises {
        goals.extend(collect_goals_from_derivation(prem));
    }
    goals
}

#[derive(Debug)]
pub enum State {
    None,
    Checking(Exp, Exp),
    Inferring(Exp),
}

#[derive(Debug)]
pub struct Checker {
    context: Context,
    goals: Vec<ProveTree>,
    state: State,
}

impl Default for Checker {
    fn default() -> Self {
        Checker {
            context: Context(vec![]),
            goals: vec![],
            state: State::None,
        }
    }
}

impl Checker {
    pub fn current_goals(&self) -> &Vec<ProveTree> {
        &self.goals
    }
    pub fn is_accepted(&self) -> bool {
        self.goals.is_empty()
    }
    pub fn context(&self) -> &Context {
        &self.context
    }
    pub fn state(&self) -> &State {
        &self.state
    }
    pub fn is_waiting(&self) -> bool {
        matches!(self.state, State::None)
    }
    pub fn check(&mut self, term: &Exp, ty: &Exp) -> (Derivation, bool) {
        let (der, b) = crate::derivation::check(&self.context, term, ty);
        let goals = collect_goals_from_derivation(&der);
        if goals.is_empty() {
            self.state = State::None;
        } else {
            self.state = State::Checking(term.clone(), ty.clone());
        }
        (der, b)
    }
    pub fn infer(&mut self, term: &Exp) -> (Derivation, Option<Exp>) {
        let (der, ty) = crate::derivation::infer(&self.context, term);
        let goals = collect_goals_from_derivation(&der);
        if goals.is_empty() {
            self.state = State::None;
        } else {
            self.state = State::Inferring(term.clone());
        }
        (der, ty)
    }
    pub fn infer_sort(&mut self, term: &Exp) -> (Derivation, Option<Sort>) {
        let (der, s) = crate::derivation::infer_sort(&self.context, term);
        // self.goals = collect_goals_from_derivation(&der);
        // I think infer_sort will not produce any goals
        (der, s)
    }
    pub fn push(&mut self, var: Var, ty: Exp) -> (Derivation, bool) {
        let (der, res) = self.infer_sort(&ty);
        if res.is_none() {
            return (der, false);
        }

        self.context.0.push((var, ty));
        (der, true)
    }
}
