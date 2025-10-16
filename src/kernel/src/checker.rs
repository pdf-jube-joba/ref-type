// "interactive" type checker

use crate::{
    calculus::is_alpha_eq,
    derivation::prove_command,
    exp::{Context, Derivation, Exp, Judgement, Provable, ProveCommandBy, Var},
};

// return derivation of provable judgement if exists
pub fn get_first_goal(der: &mut Derivation) -> Option<&mut Derivation> {
    match der.conclusion {
        Judgement::Provable(_) => Some(der),
        _ => {
            for prem in &mut der.premises {
                if let Some(g) = get_first_goal(prem) {
                    return Some(g);
                }
            }
            None
        }
    }
}

pub fn solve(der: &mut Derivation, command: ProveCommandBy) -> bool {
    let Some(prove_derivation) = get_first_goal(der) else {
        return false;
    };

    let Judgement::Provable(Provable { ctx, prop }) = &prove_derivation.conclusion else {
        unreachable!("get_first_goal should return a Provable judgement");
    };

    let (der, b): (Derivation, bool) = prove_command(ctx, command);
    let Judgement::Provable(Provable {
        ctx: _, // ctx is shared with der.colclusion.ctx
        prop: prop_derived,
    }) = &der.conclusion
    else {
        unreachable!("prove_command should return a Provable judgement");
    };
    if b && is_alpha_eq(prop_derived, prop) {
        *prove_derivation = der;
        true
    } else {
        false
    }
}

#[derive(Debug)]
pub struct Checker {
    context: Context,
}

impl Default for Checker {
    fn default() -> Self {
        Checker {
            context: Context(vec![]),
        }
    }
}

impl Checker {
    pub fn context(&self) -> &Context {
        &self.context
    }
    pub fn check(
        &mut self,
        term: &Exp,
        ty: &Exp,
        prove_commands: Vec<ProveCommandBy>,
    ) -> (Derivation, bool) {
        let (der, b) = crate::derivation::check(&self.context, term, ty);
        if !b {
            return (der, false);
        }

        let mut der = der;
        for command in prove_commands {
            if !solve(&mut der, command) {
                return (der, false);
            }
        }

        if get_first_goal(&mut der).is_some() {
            return (der, false);
        }

        (der, b)
    }
    pub fn push(&mut self, var: Var, ty: Exp) -> (Derivation, bool) {
        let (der, res) = crate::derivation::infer_sort(&self.context, &ty);
        if res.is_none() {
            return (der, false);
        }

        self.context.0.push((var, ty));
        (der, true)
    }
    pub fn pop(&mut self) {
        self.context.0.pop();
    }
}
