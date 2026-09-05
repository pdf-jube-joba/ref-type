//! Checked handles and judgements for the CBPV Program calculus.

use serde::Serialize;

use crate::{exp::RawExp, ids::SymbolId};

/// A raw kernel term classified as Program syntax.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub struct Program(RawExp);

impl Program {
    pub(crate) fn checked(raw: RawExp) -> Self {
        Self(raw)
    }

    pub fn raw(self) -> RawExp {
        self.0
    }
}

/// An assumption in a Program context (`Delta` in `system.md`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ProgramContextEntry {
    Type { var: SymbolId },
    Value { var: SymbolId, ty: Program },
}

pub type ProgramContext = Vec<ProgramContextEntry>;

/// Program formation and typing are distinct from Set/Prop typing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ProgramJudgement {
    ValueType,
    ComputationType,
    Value { ty: Program },
    Computation { ty: Program },
}

/// A Program term together with the formation/typing judgement it satisfies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct WellTypedProgram {
    pub program: Program,
    pub judgement: ProgramJudgement,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        derivation::CheckSession,
        environment::CrateEnv,
        exp::{ContextEntry, RawNode},
        ids::SymbolId,
    };

    #[test]
    fn program_judgement_returns_a_program_handle() {
        let env = CrateEnv::new();
        let raw = env.arena().alloc(RawNode::Bound(0));
        let mut context = vec![ContextEntry::ProgramType { var: SymbolId(7) }];
        let mut session = CheckSession::new(&env, env.root_module(), &mut context);

        let checked = session.infer_program_judgement(raw).unwrap();

        assert_eq!(checked.program.raw(), raw);
        assert_eq!(checked.judgement, ProgramJudgement::ValueType);
    }

    #[test]
    fn set_terms_are_rejected_by_the_program_judgement() {
        let env = CrateEnv::new();
        let raw = env.arena().alloc(RawNode::Sort(crate::sort::Sort::Set(0)));
        let mut context = Vec::new();
        let mut session = CheckSession::new(&env, env.root_module(), &mut context);

        assert!(session.infer_program_judgement(raw).is_err());
    }
}
