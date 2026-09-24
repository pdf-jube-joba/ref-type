use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextEdit {
    pub location: Location,
    pub replacement: String,
}

#[derive(Debug, Clone)]
pub struct EditProposal {
    pub revision: RevisionId,
    pub edits: Vec<TextEdit>,
    pub diagnostics: Vec<Diagnostic>,
    pub goals: Vec<GoalSnapshot>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EditError {
    Stale,
    UnknownGoal,
    GeneratedGoal,
    InvalidRange,
    OverlappingEdits,
    Rejected(Vec<String>),
}

impl AnalysisHost {
    /// Apply exactly the edits that were checked against this input revision.
    pub fn apply_edits(&mut self, proposal: &EditProposal) -> Result<(), EditError> {
        if self.sources.revision() != proposal.revision {
            return Err(EditError::Stale);
        }
        self.sources = edited_sources(&self.sources, &proposal.edits)?;
        Ok(())
    }

    pub fn give(&self, goal: GoalId, term: &str) -> Result<EditProposal, EditError> {
        self.propose_goal(goal, term, false)
    }

    pub fn refine(&self, goal: GoalId, term: &str) -> Result<EditProposal, EditError> {
        self.propose_goal(goal, term, true)
    }

    fn propose_goal(
        &self,
        id: GoalId,
        term: &str,
        allow_goals: bool,
    ) -> Result<EditProposal, EditError> {
        if id.revision != self.sources.revision() {
            return Err(EditError::Stale);
        }
        let snapshot = self.snapshot();
        let goal = snapshot
            .check()
            .goals
            .iter()
            .find(|goal| goal.id == id)
            .ok_or(EditError::UnknownGoal)?;
        if !goal.editable || goal.occurrences.is_empty() {
            return Err(EditError::GeneratedGoal);
        }
        let expression =
            crate::parse::str_parse_exp(term).map_err(|error| EditError::Rejected(vec![error]))?;
        let replacement = match expression {
            crate::syntax::SExp {
                kind: crate::syntax::SExpKind::AccessPath { .. },
                ..
            }
            | crate::syntax::SExp {
                kind: crate::syntax::SExpKind::Meta { .. },
                ..
            }
            | crate::syntax::SExp {
                kind: crate::syntax::SExpKind::Sort(_),
                ..
            } => term.trim().to_owned(),
            _ => format!("({term})"),
        };
        let mut edits = Vec::new();
        for location in &goal.occurrences {
            let file = self.sources.file(location.file).ok_or(EditError::Stale)?;
            let original = file
                .source
                .text
                .get(location.range.start..location.range.end)
                .ok_or(EditError::InvalidRange)?;
            let expected = match goal.flavor {
                crate::metavariables::MetaFlavor::Implicit => "_".to_string(),
                crate::metavariables::MetaFlavor::Goal => "?".to_string(),
                crate::metavariables::MetaFlavor::Named(number) => format!("?{number}"),
                crate::metavariables::MetaFlavor::Synthetic => {
                    return Err(EditError::GeneratedGoal);
                }
            };
            if original != expected {
                return Err(EditError::GeneratedGoal);
            }
            edits.push(TextEdit {
                location: *location,
                replacement: replacement.clone(),
            });
        }
        let sources = edited_sources(&self.sources, &edits)?;
        let candidate = AnalysisHost {
            sources,
            root: self.root.clone(),
            identities: self.identities.clone(),
            current: RefCell::default(),
        }
        .snapshot();
        let result = candidate.check();
        let accepted = candidate.check_item(id.owner).is_some_and(|item| {
            item.status == ItemCheckStatus::Checked
                || allow_goals && item.status == ItemCheckStatus::Incomplete
        });
        if !accepted {
            return Err(EditError::Rejected(
                result
                    .diagnostics
                    .iter()
                    .map(|diagnostic| diagnostic.message.clone())
                    .collect(),
            ));
        }
        Ok(EditProposal {
            revision: self.sources.revision(),
            edits,
            diagnostics: result.diagnostics.clone(),
            goals: result.goals.clone(),
        })
    }
}

fn edited_sources(
    sources: &SourceDatabase,
    edits: &[TextEdit],
) -> Result<SourceDatabase, EditError> {
    let mut by_file = std::collections::BTreeMap::<FileId, Vec<&TextEdit>>::new();
    for edit in edits {
        by_file.entry(edit.location.file).or_default().push(edit);
    }
    let mut result = sources.clone();
    for (id, mut edits) in by_file {
        let file = sources.file(id).ok_or(EditError::Stale)?;
        edits.sort_by_key(|edit| edit.location.range.start);
        let mut previous_end = 0;
        for edit in &edits {
            if file.revision != edit.location.revision {
                return Err(EditError::Stale);
            }
            let range = edit.location.range;
            if range.start > range.end || file.source.text.get(range.start..range.end).is_none() {
                return Err(EditError::InvalidRange);
            }
            if range.start < previous_end {
                return Err(EditError::OverlappingEdits);
            }
            previous_end = range.end;
        }
        let mut text = file.source.text.clone();
        for edit in edits.into_iter().rev() {
            text.replace_range(
                edit.location.range.start..edit.location.range.end,
                &edit.replacement,
            );
        }
        result.set_overlay(&file.source.id.0, text);
    }
    Ok(result)
}
