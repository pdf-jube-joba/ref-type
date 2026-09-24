//! Resolve expression identities through the source AST's occurrence metadata.
use crate::{
    AstId, Module, ModuleBody, ModuleItem, SourceFile, SourceLocation, visit::VisitSources,
};
use std::{cell::RefCell, collections::HashMap, sync::Arc};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GenerationReason {
    Desugaring,
    ImplicitType,
    InferredFunction,
    Elaboration,
    KernelLowering,
}

/// Edges refer to occurrences, not to shared term handles.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DerivedOrigin {
    Expansion {
        call: Option<AstId>,
        definition: Option<AstId>,
    },
    Template {
        expansion: AstId,
        template: Option<AstId>,
    },
    Capture {
        expansion: AstId,
        parameter: Option<AstId>,
        captured: Option<AstId>,
    },
    Generated {
        source: Option<AstId>,
        reason: GenerationReason,
    },
}

impl DerivedOrigin {
    fn primary(self) -> Option<AstId> {
        match self {
            Self::Expansion { call, .. } => call,
            Self::Template { expansion, .. } => Some(expansion),
            Self::Capture { captured, .. } => captured,
            Self::Generated { source, .. } => source,
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct SourceMap {
    expressions: HashMap<AstId, SourceLocation>,
    origins: RefCell<HashMap<AstId, DerivedOrigin>>,
}

impl SourceMap {
    pub fn location(&self, mut id: AstId) -> Option<&SourceLocation> {
        loop {
            if let Some(location) = self.expressions.get(&id) {
                return Some(location);
            }
            id = self.origin(id)?.primary()?;
        }
    }

    /// The written occurrence, including a template's definition-site names.
    pub fn written_location(&self, mut id: AstId) -> Option<&SourceLocation> {
        loop {
            if let Some(location) = self.expressions.get(&id) {
                return Some(location);
            }
            id = match self.origin(id)? {
                DerivedOrigin::Template { template, .. } => template?,
                DerivedOrigin::Generated { .. } => return None,
                other => other.primary()?,
            };
        }
    }

    pub fn origin(&self, id: AstId) -> Option<DerivedOrigin> {
        self.origins.borrow().get(&id).copied()
    }

    pub fn is_editable(&self, mut id: AstId) -> bool {
        loop {
            if self.expressions.contains_key(&id) {
                return true;
            }
            match self.origin(id) {
                Some(DerivedOrigin::Capture {
                    captured: Some(source),
                    ..
                }) => id = source,
                _ => return false,
            }
        }
    }

    pub fn trace(&self, root: AstId) -> Vec<(AstId, Option<DerivedOrigin>)> {
        let mut pending = vec![root];
        let mut seen = std::collections::HashSet::new();
        let mut result = Vec::new();
        while let Some(id) = pending.pop() {
            if !seen.insert(id) {
                continue;
            }
            let origin = self.origin(id);
            result.push((id, origin));
            match origin {
                Some(DerivedOrigin::Expansion { call, definition }) => {
                    pending.extend(definition);
                    pending.extend(call);
                }
                Some(DerivedOrigin::Template {
                    expansion,
                    template,
                }) => {
                    pending.extend(template);
                    pending.push(expansion);
                }
                Some(DerivedOrigin::Capture {
                    expansion,
                    parameter,
                    captured,
                }) => {
                    pending.extend(parameter);
                    pending.push(expansion);
                    pending.extend(captured);
                }
                Some(DerivedOrigin::Generated { source, .. }) => pending.extend(source),
                None => {}
            }
        }
        result
    }

    pub fn derive(&self, origin: DerivedOrigin) -> AstId {
        let id = AstId::fresh();
        self.origins.borrow_mut().insert(id, origin);
        id
    }

    pub fn generated(&self, source: Option<AstId>, reason: GenerationReason) -> AstId {
        self.derive(DerivedOrigin::Generated { source, reason })
    }

    pub fn insert(&mut self, syntax: &impl VisitSources, source: &Arc<SourceFile>) {
        syntax.visit_sources(&mut |node| {
            self.expressions
                .entry(node.id)
                .or_insert_with(|| SourceLocation {
                    source: source.clone(),
                    span: node.span,
                });
        });
    }

    pub fn insert_module(&mut self, module: &Module) {
        if let Some(source) = module.header_source.as_ref().or(module.source.as_ref()) {
            self.insert(&module.name, source);
            for parameter in &module.parameters {
                self.insert(parameter, source);
            }
        }
        if let ModuleBody::Inline(items) = &module.body {
            for item in items {
                if let ModuleItem::ChildModule { module } = item {
                    self.insert_module(module);
                } else if let Some(source) = &module.source {
                    self.insert(item, source);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ComputationTermExp, SourceId, parse::str_parse_exp};

    fn source(text: &str) -> Arc<SourceFile> {
        Arc::new(SourceFile {
            id: SourceId("test.ref".into()),
            text: text.into(),
        })
    }

    #[test]
    fn ranges_cover_nested_expressions_and_internal_comments() {
        let file = source(r"/* 前 */ f /* 間 */ (g x) = h y -> \F(A)  ");
        let exp = str_parse_exp(&file.text).unwrap();
        let mut map = SourceMap::default();
        map.insert(&exp, &file);
        let mut fragments = Vec::new();
        exp.visit_sources(&mut |node| {
            let location = map.location(node.id).unwrap();
            assert_eq!(location.span, node.span);
            fragments.push(&file.text[node.span.start..node.span.end]);
        });
        assert_eq!(
            fragments,
            [
                r"f /* 間 */ (g x) = h y -> \F(A)",
                "f /* 間 */ (g x) = h y",
                "f /* 間 */ (g x)",
                "f",
                "f",
                "(g x)",
                "g",
                "g",
                "x",
                "x",
                "h y",
                "h",
                "h",
                "y",
                "y",
                r"\F(A)",
                "(A)",
                "A",
            ]
        );
    }

    #[test]
    fn identities_distinguish_occurrences_and_independent_parses() {
        let file = source("f x x");
        let first = str_parse_exp(&file.text).unwrap();
        let second = str_parse_exp(&file.text).unwrap();
        let mut map = SourceMap::default();
        map.insert(&first, &file);
        assert!(map.location(second.source.unwrap().id).is_none());
        assert_eq!(first.source.unwrap().id, first.clone().source.unwrap().id);
        let mut ids = std::collections::HashSet::new();
        first.visit_sources(&mut |node| {
            assert!(ids.insert(node.id));
        });
        assert_eq!(ids.len(), 8);
    }

    #[test]
    fn program_classification_keeps_expression_occurrences() {
        let file = source(r"\cfun (x: A) => \let y: A := x \in (\force f) y");
        let parsed = str_parse_exp(&file.text).unwrap();
        let root = parsed.source.unwrap().id;
        let program = ComputationTermExp::try_from(parsed).unwrap();
        assert_eq!(program.source.unwrap().id, root);
        let mut map = SourceMap::default();
        map.insert(&program, &file);
        let mut fragments = Vec::new();
        program.visit_sources(&mut |node| {
            let location = map.location(node.id).unwrap();
            fragments.push(&file.text[location.span.start..location.span.end]);
        });
        assert!(fragments.contains(&r"\let y: A := x \in (\force f) y"));
        assert!(fragments.contains(&r"(\force f)"));
        assert!(fragments.contains(&"f"));
        assert!(fragments.contains(&"x"));
        assert!(fragments.contains(&"y"));
    }
}
