//! Structured parse failures and owned token descriptions.
use super::*;

#[derive(Debug, Clone)]
pub struct ParseError {
    pub kind: ParseErrorKind,
    pub(super) start: usize,
    pub(super) end: usize,
    pub source: Option<std::sync::Arc<SourceFile>>,
}

impl ParseError {
    pub fn with_source(mut self, source: std::sync::Arc<SourceFile>) -> Self {
        self.source = Some(source);
        self
    }
    pub fn span(&self) -> SourceSpan {
        SourceSpan {
            start: self.start,
            end: self.end,
        }
    }
    pub fn message(&self) -> String {
        format!("parse error: {} ({}..{})", self.kind, self.start, self.end)
    }
    pub fn render(&self, source: &std::sync::Arc<SourceFile>) -> String {
        format!(
            "{}\n{}",
            self.message(),
            SourceLocation {
                source: source.clone(),
                span: self.span()
            }
            .render()
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum OwnedToken {
    KeyWord(String),
    MacroVar(String),
    MacroRest(String),
    QuotedMacro(String),
    EscapedMacro(String),
    Ident(String),
    Caret,
    Number(String),
    Metavariable(String),
    Hole,
    Macro(String),
    LParen,
    RParen,
    MathLParen,
    MathRParen,
    CommentStart,
    CommentEnd,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    ComputationArrow,
    BindArrow,
    Arrow,
    DoubleArrow,
    Assign,
    Pipe,
    Colon,
    Semicolon,
    Period,
    Comma,
    Equal,
    Exclamation,
    DoubleColon,
    RecordConstructor,
}
impl Token<'_> {
    pub(super) fn owned(self) -> OwnedToken {
        match self {
            Self::KeyWord(text) => OwnedToken::KeyWord(text.to_owned()),
            Self::MacroVar(text) => OwnedToken::MacroVar(text.to_owned()),
            Self::MacroRest(text) => OwnedToken::MacroRest(text.to_owned()),
            Self::QuotedMacro(text) => OwnedToken::QuotedMacro(text.to_owned()),
            Self::EscapedMacro(text) => OwnedToken::EscapedMacro(text.to_owned()),
            Self::Ident(text) => OwnedToken::Ident(text.to_owned()),
            Self::Caret => OwnedToken::Caret,
            Self::Number(text) => OwnedToken::Number(text.to_owned()),
            Self::Metavariable(text) => OwnedToken::Metavariable(text.to_owned()),
            Self::Hole => OwnedToken::Hole,
            Self::Macro(text) => OwnedToken::Macro(text.to_owned()),
            Self::LParen => OwnedToken::LParen,
            Self::RParen => OwnedToken::RParen,
            Self::MathLParen => OwnedToken::MathLParen,
            Self::MathRParen => OwnedToken::MathRParen,
            Self::CommentStart => OwnedToken::CommentStart,
            Self::CommentEnd => OwnedToken::CommentEnd,
            Self::LBrace => OwnedToken::LBrace,
            Self::RBrace => OwnedToken::RBrace,
            Self::LBracket => OwnedToken::LBracket,
            Self::RBracket => OwnedToken::RBracket,
            Self::ComputationArrow => OwnedToken::ComputationArrow,
            Self::BindArrow => OwnedToken::BindArrow,
            Self::Arrow => OwnedToken::Arrow,
            Self::DoubleArrow => OwnedToken::DoubleArrow,
            Self::Assign => OwnedToken::Assign,
            Self::Pipe => OwnedToken::Pipe,
            Self::Colon => OwnedToken::Colon,
            Self::Semicolon => OwnedToken::Semicolon,
            Self::Period => OwnedToken::Period,
            Self::Comma => OwnedToken::Comma,
            Self::Equal => OwnedToken::Equal,
            Self::Exclamation => OwnedToken::Exclamation,
            Self::DoubleColon => OwnedToken::DoubleColon,
            Self::RecordConstructor => OwnedToken::RecordConstructor,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Expected {
    Keyword(String),
    Token(OwnedToken),
    Identifier,
    Number,
    OtherSymbol,
    ModuleItem,
    MacroPatternAtom,
    MacroPatternElement,
    StructureSort,
}
impl std::fmt::Display for Expected {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Keyword(keyword) => write!(f, "keyword {keyword}"),
            Self::Token(token) => write!(f, "{token:?}"),
            Self::Identifier => f.write_str("identifier"),
            Self::Number => f.write_str("number"),
            Self::OtherSymbol => f.write_str("other symbol"),
            Self::ModuleItem => f.write_str("a module item"),
            Self::MacroPatternAtom => f.write_str("macro pattern atom"),
            Self::MacroPatternElement => f.write_str(
                "expression/token/rest capture, escaped token, quoted literal, or nested pattern;",
            ),
            Self::StructureSort => f.write_str("PTS sort or \\VType in structure declaration"),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ParseErrorKind {
    Expected {
        expected: Expected,
        found: Option<OwnedToken>,
    },
    Lex {
        text: String,
    },
    InvalidNumber {
        text: String,
    },
    DuplicateStructureField {
        name: String,
    },
    UnknownAxiom {
        name: String,
    },
    MetavariableNumberOverflow {
        text: String,
    },
    UnexpectedKeyword {
        keyword: String,
    },
    ExpectedProofField {
        name: String,
    },
    ExtraTokens {
        found: OwnedToken,
    },
    ProgramDatatypeDeclarationsCannotHaveIndices,
    ProgramLambdaRequiresAPlainValueBinder,
    DuplicateStepMatchBranch,
    ExpectedPtsSortOrVtypeInInductiveDeclaration,
    ExpectedContinueOrFinishBranch,
    ExpectedOrFollowedByDigits,
    ExpectedAtom,
    ExpectedBlockStatementOrReturn,
    ExpectedExpressionStartingWithKeyword,
    ExpectedFixedTokenSequencePatternOr,
    ExpectedInductionBinders,
    ExpectedMacroExpression,
    ExpectedNumberedMetavariableAfterAssign,
    ExpectedSingleIdentifierInRefinementBinder,
    ExpectedSortKeyword,
    ExpectedSubsetTypeXAWhereP,
    MacroCapturesAreOnlyValidInMacroTemplates,
    MissingContinueBranch,
    MissingFinishBranch,
    RefinementBindersAreNotAllowedInInductiveSignatures,
    RestSplicesAreOnlyValidInMacroTemplates,
    StepMatchExpectsARunstepType,
    TokenMatchingIsOnlyValidInNamedMacroTemplates,
    UnmatchedCommentEnd,
}
impl std::fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Expected { expected, found } => {
                write!(f, "expected {expected}, found ")?;
                match found {
                    Some(token) => write!(f, "{token:?}"),
                    None => f.write_str("<eof>"),
                }
            }
            Self::Lex { text } => write!(f, "lex error: {text:?}"),
            Self::InvalidNumber { text } => write!(f, "invalid number: {text}"),
            Self::DuplicateStructureField { name } => {
                write!(f, "duplicate structure field: {name}")
            }
            Self::UnknownAxiom { name } => write!(f, "unknown axiom: {name}"),
            Self::MetavariableNumberOverflow { text } => {
                write!(f, "metavariable number is too large: {text}")
            }
            Self::UnexpectedKeyword { keyword } => {
                write!(f, "unexpected keyword in atom: {keyword}")
            }
            Self::ExpectedProofField { name } => write!(f, "expected `{name}` proof field"),
            Self::ExtraTokens { found } => write!(f, "extra tokens after expression: {found:?}"),
            Self::ProgramDatatypeDeclarationsCannotHaveIndices => {
                f.write_str("Program datatype declarations cannot have indices")
            }
            Self::ProgramLambdaRequiresAPlainValueBinder => {
                f.write_str("Program lambda requires a plain value binder")
            }
            Self::DuplicateStepMatchBranch => f.write_str("duplicate step-match branch"),
            Self::ExpectedPtsSortOrVtypeInInductiveDeclaration => {
                f.write_str("expected PTS sort or \\VType in inductive declaration")
            }
            Self::ExpectedContinueOrFinishBranch => {
                f.write_str("expected \\continue or \\finish branch")
            }
            Self::ExpectedOrFollowedByDigits => {
                f.write_str("expected `?` or `_` followed by digits")
            }
            Self::ExpectedAtom => f.write_str("expected atom"),
            Self::ExpectedBlockStatementOrReturn => {
                f.write_str("expected block statement or \\return")
            }
            Self::ExpectedExpressionStartingWithKeyword => {
                f.write_str("expected expression starting with keyword")
            }
            Self::ExpectedFixedTokenSequencePatternOr => {
                f.write_str("expected fixed token, sequence pattern, or _")
            }
            Self::ExpectedInductionBinders => f.write_str("expected induction binders"),
            Self::ExpectedMacroExpression => f.write_str("expected macro expression"),
            Self::ExpectedNumberedMetavariableAfterAssign => {
                f.write_str("expected numbered metavariable after \\assign")
            }
            Self::ExpectedSingleIdentifierInRefinementBinder => {
                f.write_str("expected single identifier in refinement binder")
            }
            Self::ExpectedSortKeyword => f.write_str("expected sort keyword"),
            Self::ExpectedSubsetTypeXAWhereP => {
                f.write_str("expected subset type `{ x : A \\where P }`")
            }
            Self::MacroCapturesAreOnlyValidInMacroTemplates => {
                f.write_str("macro captures are only valid in macro templates")
            }
            Self::MissingContinueBranch => f.write_str("missing \\continue branch"),
            Self::MissingFinishBranch => f.write_str("missing \\finish branch"),
            Self::RefinementBindersAreNotAllowedInInductiveSignatures => {
                f.write_str("refinement binders are not allowed in inductive signatures")
            }
            Self::RestSplicesAreOnlyValidInMacroTemplates => {
                f.write_str("rest splices are only valid in macro templates")
            }
            Self::StepMatchExpectsARunstepType => f.write_str("step-match expects a RunStep type"),
            Self::TokenMatchingIsOnlyValidInNamedMacroTemplates => {
                f.write_str("token matching is only valid in named macro templates")
            }
            Self::UnmatchedCommentEnd => f.write_str("unmatched comment end"),
        }
    }
}
impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message())?;
        if let Some(source) = &self.source {
            write!(
                f,
                "\n{}",
                SourceLocation {
                    source: source.clone(),
                    span: self.span()
                }
                .render()
            )?;
        }
        Ok(())
    }
}
impl std::error::Error for ParseError {}

impl ParseErrorKind {
    pub fn diagnostic_data(&self) -> ::diagnostics::DiagnosticData {
        use ::diagnostics::DiagnosticData as Data;
        match self {
            Self::Expected { expected, found } => {
                let mut data =
                    Data::new("syntax.Expected").with("expected", expected.diagnostic_data());
                if let Some(found) = found {
                    data = data.with("found", found.diagnostic_data());
                }
                data
            }
            Self::Lex { text } => Data::new("syntax.Lex").with("text", text.clone()),
            Self::InvalidNumber { text } => {
                Data::new("syntax.InvalidNumber").with("text", text.clone())
            }
            Self::DuplicateStructureField { name } => {
                Data::new("syntax.DuplicateStructureField").with("name", name.clone())
            }
            Self::UnknownAxiom { name } => {
                Data::new("syntax.UnknownAxiom").with("name", name.clone())
            }
            Self::MetavariableNumberOverflow { text } => {
                Data::new("syntax.MetavariableNumberOverflow").with("text", text.clone())
            }
            Self::UnexpectedKeyword { keyword } => {
                Data::new("syntax.UnexpectedKeyword").with("keyword", keyword.clone())
            }
            Self::ExpectedProofField { name } => {
                Data::new("syntax.ExpectedProofField").with("name", name.clone())
            }
            Self::ExtraTokens { found } => {
                Data::new("syntax.ExtraTokens").with("found", found.diagnostic_data())
            }
            other => Data::new(format!("syntax.{other:?}")),
        }
    }
}
impl Expected {
    fn diagnostic_data(&self) -> ::diagnostics::DiagnosticData {
        use ::diagnostics::DiagnosticData as Data;
        match self {
            Self::Keyword(text) => Data::new("syntax.Keyword").with("text", text.clone()),
            Self::Token(token) => token.diagnostic_data(),
            other => Data::new(format!("syntax.Expected.{other:?}")),
        }
    }
}
impl ::diagnostics::DiagnosticError for ParseError {
    fn diagnostic_data(&self) -> ::diagnostics::DiagnosticData {
        let mut data = self
            .kind
            .diagnostic_data()
            .with("start", self.start)
            .with("end", self.end);
        if let Some(source) = &self.source {
            data = data.with("file", source.id.0.to_string_lossy().into_owned());
        }
        data
    }
}

impl OwnedToken {
    fn diagnostic_data(&self) -> ::diagnostics::DiagnosticData {
        match self {
            Self::KeyWord(text) => ::diagnostics::DiagnosticData::new("syntax.Token.KeyWord")
                .with("text", text.clone()),
            Self::MacroVar(text) => ::diagnostics::DiagnosticData::new("syntax.Token.MacroVar")
                .with("text", text.clone()),
            Self::MacroRest(text) => ::diagnostics::DiagnosticData::new("syntax.Token.MacroRest")
                .with("text", text.clone()),
            Self::QuotedMacro(text) => {
                ::diagnostics::DiagnosticData::new("syntax.Token.QuotedMacro")
                    .with("text", text.clone())
            }
            Self::EscapedMacro(text) => {
                ::diagnostics::DiagnosticData::new("syntax.Token.EscapedMacro")
                    .with("text", text.clone())
            }
            Self::Ident(text) => {
                ::diagnostics::DiagnosticData::new("syntax.Token.Ident").with("text", text.clone())
            }
            Self::Caret => ::diagnostics::DiagnosticData::new("syntax.Token.Caret"),
            Self::Number(text) => {
                ::diagnostics::DiagnosticData::new("syntax.Token.Number").with("text", text.clone())
            }
            Self::Metavariable(text) => {
                ::diagnostics::DiagnosticData::new("syntax.Token.Metavariable")
                    .with("text", text.clone())
            }
            Self::Hole => ::diagnostics::DiagnosticData::new("syntax.Token.Hole"),
            Self::Macro(text) => {
                ::diagnostics::DiagnosticData::new("syntax.Token.Macro").with("text", text.clone())
            }
            Self::LParen => ::diagnostics::DiagnosticData::new("syntax.Token.LParen"),
            Self::RParen => ::diagnostics::DiagnosticData::new("syntax.Token.RParen"),
            Self::MathLParen => ::diagnostics::DiagnosticData::new("syntax.Token.MathLParen"),
            Self::MathRParen => ::diagnostics::DiagnosticData::new("syntax.Token.MathRParen"),
            Self::CommentStart => ::diagnostics::DiagnosticData::new("syntax.Token.CommentStart"),
            Self::CommentEnd => ::diagnostics::DiagnosticData::new("syntax.Token.CommentEnd"),
            Self::LBrace => ::diagnostics::DiagnosticData::new("syntax.Token.LBrace"),
            Self::RBrace => ::diagnostics::DiagnosticData::new("syntax.Token.RBrace"),
            Self::LBracket => ::diagnostics::DiagnosticData::new("syntax.Token.LBracket"),
            Self::RBracket => ::diagnostics::DiagnosticData::new("syntax.Token.RBracket"),
            Self::ComputationArrow => {
                ::diagnostics::DiagnosticData::new("syntax.Token.ComputationArrow")
            }
            Self::BindArrow => ::diagnostics::DiagnosticData::new("syntax.Token.BindArrow"),
            Self::Arrow => ::diagnostics::DiagnosticData::new("syntax.Token.Arrow"),
            Self::DoubleArrow => ::diagnostics::DiagnosticData::new("syntax.Token.DoubleArrow"),
            Self::Assign => ::diagnostics::DiagnosticData::new("syntax.Token.Assign"),
            Self::Pipe => ::diagnostics::DiagnosticData::new("syntax.Token.Pipe"),
            Self::Colon => ::diagnostics::DiagnosticData::new("syntax.Token.Colon"),
            Self::Semicolon => ::diagnostics::DiagnosticData::new("syntax.Token.Semicolon"),
            Self::Period => ::diagnostics::DiagnosticData::new("syntax.Token.Period"),
            Self::Comma => ::diagnostics::DiagnosticData::new("syntax.Token.Comma"),
            Self::Equal => ::diagnostics::DiagnosticData::new("syntax.Token.Equal"),
            Self::Exclamation => ::diagnostics::DiagnosticData::new("syntax.Token.Exclamation"),
            Self::DoubleColon => ::diagnostics::DiagnosticData::new("syntax.Token.DoubleColon"),
            Self::RecordConstructor => {
                ::diagnostics::DiagnosticData::new("syntax.Token.RecordConstructor")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expected_tokens_are_retained_at_eof_and_before_other_tokens() {
        for (source, found) in [
            (r"\fun (x: \Set", None),
            (r"\fun (x: \Set]", Some(OwnedToken::RBracket)),
        ] {
            let error = str_parse_exp(source).unwrap_err();
            assert_eq!(
                error.kind,
                ParseErrorKind::Expected {
                    expected: Expected::Token(OwnedToken::RParen),
                    found,
                }
            );
            assert_eq!(error.span().end, source.len());
        }
    }
}
