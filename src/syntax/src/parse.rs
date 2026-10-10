use crate::{parse::term_parse::TermParser, syntax::*};
use logos::Logos;

#[derive(Logos, Debug, PartialEq, Clone, Copy)]
#[logos(skip r"\p{White_Space}+")]
enum Token<'a> {
    // Keywords (start from "\" character)
    #[regex(r"\\[a-zA-Z][a-zA-Z0-9-]*")]
    KeyWord(&'a str), // any concatenation of non-alphanumeric symbols without spaces
    #[regex(r"\$[a-zA-Z][a-zA-Z0-9_]*")]
    MacroVar(&'a str),
    #[regex(r"\.\.[a-zA-Z][a-zA-Z0-9_]*")]
    MacroRest(&'a str),
    #[regex(r#""[^"\n]*""#)]
    QuotedMacro(&'a str),
    #[regex(r"\\[^a-zA-Z0-9\s(){}$\[\]_,]+")]
    EscapedMacro(&'a str),
    #[regex(r"[a-zA-Z][a-zA-Z0-9_]*")]
    Ident(&'a str),
    #[token("^")]
    Caret,
    #[regex(r"[0-9]+")]
    Number(&'a str),
    #[token("?")]
    #[regex(r"_[0-9]+")]
    Metavariable(&'a str),
    #[token("_", priority = 3)]
    Hole,
    // Commas delimit patterns even when adjacent to a rest capture (`$x,..r`).
    // Other non-space symbol sequences are classified in lex_all.
    #[token("/\\")]
    #[regex(r#"[^\s\\A-Za-z0-9?(){}$\[\]_\",^]+"#)]
    Macro(&'a str),
    // special symbol tokens (which have their own meaning in parsing)
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("\\(")]
    MathLParen,
    #[token("\\)")]
    MathRParen,
    // comment tokens (will be ignored before lex_all output)
    #[token("/*")]
    CommentStart,
    #[token("*/")]
    CommentEnd,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    // mapped tokens (will be produced by mapping MacroToken in lex_all)
    // 2 char
    ComputationArrow, // "~>"
    BindArrow,        // "<-"
    Arrow,            // "->"
    DoubleArrow,      // "=>"
    Assign,           // ":="
    // 1 char
    Pipe,      // "|"
    Colon,     // ":"
    Semicolon, // ";"
    Period,    // "."
    #[token(",")]
    Comma, // ","
    Equal,     // "="
    Exclamation, // "!"
    DoubleColon, // "::"
    RecordConstructor, // "::#"
}

static SORT_KEYWORDS: &[&str] = &["\\Prop", "\\PropKind", "\\Set", "\\SetKind"];

static EXPRESSION_ATOM_KEYWORDS: &[&str] = &[
    "\\induction", // function-valued inductive eliminator
    "\\Pow",
    "\\In",
    "\\Cast",
    "\\into",
    "\\fun",
    "\\forall",
    "\\cfun",
    "\\match",
    "\\tmatch",
    "\\VType",
    "\\U",
    "\\F",
    "\\thunk",
    "\\return",
    "\\force",
    "\\squash",
    "\\RunStep",
    "\\continue",
    "\\finish",
    "\\run",
    "\\runCase",
    "\\step-match",
    "\\Box",
    "\\box",
    "\\boxapp",
    "\\exists", // \exists <Bind>
    "\\choice",
    "\\take",     // \take <Bind> => <body>
    "\\takefrom", // \takefrom <var>: <type> \by <existence>;
    "\\block",    // block expression
    "\\program",  // Program block expression
];

static PROOF_TERM_KEYWORDS: &[&str] = &[
    "\\exact",
    "\\bysub",
    "\\refl",
    "\\idelim",
    "\\transporteq",
    "\\axiom",
    "\\choiceeq",
];

fn lex_all<'a>(input: &'a str) -> Result<Vec<SpannedToken<'a>>, ParseError> {
    lex_with_comments(input, |_| {})
}

fn lex_with_comments<'a>(
    input: &'a str,
    mut comment: impl FnMut(SourceSpan),
) -> Result<Vec<SpannedToken<'a>>, ParseError> {
    let mut lexer = Token::lexer(input);
    let mut out = Vec::new();

    let mut comment_level = 0;
    let mut comment_start = 0;

    while let Some(tok) = lexer.next() {
        match tok {
            Ok(Token::CommentStart) => {
                if comment_level == 0 {
                    comment_start = lexer.span().start;
                }
                comment_level += 1;
            }
            Ok(Token::CommentEnd) => {
                if comment_level == 0 {
                    return Err(ParseError {
                        kind: ParseErrorKind::UnmatchedCommentEnd,
                        start: lexer.span().start,
                        end: lexer.span().end,
                        source: None,
                    });
                }
                comment_level -= 1;
                if comment_level == 0 {
                    comment(SourceSpan {
                        start: comment_start,
                        end: lexer.span().end,
                    });
                }
            }
            Ok(_) if comment_level > 0 => {
                continue; // skip tokens inside comments
            }
            Ok(Token::Macro(s)) => {
                // map known symbol sequences to specific token variants
                let mapped = match s {
                    "~>" => Token::ComputationArrow,
                    "<-" => Token::BindArrow,
                    "->" => Token::Arrow,
                    "=>" => Token::DoubleArrow,
                    ":=" => Token::Assign,
                    "|" => Token::Pipe,
                    ":" => Token::Colon,
                    ";" => Token::Semicolon,
                    "." => Token::Period,
                    "=" => Token::Equal,
                    "!" => Token::Exclamation,
                    "::" => Token::DoubleColon,
                    "::#" => Token::RecordConstructor,
                    _ => Token::Macro(s),
                };

                let span = lexer.span();
                out.push(SpannedToken {
                    kind: mapped,
                    start: span.start,
                    end: span.end,
                });
            }
            Ok(kind) => {
                let span = lexer.span();
                out.push(SpannedToken {
                    kind,
                    start: span.start,
                    end: span.end,
                });
            }
            Err(_) => {
                let span = lexer.span();
                let bad = &input[span.clone()];
                return Err(ParseError {
                    kind: ParseErrorKind::Lex {
                        text: bad.to_owned(),
                    },
                    start: span.start,
                    end: span.end,
                    source: None,
                });
            }
        }
    }

    Ok(out)
}

#[derive(Debug, Clone, Copy)]
struct SpannedToken<'a> {
    kind: Token<'a>,
    start: usize,
    end: usize,
}

mod diagnostics;
pub use diagnostics::{Expected, OwnedToken, ParseError, ParseErrorKind};

pub mod documentation;
mod term_parse;

trait TokenCursor<'a>: Sized {
    fn tokens(&self) -> &'a [SpannedToken<'a>];

    fn span_at(&self, position: usize) -> SourceSpan {
        self.tokens().get(position).map_or_else(
            || {
                let end = self.tokens().last().map_or(0, |token| token.end);
                SourceSpan { start: end, end }
            },
            |token| SourceSpan {
                start: token.start,
                end: token.end,
            },
        )
    }

    fn eof_error(&self, expected: Expected) -> ParseError {
        let span = self.span_at(self.tokens().len());
        ParseError {
            kind: ParseErrorKind::Expected {
                expected,
                found: None,
            },
            start: span.start,
            end: span.end,
            source: None,
        }
    }

    fn position(&self) -> usize;
    fn set_position(&mut self, position: usize);

    fn peek(&self) -> Option<&'a Token<'a>> {
        self.tokens().get(self.position()).map(|token| &token.kind)
    }

    fn next(&mut self) -> Option<&'a SpannedToken<'a>> {
        let token = self.tokens().get(self.position());
        if token.is_some() {
            self.set_position(self.position() + 1);
        }
        token
    }

    fn bump_if_token(&mut self, expected: Token<'a>) -> bool {
        if self.peek() == Some(&expected) {
            self.set_position(self.position() + 1);
            return true;
        }
        false
    }

    fn bump_if_keyword(&mut self, keyword: &str) -> bool {
        if let Some(Token::KeyWord(actual)) = self.peek()
            && *actual == keyword
        {
            self.set_position(self.position() + 1);
            return true;
        }
        false
    }

    fn expect_token(&mut self, expected: Token<'a>) -> Result<SpannedToken<'a>, ParseError> {
        if let Some(token) = self.tokens().get(self.position()) {
            if token.kind == expected {
                self.set_position(self.position() + 1);
                Ok(*token)
            } else {
                Err(ParseError {
                    kind: ParseErrorKind::Expected {
                        expected: Expected::Token(expected.owned()),
                        found: Some(token.kind.owned()),
                    },
                    start: token.start,
                    end: token.end,
                    source: None,
                })
            }
        } else {
            Err(self.eof_error(Expected::Token(expected.owned())))
        }
    }

    fn expect_keyword(&mut self, keyword: &str) -> Result<&'a str, ParseError> {
        match self.next() {
            Some(token) => match token.kind {
                Token::KeyWord(actual) if actual == keyword => Ok(actual),
                other => Err(ParseError {
                    kind: ParseErrorKind::Expected {
                        expected: Expected::Keyword(keyword.to_owned()),
                        found: Some(other.owned()),
                    },
                    start: token.start,
                    end: token.end,
                    source: None,
                }),
            },
            None => Err(self.eof_error(Expected::Keyword(keyword.to_owned()))),
        }
    }

    fn expect_ident(&mut self) -> Result<Identifier, ParseError> {
        match self.next() {
            Some(token) => match token.kind {
                Token::Ident(name) => Ok(Identifier(name.to_owned())),
                other => Err(ParseError {
                    kind: ParseErrorKind::Expected {
                        expected: Expected::Identifier,
                        found: Some(other.owned()),
                    },
                    start: token.start,
                    end: token.end,
                    source: None,
                }),
            },
            None => Err(self.eof_error(Expected::Identifier)),
        }
    }
}

#[derive(Debug)]
struct Parser<'a> {
    tokens: &'a [SpannedToken<'a>],
    pos: usize,
}

// `fn bump_if_*` consumes tokens only if matched
// `fn parse_*` consumes tokens whether succeed or fail, the parser position is advanced
// A selected production commits: errors never restore the cursor.
impl<'a> Parser<'a> {
    fn new(tokens: &'a [SpannedToken<'a>]) -> Self {
        Self { tokens, pos: 0 }
    }

    fn parse_sexp(&mut self) -> Result<SExp, ParseError> {
        let mut term_parser = TermParser::new(&self.tokens[self.pos..]);
        let (sexp, consumed) = term_parser.parse_sexp_advanced()?;
        self.pos += consumed;
        Ok(sexp)
    }

    fn parse_macro_template(&mut self) -> Result<SExp, ParseError> {
        let mut term_parser = TermParser::new_macro_template(&self.tokens[self.pos..]);
        let (sexp, consumed) = term_parser.parse_sexp_advanced()?;
        self.pos += consumed;
        Ok(sexp)
    }

    fn parse_arrow_nosubset(&mut self) -> Result<(Vec<RightBind>, SExp), ParseError> {
        let mut term_parser = TermParser::new(&self.tokens[self.pos..]);
        let (rightbinds, sexp, consumed) = term_parser.parse_arrow_nosubset_advanced()?;
        self.pos += consumed;
        Ok((rightbinds, sexp))
    }

    // "(" <ident> ("," <ident>)* ":" <ty: SExp> ")"
    fn parse_rightbinds(&mut self) -> Result<Vec<RightBind>, ParseError> {
        let mut term_parser = TermParser::new(&self.tokens[self.pos..]);
        let (rightbind, advanced) = term_parser.parse_simple_binds_advanced()?;
        self.pos += advanced;
        Ok(rightbind)
    }

    fn parse_bracketed_rightbinds(&mut self) -> Result<Vec<RightBind>, ParseError> {
        let mut term_parser = TermParser::new(&self.tokens[self.pos..]);
        let (rightbind, advanced) = term_parser.parse_simple_binds_bracketed_advanced()?;
        self.pos += advanced;
        Ok(rightbind)
    }

    // <var: Ident> ":" <ty: SExp> ":=" <body: SExp> ";"
    fn parse_definition(&mut self) -> Result<ModuleItem, ParseError> {
        let first_name = self.expect_ident()?;
        let mut first_binders = Vec::new();
        while matches!(self.peek(), Some(Token::LParen | Token::LBracket)) {
            let binders = if self.peek() == Some(&Token::LBracket) {
                self.parse_bracketed_rightbinds()?
            } else {
                self.parse_rightbinds()?
            };
            first_binders.extend(binders);
        }
        let (owner, name, binders) = if self.bump_if_token(Token::DoubleColon) {
            let name = self.expect_ident()?;
            let mut binders = Vec::new();
            while self.peek() == Some(&Token::LParen) {
                let parsed = self.parse_rightbinds()?;
                binders.extend(parsed);
            }
            (
                Some(AssociatedOwner {
                    type_name: first_name,
                    parameters: first_binders,
                }),
                name,
                binders,
            )
        } else {
            (None, first_name, first_binders)
        };
        self.expect_token(Token::Colon)?;
        let ty = self.parse_sexp()?;
        self.expect_token(Token::Assign)?;
        let body = self.parse_sexp()?;
        self.expect_token(Token::Semicolon)?;
        Ok(ModuleItem::Definition {
            owner,
            name,
            binders,
            ty,
            body,
        })
    }

    fn parse_structure(&mut self) -> Result<ModuleItem, ParseError> {
        let name = self.expect_ident()?;
        let mut parameters = Vec::new();
        while self.peek() == Some(&Token::LBracket) {
            parameters.extend(self.parse_bracketed_rightbinds()?);
        }
        let kind = if self.peek() == Some(&Token::LBrace) {
            None
        } else {
            self.expect_token(Token::Colon)?;
            let kind = match self.parse_sexp()? {
                SExp::Sort(sort) => InductiveKind::Pts(sort),
                SExp::ValueType => InductiveKind::Program,
                _ => return Err(self.eof_error(Expected::StructureSort)),
            };
            self.bump_if_token(Token::Assign);
            Some(kind)
        };
        let mut field_spans = Vec::new();
        let fields = self.parse_structure_fields(&mut field_spans)?;
        let mut names = std::collections::HashSet::new();
        for (field, _, _) in &fields {
            if !names.insert(field.as_str()) {
                return Err(ParseError {
                    kind: ParseErrorKind::DuplicateStructureField {
                        name: field.0.clone(),
                    },
                    start: self.span_at(self.pos - 1).start,
                    end: self.span_at(self.pos - 1).end,
                    source: None,
                });
            }
        }
        self.bump_if_token(Token::Semicolon);
        Ok(ModuleItem::Structure {
            name,
            parameters,
            kind,
            fields,
            field_spans,
        })
    }

    fn parse_structure_fields(
        &mut self,
        spans: &mut Vec<SourceSpan>,
    ) -> Result<Vec<(Identifier, SExp, Option<SExp>)>, ParseError> {
        self.expect_token(Token::LBrace)?;
        let mut fields = Vec::new();
        while !self.bump_if_token(Token::RBrace) {
            let start = self.span_at(self.pos).start;
            let name = self.expect_ident()?;
            self.expect_token(Token::Colon)?;
            let ty = self.parse_sexp()?;
            let default = if self.bump_if_token(Token::Assign) {
                Some(self.parse_sexp()?)
            } else {
                None
            };
            fields.push((name, ty, default));
            spans.push(SourceSpan {
                start,
                end: self.span_at(self.pos - 1).end,
            });
            if self.bump_if_token(Token::RBrace) {
                break;
            }
            self.expect_token(Token::Comma)?;
        }
        Ok(fields)
    }

    // (cosumed "\import" keyword) <path: ModuleAccessPath> "\as" <import_name: Ident> ";"
    fn parse_module_selection(&mut self) -> Result<ModuleInstantiatePath, ParseError> {
        let rooted = if self.bump_if_token(Token::Period) {
            Some(Some(0))
        } else if self.bump_if_keyword("\\root") {
            self.expect_token(Token::Period)?; // expect '.'
            Some(None)
        } else {
            let mut count = 0;
            while self.bump_if_keyword("\\parent") {
                count += 1;
                self.expect_token(Token::Period)?; // expect '.'
            }
            (count > 0).then_some(Some(count))
        };

        let mut calls = vec![];
        let starts_from_import = rooted.is_none()
            && matches!(
                self.tokens.get(self.pos).map(|token| &token.kind),
                Some(Token::Ident(_))
            )
            && matches!(
                self.tokens.get(self.pos + 1).map(|token| &token.kind),
                Some(Token::Period | Token::DoubleColon)
            );
        let imported_parent = if starts_from_import {
            let candidate = self.expect_ident()?;
            if !self.bump_if_token(Token::Period)
                && self.peek() == Some(&Token::DoubleColon)
                && matches!(
                    self.tokens.get(self.pos + 2).map(|token| &token.kind),
                    Some(Token::LBracket)
                )
            {
                self.expect_token(Token::DoubleColon)?;
            }
            Some(candidate)
        } else {
            None
        };

        if matches!(self.peek(), Some(Token::Ident(_))) {
            loop {
                calls.push(self.parse_module_access_path()?);
                if !self.bump_if_token(Token::Period) {
                    break;
                }
            }
        }

        let path = if let Some(import_name) = imported_parent {
            ModuleInstantiatePath::FromImport { import_name, calls }
        } else {
            match rooted.unwrap_or(Some(0)) {
                Some(num) => ModuleInstantiatePath::FromCurrent {
                    back_parent: num,
                    calls,
                },
                None => ModuleInstantiatePath::FromRoot { calls },
            }
        };

        Ok(path)
    }

    fn parse_import(&mut self) -> Result<ModuleItem, ParseError> {
        let path = self.parse_module_selection()?;
        self.expect_keyword("\\as")?;
        let import_name = self.expect_ident()?;
        self.expect_token(Token::Semicolon)?;
        Ok(ModuleItem::Import { path, import_name })
    }

    // <specified_module> = <mod_name> "[" (<param: Ident> ":=" <arg: SExp> ",")* "]"
    fn parse_module_access_path(
        &mut self,
    ) -> Result<(Identifier, Vec<(Identifier, SExp)>), ParseError> {
        let module_name = self.expect_ident()?;
        self.expect_token(Token::LBracket)?;

        let mut assign_pairs = Vec::new();
        if !self.bump_if_token(Token::RBracket) {
            loop {
                let param = self.expect_ident()?;
                self.expect_token(Token::Assign)?; // expect ':='
                let arg = self.parse_sexp()?;
                assign_pairs.push((param, arg));

                if self.bump_if_token(Token::RBracket) {
                    break; // end of parameter list
                }
                self.expect_token(Token::Comma)?; // expect ','
            }
        }

        Ok((module_name, assign_pairs))
    }

    // "|" <ctor_name: Ident> ":" <rightbinds> "->" <SExp>
    fn parse_ctor_decl(&mut self) -> Result<(Identifier, Vec<RightBind>, SExp), ParseError> {
        self.expect_token(Token::Pipe)?; // expect '|'
        let ctor_name = self.expect_ident()?;
        self.expect_token(Token::Colon)?; // expect ':'
        let (rightbinds, ends) = self.parse_arrow_nosubset()?;
        Ok((ctor_name, rightbinds, ends))
    }

    //  <type_name: Ident> ("[" <param: Ident> ":" <ty: SExp> "]")* ":" <arity> ":=" (<ctor_decl>)* ";"
    fn parse_inductive_decl(&mut self) -> Result<ModuleItem, ParseError> {
        let type_name = self.expect_ident()?;

        let mut parameters = vec![];

        while self.peek() == Some(&Token::LBracket) {
            let param = self.parse_bracketed_rightbinds()?;
            parameters.extend(param);
        }

        self.expect_token(Token::Colon)?;

        // <arity> = <indices> <Sort>
        // <indices> = <rightbinds>
        let (indices, expect_sort) = self.parse_arrow_nosubset()?;
        let kind = match expect_sort {
            SExp::Sort(s) => InductiveKind::Pts(s),
            SExp::ValueType if indices.is_empty() => InductiveKind::Program,
            SExp::ValueType => {
                return Err(ParseError {
                    kind: ParseErrorKind::ProgramDatatypeDeclarationsCannotHaveIndices,
                    start: self.span_at(self.pos.saturating_sub(1)).start,
                    end: self.span_at(self.pos.saturating_sub(1)).end,
                    source: None,
                });
            }
            _ => {
                return Err(ParseError {
                    kind: ParseErrorKind::ExpectedPtsSortOrVtypeInInductiveDeclaration,
                    start: self.span_at(self.pos.saturating_sub(1)).start,
                    end: self.span_at(self.pos.saturating_sub(1)).end,
                    source: None,
                });
            }
        };

        // body of constructors
        self.expect_token(Token::Assign)?;
        let mut constructors = vec![];
        while self.peek() == Some(&Token::Pipe) {
            constructors.push(self.parse_ctor_decl()?);
        }
        self.expect_token(Token::Semicolon)?;
        Ok(ModuleItem::Inductive {
            type_name,
            parameters,
            indices,
            kind,
            constructors,
        })
    }

    fn parse_macro_pattern_atom(&mut self) -> Result<MacroSeqAtom, ParseError> {
        match self.next() {
            Some(SpannedToken {
                kind: Token::MacroVar(name),
                ..
            }) => Ok(MacroSeqAtom::Capture(Identifier(name[1..].to_string()))),
            Some(SpannedToken {
                kind: Token::Ident(name),
                ..
            }) => Ok(MacroSeqAtom::TokenCapture(Identifier(name.to_string()))),
            Some(SpannedToken {
                kind: Token::MacroRest(name),
                ..
            }) => Ok(MacroSeqAtom::Rest(Identifier(name[2..].to_string()))),
            Some(SpannedToken {
                kind: Token::EscapedMacro(token),
                ..
            }) => Ok(MacroSeqAtom::Tok(MacroToken(token[1..].to_string()))),
            Some(SpannedToken {
                kind: Token::QuotedMacro(token),
                ..
            }) => Ok(MacroSeqAtom::Quoted(token[1..token.len() - 1].to_string())),
            Some(SpannedToken {
                kind: Token::LParen,
                ..
            }) => {
                let atoms = self.parse_macro_pattern_items(Token::RParen)?;
                self.expect_token(Token::RParen)?;
                Ok(MacroSeqAtom::Seq(atoms))
            }
            Some(token) => Err(ParseError {
                kind: ParseErrorKind::Expected {
                    expected: Expected::MacroPatternElement,
                    found: Some(token.kind.owned()),
                },
                start: token.start,
                end: token.end,
                source: None,
            }),
            None => Err(self.eof_error(Expected::MacroPatternAtom)),
        }
    }

    fn parse_macro_pattern_items(
        &mut self,
        close: Token<'a>,
    ) -> Result<Vec<MacroSeqAtom>, ParseError> {
        let mut atoms = Vec::new();
        if self.peek() == Some(&close) {
            return Ok(atoms);
        }
        loop {
            atoms.push(self.parse_macro_pattern_atom()?);
            if self.peek() == Some(&close) {
                return Ok(atoms);
            }
            self.expect_token(Token::Comma)?;
        }
    }

    fn parse_macro_decl(&mut self, math: bool) -> Result<ModuleItem, ParseError> {
        let name = self.expect_ident()?;
        self.expect_token(Token::LParen)?;
        let before = self.parse_macro_pattern_items(Token::RParen)?;
        self.expect_token(Token::RParen)?;
        self.expect_token(Token::Assign)?;
        let after = self.parse_macro_template()?;
        self.expect_token(Token::Semicolon)?;
        Ok(if math {
            ModuleItem::MathMacro {
                name,
                before,
                after,
            }
        } else {
            ModuleItem::UserMacro {
                name,
                before,
                after,
            }
        })
    }

    fn parse_use_macro(&mut self) -> Result<ModuleItem, ParseError> {
        let path = self.parse_module_selection()?;
        self.expect_token(Token::DoubleColon)?;
        let macro_name = self.expect_ident()?;
        let name = if self.bump_if_keyword("\\as") {
            self.expect_ident()?
        } else {
            macro_name.clone()
        };
        self.expect_token(Token::Semicolon)?;
        Ok(ModuleItem::UseMacro {
            path,
            macro_name,
            name,
        })
    }

    fn try_parse_module_item(&mut self) -> Result<Option<ModuleItem>, ParseError> {
        if self.bump_if_keyword("\\structure") {
            return self.parse_structure().map(Some);
        }
        if self.bump_if_keyword("\\definition")
            || self.bump_if_keyword("\\machine")
            || self.bump_if_keyword("\\correspondence")
        {
            let def = self.parse_definition()?;
            return Ok(Some(def));
        }
        if self.bump_if_keyword("\\import") {
            let imp = self.parse_import()?;
            return Ok(Some(imp));
        }
        if self.bump_if_keyword("\\inductive") {
            let ind = self.parse_inductive_decl()?;
            return Ok(Some(ind));
        }
        if self.bump_if_keyword("\\math-macro") {
            return self.parse_macro_decl(true).map(Some);
        }
        if self.bump_if_keyword("\\macro") {
            return self.parse_macro_decl(false).map(Some);
        }
        if self.bump_if_keyword("\\use") {
            return self.parse_use_macro().map(Some);
        }
        if self.peek() == Some(&Token::KeyWord("\\module")) {
            let module = self.parse_module()?;
            return Ok(Some(ModuleItem::ChildModule {
                module: module.into(),
            }));
        }
        if self.bump_if_keyword("\\eval") {
            let exp = self.parse_sexp()?;
            self.expect_token(Token::Semicolon)?;
            return Ok(Some(ModuleItem::Eval { exp }));
        }
        if self.bump_if_keyword("\\normalize") {
            let exp = self.parse_sexp()?;
            self.expect_token(Token::Semicolon)?;
            return Ok(Some(ModuleItem::Normalize { exp }));
        }
        if self.bump_if_keyword("\\check") {
            let exp = self.parse_sexp()?;
            self.expect_token(Token::Colon)?;
            let ty = self.parse_sexp()?;
            self.expect_token(Token::Semicolon)?;
            return Ok(Some(ModuleItem::Check { exp, ty }));
        }
        if self.bump_if_keyword("\\infer") {
            let exp = self.parse_sexp()?;
            self.expect_token(Token::Semicolon)?;
            return Ok(Some(ModuleItem::Infer { exp }));
        }
        Ok(None)
    }

    // parse an inline or external module
    // "\module" <module_name: Ident> <parameters>? ("{" (<module_item>)* "}" | ";")
    fn parse_module(&mut self) -> Result<Module, ParseError> {
        let start = self.tokens.get(self.pos).map_or(0, |token| token.start);
        let mut declaration_spans = Vec::new();
        self.expect_keyword("\\module")?;
        let module_name = self.expect_ident()?;

        let parameters = if self.peek() == Some(&Token::LParen) {
            self.parse_rightbinds()?
        } else {
            Vec::new()
        };

        let body = if self.bump_if_token(Token::Semicolon) {
            ModuleBody::External
        } else {
            self.expect_token(Token::LBrace)?; // expect '{'
            let (declarations, spans) = self.parse_module_items_with_spans()?;
            declaration_spans = spans;
            self.expect_token(Token::RBrace)?; // expect '}'
            ModuleBody::Inline(declarations)
        };

        Ok(Module {
            name: module_name,
            parameters,
            body,
            span: SourceSpan {
                start,
                end: self.tokens[self.pos - 1].end,
            },
            declaration_spans,
            source: None,
            header_source: None,
        })
    }

    fn parse_module_items_with_spans(
        &mut self,
    ) -> Result<(Vec<ModuleItem>, Vec<SourceSpan>), ParseError> {
        let mut declarations = Vec::new();
        let mut spans = Vec::new();
        loop {
            let start = self.tokens.get(self.pos).map_or(0, |token| token.start);
            let Some(item) = self.try_parse_module_item()? else {
                break;
            };
            spans.push(SourceSpan {
                start,
                end: self.tokens[self.pos - 1].end,
            });
            declarations.push(item);
        }
        Ok((declarations, spans))
    }
}

impl<'a> TokenCursor<'a> for Parser<'a> {
    fn tokens(&self) -> &'a [SpannedToken<'a>] {
        self.tokens
    }

    fn position(&self) -> usize {
        self.pos
    }

    fn set_position(&mut self, position: usize) {
        debug_assert!(
            position >= self.pos,
            "parser cursor must never move backwards"
        );
        self.pos = position;
    }
}

/// The identifier of a macro declaration, excluding its keyword and comments.
pub fn macro_declaration_name_span(input: &str, name: &str) -> Option<SourceSpan> {
    let tokens = lex_all(input).ok()?;
    tokens.windows(2).find_map(|tokens| {
        (matches!(tokens[0].kind, Token::KeyWord("\\macro" | "\\math-macro"))
            && matches!(tokens[1].kind, Token::Ident(actual) if actual == name))
        .then_some(SourceSpan {
            start: tokens[1].start,
            end: tokens[1].end,
        })
    })
}

/// Source occurrences of named macro calls, excluding comments and quoted tokens.
pub fn named_macro_call_spans(input: &str, name: &str) -> Vec<SourceSpan> {
    let Ok(tokens) = lex_all(input) else {
        return Vec::new();
    };
    tokens
        .windows(2)
        .filter_map(|tokens| {
            (matches!(tokens[0].kind, Token::Ident(actual) if actual == name)
                && tokens[1].kind == Token::Exclamation
                && tokens[0].end == tokens[1].start)
                .then_some(SourceSpan {
                    start: tokens[0].start,
                    end: tokens[0].end,
                })
        })
        .collect()
}

pub fn str_parse_exp(input: &str) -> Result<SExp, ParseError> {
    let tokens = lex_all(input)?;
    let mut parser = Parser::new(&tokens);
    let expression = parser.parse_sexp()?;
    if let Some(extra) = parser.tokens.get(parser.pos) {
        return Err(ParseError {
            kind: ParseErrorKind::ExtraTokens {
                found: extra.kind.owned(),
            },
            start: extra.start,
            end: extra.end,
            source: None,
        });
    }
    Ok(expression)
}

pub fn str_parse_modules(input: &str) -> Result<Vec<Module>, ParseError> {
    parse_root(input)
}

pub fn parse_modules_from_source(
    source: &std::sync::Arc<SourceFile>,
) -> Result<Vec<Module>, ParseError> {
    parse_root(&source.text).map_err(|error| error.with_source(source.clone()))
}

pub fn parse_root(input: &str) -> Result<Vec<Module>, ParseError> {
    let tokens = lex_all(input)?;
    let mut parser = Parser::new(&tokens);
    let mut modules = Vec::new();
    while parser.pos < parser.tokens.len() {
        modules.push(parser.parse_module()?);
    }
    Ok(modules)
}

pub fn parse_module_items_from_source(
    source: &std::sync::Arc<SourceFile>,
) -> Result<(Vec<ModuleItem>, Vec<SourceSpan>), ParseError> {
    parse_items(&source.text).map_err(|error| error.with_source(source.clone()))
}

pub fn parse_items(input: &str) -> Result<(Vec<ModuleItem>, Vec<SourceSpan>), ParseError> {
    let tokens = lex_all(input)?;
    let mut parser = Parser::new(&tokens);
    let declarations = parser.parse_module_items_with_spans()?;
    if let Some(extra) = parser.tokens.get(parser.pos) {
        return Err(ParseError {
            kind: ParseErrorKind::Expected {
                expected: Expected::ModuleItem,
                found: Some(extra.kind.owned()),
            },
            start: extra.start,
            end: extra.end,
            source: None,
        });
    }
    Ok(declarations)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn logos_test() {
        fn tok_all_ok(input: &'static str) {
            let mut toks = Token::lexer(input);
            loop {
                match toks.next() {
                    Some(Ok(ok)) => {
                        println!("span[{:?}] slice[{}]", toks.span(), toks.slice());
                        println!("  {:?}", ok);
                    }
                    Some(Err(_)) => panic!("lex error in input: {}", input),
                    None => break,
                }
            }
        }
        tok_all_ok(r"\forall (x: X) -> Y => z");
        tok_all_ok(r"(x @ z # a");
        tok_all_ok(r"x \( y += z \)");
    }
    #[test]
    fn lexer_test() {
        fn print_and_unwrap(input: &'static str) {
            println!("Input: {:?}", input);
            let spantoks = &lex_all(input).unwrap();
            for tok in spantoks {
                println!("{:?}", tok);
            }
        }
        print_and_unwrap(r"\forall (x: X) -> Y => z");
        print_and_unwrap(r"x \( y + z \) l");
        print_and_unwrap(r"x mymacro!{ a + b c } l");
        print_and_unwrap(r"x /* this is a comment */ (y z)");
        print_and_unwrap(r"x :: y ++ := z");
        print_and_unwrap(r"\Prop \Set (0)");
        print_and_unwrap(r"(( \( \) ))");
        print_and_unwrap(r"x.y # name { hello: ");
    }

    #[test]
    fn machine_and_correspondence_preserve_typed_definition_items() {
        for keyword in ["machine", "correspondence"] {
            let source = format!("\\{keyword} implementation: Program := witness;");
            let (actual, spans) = parse_items(&source).unwrap();
            let [
                ModuleItem::Definition {
                    owner,
                    name,
                    binders,
                    ty,
                    body,
                },
            ] = actual.as_slice()
            else {
                panic!("expected a typed definition: {actual:?}");
            };
            assert!(owner.is_none());
            assert_eq!(name.0, "implementation");
            assert!(binders.is_empty());
            for (term, expected) in [(ty, "Program"), (body, "witness")] {
                let SExp::AccessPath {
                    access: LocalAccess::Current { access: name, .. },
                    parameters,
                } = term
                else {
                    panic!("expected an unqualified name: {term:?}");
                };
                assert_eq!(name.0, expected);
                assert!(parameters.is_empty());
            }
            assert_eq!(spans.len(), 1);
            assert_eq!(spans[0].start, 0);
            assert_eq!(spans[0].end, source.len());
        }
    }

    #[test]
    fn malformed_declarations_do_not_end_optional_lists() {
        for input in [
            r"\definition f(x: A, y): A := x;",
            r"\module M(x: A, y) {}",
            r"\inductive T: \Set := | ctor: ;",
            r"\import M[x := ] \as Alias;",
            r"\import M[]. \as Alias;",
        ] {
            let tokens = lex_all(input).unwrap();
            let mut parser = Parser::new(&tokens);
            let error = parser.try_parse_module_item().unwrap_err();
            assert!(error.start > 0, "lost failure position: {input}: {error:?}");
        }
        let input = r"\definition f: A := x";
        let tokens = lex_all(input).unwrap();
        let error = Parser::new(&tokens).try_parse_module_item().unwrap_err();
        assert_eq!((error.start, error.end), (input.len(), input.len()));
    }

    #[test]
    fn parse_rightbinds_test() {
        fn print_and_unwrap(input: &'static str) {
            let lex = &lex_all(input).unwrap();
            let mut parser = Parser::new(lex);
            let binds = parser.parse_rightbinds().unwrap();
            println!("Parsed RightBinds: {:?} => {:?}", input, binds);
        }
        print_and_unwrap(r"(x: X)");
        print_and_unwrap(r"(x: X, y: Y, z: Z)");
        print_and_unwrap(r"(P1: \Prop,  p1: P1, )");
    }
    #[test]
    fn pares_ctor_decl_test() {
        fn print_and_unwrap(input: &'static str) {
            let lex = &lex_all(input).unwrap();
            let mut parser = Parser::new(lex);
            let ctor = parser.parse_ctor_decl().unwrap();
            println!("Parsed CtorDecl: {:?} => {:?}", input, ctor);
        }
        print_and_unwrap(r"| true : Bool");
        print_and_unwrap(r"| succ : Nat -> Nat");
        print_and_unwrap(r"| u: A -> B -> U");
        print_and_unwrap(r"| cons : \forall (X : \Set) -> X -> List X -> List X");
    }
    #[test]
    fn parse_module_item() {
        fn print_and_unwrap(input: &'static str) {
            let lex = &lex_all(input).unwrap();
            let mut parser = Parser::new(lex);
            let item = parser.try_parse_module_item();
            match item {
                Ok(Some(mi)) => {
                    println!("Parsed ModuleItem: {:?} => {:?}", input, mi);
                }
                Ok(None) => {
                    panic!("Failed to parse ModuleItem: {}", input);
                }
                Err(err) => {
                    panic!("Error: {:?}", err);
                }
            }
        }
        print_and_unwrap(r"\definition id : \forall (X : \Set) -> X -> X := \fun (x : X) => x ;");
        print_and_unwrap(r"\definition l : \forall (X : \Set) -> X -> X := \fun (x : X) => x ;");
        print_and_unwrap(
            r"\definition l: \forall (X, Y: \Set) -> \SetKind := \fun (_: \Set) => a;",
        );
        print_and_unwrap(r"\definition one: Nat := Nat::succ Nat::zero;");
        print_and_unwrap(r"\import MyModule [] \as ImportedModule ;");
        print_and_unwrap(r"\import MyModule [ A := B, C := \fun (x: X) => y] \as T;");
        print_and_unwrap(r"\inductive Bool : \Set := | true : Bool | false : Bool;");
        print_and_unwrap(r"\inductive Nat : \Set := | zero : Nat | succ : Nat -> Nat;");
    }
}
