use super::{
    EXPRESSION_ATOM_KEYWORDS, PROOF_TERM_KEYWORDS, ParseError, Parser, SORT_KEYWORDS, SpannedToken,
    Token, TokenCursor,
};
use super::{Expected, ParseErrorKind};
use crate::syntax::*;

pub(super) struct TermParser<'a> {
    tokens: &'a [SpannedToken<'a>],
    pos: usize,
    allow_macro_parameters: bool,
    allow_empty_record_literal: bool,
    #[cfg(test)]
    consumed: usize,
}

impl<'a> TermParser<'a> {
    pub(super) fn new(tokens: &'a [SpannedToken<'a>]) -> Self {
        Self {
            tokens,
            pos: 0,
            allow_macro_parameters: false,
            allow_empty_record_literal: true,
            #[cfg(test)]
            consumed: 0,
        }
    }

    pub(super) fn new_macro_template(tokens: &'a [SpannedToken<'a>]) -> Self {
        Self {
            tokens,
            pos: 0,
            allow_macro_parameters: true,
            allow_empty_record_literal: true,
            #[cfg(test)]
            consumed: 0,
        }
    }

    fn expect_binder_ident(&mut self) -> Result<Identifier, ParseError> {
        match self.peek() {
            Some(Token::Hole) => {
                self.next();
                Ok(Identifier("_".into()))
            }
            _ => self.expect_ident(),
        }
    }

    fn expect_number(&mut self) -> Result<usize, ParseError> {
        match self.next() {
            Some(t) => match &t.kind {
                Token::Number(num_str) => match num_str.parse::<usize>() {
                    Ok(n) => Ok(n),
                    Err(_) => Err(ParseError {
                        kind: ParseErrorKind::InvalidNumber {
                            text: (*num_str).to_owned(),
                        },
                        start: t.start,
                        end: t.end,
                        source: None,
                    }),
                },
                other => Err(ParseError {
                    kind: ParseErrorKind::Expected {
                        expected: Expected::Number,
                        found: Some(other.owned()),
                    },
                    start: t.start,
                    end: t.end,
                    source: None,
                }),
            },
            None => Err(self.eof_error(Expected::Number)),
        }
    }

    fn expect_othersymbol(&mut self) -> Result<&'a str, ParseError> {
        match self.next() {
            Some(t) => match &t.kind {
                Token::Macro(sym_str) => Ok(sym_str),
                other => Err(ParseError {
                    kind: ParseErrorKind::Expected {
                        expected: Expected::OtherSymbol,
                        found: Some(other.owned()),
                    },
                    start: t.start,
                    end: t.end,
                    source: None,
                }),
            },
            None => Err(self.eof_error(Expected::OtherSymbol)),
        }
    }

    fn parse_parenthesized<F, T>(&mut self, parse_inner: F) -> Result<T, ParseError>
    where
        F: FnOnce(&mut Self) -> Result<T, ParseError>,
    {
        self.expect_token(Token::LParen)?; // expect '('
        let result = parse_inner(self)?;
        self.expect_token(Token::RParen)?; // expect ')'
        Ok(result)
    }

    fn parse_bracketed<F, T>(&mut self, parse_inner: F) -> Result<T, ParseError>
    where
        F: FnOnce(&mut Self) -> Result<T, ParseError>,
    {
        self.expect_token(Token::LBracket)?;
        let result = parse_inner(self)?;
        self.expect_token(Token::RBracket)?;
        Ok(result)
    }

    fn parse_by<F, T>(&mut self, parse_inner: F) -> Result<T, ParseError>
    where
        F: FnOnce(&mut Self) -> Result<T, ParseError>,
    {
        self.expect_keyword("\\by")?;
        self.expect_token(Token::LBrace)?;
        let result = parse_inner(self)?;
        self.expect_token(Token::RBrace)?;
        Ok(result)
    }

    fn parse_named_by_term(&mut self, expected: &str) -> Result<SExp, ParseError> {
        let field = self.expect_ident()?;
        if field.as_str() != expected {
            return Err(self.error(ParseErrorKind::ExpectedProofField {
                name: expected.to_owned(),
            }));
        }
        self.expect_token(Token::Colon)?;
        self.parse_sexp()
    }

    fn parse_choice_proofs(&mut self) -> Result<(SExp, SExp), ParseError> {
        self.parse_by(|parser| {
            let existence = parser.parse_named_by_term("existence")?;
            parser.expect_token(Token::Comma)?;
            let uniqueness = parser.parse_named_by_term("uniqueness")?;
            Ok((existence, uniqueness))
        })
    }

    fn parse_recursion_types(&mut self) -> Result<(SExp, SExp), ParseError> {
        self.parse_bracketed(|parser| {
            let state_ty = parser.parse_sexp()?;
            parser.expect_token(Token::Comma)?;
            let result_ty = parser.parse_sexp()?;
            Ok((state_ty, result_ty))
        })
    }

    // Parse a parenthesized number (e.g., "(0)").
    fn parse_number_paren(&mut self) -> Result<usize, ParseError> {
        self.expect_token(Token::LParen)?;
        let number = self.expect_number()?;
        self.expect_token(Token::RParen)?;

        Ok(number)
    }

    // Parse a sort expression.
    // \Prop | \PropKind | \Set ( "(" <number> ")" )? | \SetKind ( "(" <number> ")" )?
    fn parse_sort(&mut self) -> Result<crate::sort::Sort, ParseError> {
        if self.bump_if_keyword("\\Prop") {
            return Ok(crate::sort::Sort::Prop);
        }
        if self.bump_if_keyword("\\PropKind") {
            return Ok(crate::sort::Sort::PropKind);
        }
        if self.bump_if_keyword("\\Set") {
            let number = if self.peek() == Some(&Token::LParen)
                && matches!(
                    self.tokens.get(self.pos + 1).map(|t| t.kind),
                    Some(Token::Number(_))
                ) {
                self.parse_number_paren()?
            } else {
                0
            };

            return Ok(crate::sort::Sort::Set(number));
        }
        if self.bump_if_keyword("\\SetKind") {
            let number = if self.peek() == Some(&Token::LParen)
                && matches!(
                    self.tokens.get(self.pos + 1).map(|t| t.kind),
                    Some(Token::Number(_))
                ) {
                self.parse_number_paren()?
            } else {
                0
            };
            return Ok(crate::sort::Sort::SetKind(number));
        }
        Err(ParseError {
            kind: ParseErrorKind::ExpectedSortKeyword,
            start: self.span_at(self.pos).start,
            end: self.span_at(self.pos).end,
            source: None,
        })
    }

    fn parse_keyword_head_atom(&mut self) -> Result<SExp, ParseError> {
        if self.bump_if_keyword(r"\tmatch") {
            if !self.allow_macro_parameters {
                return Err(
                    self.error(ParseErrorKind::TokenMatchingIsOnlyValidInNamedMacroTemplates)
                );
            }
            let target = self.expect_ident()?;
            let branches = self.parse_branches(|parser| {
                let pattern = parser.parse_token_match_pattern()?;
                parser.expect_token(Token::DoubleArrow)?;
                let body = parser.parse_sexp()?;
                Ok((pattern, body))
            })?;
            return Ok(SExp::TokenMatch { target, branches });
        }
        if self.bump_if_keyword("\\VType") {
            return Ok(SExp::ValueType);
        }
        if self.bump_if_keyword("\\U") {
            return Ok(SExp::ThunkType {
                computation_ty: Box::new(self.parse_postfix()?),
            });
        }
        if self.bump_if_keyword("\\F") {
            return Ok(SExp::ReturnType {
                value_ty: Box::new(self.parse_postfix()?),
            });
        }
        if self.bump_if_keyword(r"\match") {
            let scrutinee = self.parse_sexp()?;
            self.expect_keyword(r"\in")?;
            let path = self.parse_access_path()?;
            let return_type = if self.bump_if_keyword(r"\return") {
                let allow_empty_record_literal = self.allow_empty_record_literal;
                self.allow_empty_record_literal = false;
                let return_type = self.parse_sexp();
                self.allow_empty_record_literal = allow_empty_record_literal;
                Some(Box::new(return_type?))
            } else {
                None
            };
            self.expect_keyword(r"\with")?;
            let branches = self.parse_branches(|parser| {
                let constructor = parser.expect_ident()?;
                let mut binders = Vec::new();
                while matches!(parser.peek(), Some(Token::Ident(_))) {
                    binders.push(parser.expect_ident()?);
                }
                parser.expect_token(Token::Colon)?;
                let body = parser.parse_sexp()?;
                Ok((constructor, binders, body))
            })?;
            return Ok(match return_type {
                Some(return_type) => SExp::IndCase {
                    path,
                    scrutinee: Box::new(scrutinee),
                    return_type,
                    branches,
                },
                None => SExp::ProgramCase {
                    path,
                    scrutinee: Box::new(scrutinee),
                    branches,
                },
            });
        }
        if self.bump_if_keyword("\\Pow") {
            let set = self.parse_postfix()?;
            return Ok(SExp::PowerSet { set: Box::new(set) });
        }
        if self.bump_if_keyword("\\In") {
            let superset = self.parse_bracketed(Self::parse_sexp)?;
            let subset_name = Identifier("<membership-subset>".into());
            let element_name = Identifier("<membership-element>".into());
            let access = |name: &Identifier| SExp::AccessPath {
                access: LocalAccess::Current {
                    span: Default::default(),
                    access: name.clone(),
                },
                parameters: Vec::new(),
            };
            return Ok(SExp::Lam {
                bind: Bind::Named(RightBind {
                    vars: vec![subset_name.clone()],
                    ty: Box::new(SExp::PowerSet {
                        set: Box::new(superset.clone()),
                    }),
                }),
                body: Box::new(SExp::Lam {
                    bind: Bind::Named(RightBind {
                        vars: vec![element_name.clone()],
                        ty: Box::new(superset.clone()),
                    }),
                    body: Box::new(SExp::Pred {
                        superset: Box::new(superset),
                        subset: Box::new(access(&subset_name)),
                        element: Box::new(access(&element_name)),
                    }),
                }),
            });
        }
        if self.bump_if_keyword("\\Cast") {
            let superset = self.parse_bracketed(Self::parse_sexp)?;
            let subset_name = Identifier("<cast-subset>".into());
            return Ok(SExp::Lam {
                bind: Bind::Named(RightBind {
                    vars: vec![subset_name.clone()],
                    ty: Box::new(SExp::PowerSet {
                        set: Box::new(superset.clone()),
                    }),
                }),
                body: Box::new(SExp::TypeLift {
                    superset: Box::new(superset),
                    subset: Box::new(SExp::AccessPath {
                        access: LocalAccess::Current {
                            span: Default::default(),
                            access: subset_name,
                        },
                        parameters: Vec::new(),
                    }),
                }),
            });
        }
        if self.bump_if_keyword("\\into") {
            let superset = self.parse_bracketed(Self::parse_sexp)?;
            let (element, subset) = self.parse_parenthesized(|parser| {
                let element = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let subset = parser.parse_sexp()?;
                Ok((element, subset))
            })?;
            let proof = self.parse_by(Self::parse_sexp)?;
            return Ok(SExp::SubsetIntro {
                superset: Box::new(superset),
                subset: Box::new(subset),
                element: Box::new(element),
                proof: Box::new(proof),
            });
        }
        if self.bump_if_keyword("\\RunStep") {
            let (state_ty, result_ty) = self.parse_recursion_types()?;
            return Ok(SExp::RunStep {
                state_ty: Box::new(state_ty),
                result_ty: Box::new(result_ty),
            });
        }
        if self.bump_if_keyword("\\continue") {
            let (state_ty, result_ty) = self.parse_recursion_types()?;
            return self.parse_parenthesized(|parser| {
                let next = parser.parse_sexp()?;
                Ok(SExp::Continue {
                    state_ty: Box::new(state_ty),
                    result_ty: Box::new(result_ty),
                    next: Box::new(next),
                })
            });
        }
        if self.bump_if_keyword("\\finish") {
            let (state_ty, result_ty) = self.parse_recursion_types()?;
            return self.parse_parenthesized(|parser| {
                let output = parser.parse_sexp()?;
                Ok(SExp::Finish {
                    state_ty: Box::new(state_ty),
                    result_ty: Box::new(result_ty),
                    output: Box::new(output),
                })
            });
        }
        if self.bump_if_keyword("\\run") {
            let (state_ty, result_ty) = self.parse_recursion_types()?;
            let (step, initial) = self.parse_parenthesized(|parser| {
                let step = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let initial = parser.parse_sexp()?;
                Ok((step, initial))
            })?;
            let accessibility = Box::new(self.parse_by(Self::parse_sexp)?);
            return Ok(SExp::Run {
                state_ty: Box::new(state_ty),
                result_ty: Box::new(result_ty),
                step: Box::new(step),
                initial: Box::new(initial),
                accessibility,
            });
        }
        if self.bump_if_keyword("\\runCase") {
            let (state_ty, result_ty) = self.parse_recursion_types()?;
            let (step, initial, transition) = self.parse_parenthesized(|parser| {
                let step = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let initial = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let transition = parser.parse_sexp()?;
                Ok((step, initial, transition))
            })?;
            let (accessibility, transition_equality) = self.parse_by(|parser| {
                let accessibility = parser.parse_named_by_term("accessibility")?;
                parser.expect_token(Token::Comma)?;
                let transition_equality = parser.parse_named_by_term("equality")?;
                Ok((Box::new(accessibility), Box::new(transition_equality)))
            })?;
            return Ok(SExp::RunCase {
                state_ty: Box::new(state_ty),
                result_ty: Box::new(result_ty),
                step: Box::new(step),
                initial: Box::new(initial),
                transition: Box::new(transition),
                accessibility,
                transition_equality,
            });
        }
        if self.bump_if_keyword("\\step-match") {
            let binder = if matches!(self.peek(), Some(Token::Ident(_)))
                && self.tokens.get(self.pos + 1).map(|token| token.kind) == Some(Token::Colon)
            {
                let name = self.expect_ident()?;
                self.expect_token(Token::Colon)?;
                Some(name)
            } else {
                None
            };
            let step_ty = self.parse_postfix()?;
            let SExp::RunStep {
                state_ty,
                result_ty,
            } = step_ty.clone()
            else {
                return Err(self.error(ParseErrorKind::StepMatchExpectsARunstepType));
            };
            self.expect_keyword("\\return")?;
            let return_type = self.parse_sexp()?;
            self.expect_keyword("\\with")?;
            let branches = self.parse_branches(|parser| {
                let constructor = if parser.bump_if_keyword("\\continue") {
                    "continue"
                } else if parser.bump_if_keyword("\\finish") {
                    "finish"
                } else {
                    return Err(parser.error(ParseErrorKind::ExpectedContinueOrFinishBranch));
                };
                let argument = parser.expect_binder_ident()?;
                parser.expect_token(Token::Colon)?;
                Ok((constructor, argument, parser.parse_sexp()?))
            })?;
            let mut on_continue = None;
            let mut on_finish = None;
            for (constructor, argument, body) in branches {
                let slot = if constructor == "continue" {
                    &mut on_continue
                } else {
                    &mut on_finish
                };
                if slot.replace((argument, body)).is_some() {
                    return Err(self.error(ParseErrorKind::DuplicateStepMatchBranch));
                }
            }
            let (continue_var, continue_body) =
                on_continue.ok_or_else(|| self.error(ParseErrorKind::MissingContinueBranch))?;
            let (finish_var, finish_body) =
                on_finish.ok_or_else(|| self.error(ParseErrorKind::MissingFinishBranch))?;
            let branch = |var, ty: Box<SExp>, body, program| {
                if program {
                    SExp::ComputationLam {
                        var,
                        value_ty: ty,
                        body: Box::new(body),
                    }
                } else {
                    SExp::Lam {
                        bind: Bind::Named(RightBind {
                            vars: vec![var],
                            ty,
                        }),
                        body: Box::new(body),
                    }
                }
            };
            if let Some(var) = binder {
                let motive = SExp::Lam {
                    bind: Bind::Named(RightBind {
                        vars: vec![var],
                        ty: Box::new(step_ty),
                    }),
                    body: Box::new(return_type),
                };
                return Ok(SExp::SetStepMatch {
                    state_ty: state_ty.clone(),
                    result_ty: result_ty.clone(),
                    motive: Box::new(motive),
                    on_continue: Box::new(branch(continue_var, state_ty, continue_body, false)),
                    on_finish: Box::new(branch(finish_var, result_ty, finish_body, false)),
                });
            }
            let var = Identifier("<step-match>".into());
            return Ok(SExp::Thunk {
                computation: Box::new(SExp::ComputationLam {
                    var: var.clone(),
                    value_ty: Box::new(step_ty),
                    body: Box::new(SExp::ProgramStepMatch {
                        state_ty: state_ty.clone(),
                        result_ty: result_ty.clone(),
                        computation_ty: Box::new(return_type),
                        on_continue: Box::new(branch(continue_var, state_ty, continue_body, true)),
                        on_finish: Box::new(branch(finish_var, result_ty, finish_body, true)),
                        scrutinee: Box::new(SExp::AccessPath {
                            access: LocalAccess::Current {
                                span: Default::default(),
                                access: var,
                            },
                            parameters: Vec::new(),
                        }),
                    }),
                }),
            });
        }
        if self.bump_if_keyword("\\Box") {
            let program_ty = self.parse_bracketed(Self::parse_sexp)?;
            return Ok(SExp::BoxType {
                program_ty: Box::new(program_ty),
            });
        }
        if self.bump_if_keyword("\\box") {
            let program_ty = self.parse_bracketed(Self::parse_sexp)?;
            return self.parse_parenthesized(|parser| {
                let program = parser.parse_sexp()?;
                Ok(SExp::BoxProgram {
                    program_ty: Box::new(program_ty),
                    program: Box::new(program),
                })
            });
        }
        if self.bump_if_keyword("\\squash") {
            let program_ty = self.parse_bracketed(Self::parse_sexp)?;
            let boxed = self.parse_parenthesized(Self::parse_sexp)?;
            return Ok(SExp::ForceBox {
                program_ty: Box::new(program_ty),
                boxed: Box::new(boxed),
            });
        }
        if self.bump_if_keyword("\\boxapp") {
            return self.parse_parenthesized(|parser| {
                let function = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let argument = parser.parse_sexp()?;
                Ok(SExp::BoxApp {
                    function: Box::new(function),
                    argument: Box::new(argument),
                })
            });
        }
        if self.bump_if_keyword("\\induction") {
            let mut binders = self.parse_simple_binds_paren()?;
            while self.peek() == Some(&Token::LParen) {
                binders.extend(self.parse_simple_binds_paren()?);
            }
            if binders.is_empty() || binders.iter().any(|binder| binder.vars.is_empty()) {
                return Err(self.error(ParseErrorKind::ExpectedInductionBinders));
            }
            self.expect_keyword("\\return")?;
            let return_type = self.parse_sexp()?;
            self.expect_keyword("\\with")?;
            let cases = self.parse_branches(|parser| {
                let case_name = if parser.peek() == Some(&Token::Macro("#")) {
                    parser.next();
                    Identifier("#".to_owned())
                } else {
                    parser.expect_ident()?
                };
                parser.expect_token(Token::Colon)?;
                let case = parser.parse_sexp()?;
                Ok((case_name, case))
            })?;
            return Ok(SExp::Induction {
                binders,
                return_type: Box::new(return_type),
                cases,
            });
        }
        // r"\exists" <binding>
        if self.bump_if_keyword("\\exists") {
            let bind = if self.peek() == Some(&Token::LBrace) {
                self.parse_binding(Token::LBrace, Token::RBrace)?
            } else if self.peek() == Some(&Token::LParen)
                && matches!(
                    self.tokens.get(self.pos + 2).map(|token| token.kind),
                    Some(Token::Colon | Token::Comma)
                )
            {
                self.parse_binding(Token::LParen, Token::RParen)?
            } else {
                Bind::Named(RightBind {
                    vars: Vec::new(),
                    ty: Box::new(self.parse_equality()?),
                })
            };
            return Ok(SExp::Exists { bind });
        }
        if self.bump_if_keyword("\\choice") {
            let set = self.parse_sexp()?;
            let (existence, uniqueness) = self.parse_choice_proofs()?;
            return Ok(SExp::Choice {
                set: Box::new(set),
                existence: Box::new(existence),
                uniqueness: Box::new(uniqueness),
            });
        }
        if self.bump_if_keyword("\\take") {
            let bind = self.parse_binding(Token::LParen, Token::RParen)?;
            self.expect_token(Token::DoubleArrow)?;
            let body = self.parse_sexp()?;
            let existence = self.parse_by(|parser| parser.parse_sexp())?;
            return Ok(SExp::TakeProp {
                bind,
                body: Box::new(body),
                existence: Box::new(existence),
            });
        }
        if self.bump_if_keyword("\\block") {
            self.expect_token(Token::LBrace)?; // expect '{'
            let block = self.parse_block()?;
            self.expect_token(Token::RBrace)?; // expect '}'
            return Ok(SExp::Block(block));
        }
        if self.bump_if_keyword("\\program") {
            self.expect_token(Token::LBrace)?;
            let block = self.parse_block()?;
            self.expect_token(Token::RBrace)?;
            return Ok(SExp::Program(block));
        }

        Err(ParseError {
            kind: ParseErrorKind::ExpectedExpressionStartingWithKeyword,
            start: self.span_at(self.pos).start,
            end: self.span_at(self.pos).end,
            source: None,
        })
    }

    fn parse_proof_term(&mut self) -> Result<SExp, ParseError> {
        if self.bump_if_keyword("\\axiom") {
            self.expect_token(Token::Colon)?;
            let name = self.expect_ident()?;
            self.expect_token(Token::LParen)?;
            return match name.as_str() {
                "setext" => {
                    let left = Box::new(self.parse_sexp()?);
                    self.expect_token(Token::Comma)?;
                    let right = Box::new(self.parse_sexp()?);
                    self.expect_token(Token::Comma)?;
                    let left_to_right = Box::new(self.parse_sexp()?);
                    self.expect_token(Token::Comma)?;
                    let right_to_left = Box::new(self.parse_sexp()?);
                    self.expect_token(Token::RParen)?;
                    Ok(SExp::AxiomSetExt {
                        left,
                        right,
                        left_to_right,
                        right_to_left,
                    })
                }
                "funext" => {
                    let left = Box::new(self.parse_sexp()?);
                    self.expect_token(Token::Comma)?;
                    let right = Box::new(self.parse_sexp()?);
                    self.expect_token(Token::Comma)?;
                    let pointwise = Box::new(self.parse_sexp()?);
                    self.expect_token(Token::RParen)?;
                    Ok(SExp::AxiomFunExt {
                        left,
                        right,
                        pointwise,
                    })
                }
                "classicalIndefiniteChoice" => {
                    let domain = Box::new(self.parse_sexp()?);
                    self.expect_token(Token::Comma)?;
                    let family = Box::new(self.parse_sexp()?);
                    self.expect_token(Token::Comma)?;
                    let inhabited = Box::new(self.parse_sexp()?);
                    self.expect_token(Token::RParen)?;
                    Ok(SExp::AxiomClassicalIndefiniteChoice {
                        domain,
                        family,
                        inhabited,
                    })
                }
                _ => Err(ParseError {
                    kind: ParseErrorKind::UnknownAxiom {
                        name: name.as_str().to_owned(),
                    },
                    start: self.span_at(self.pos).start,
                    end: self.span_at(self.pos).end,
                    source: None,
                }),
            };
        }

        if self.bump_if_keyword("\\exact") {
            self.expect_token(Token::LParen)?; // expect '('
            let term = self.parse_sexp()?;
            self.expect_token(Token::Comma)?; // expect ','
            let set = self.parse_sexp()?;
            self.expect_token(Token::RParen)?; // expect ')'
            return Ok(SExp::ExistsIntro {
                element: Box::new(term),
                set: Box::new(set),
            });
        }

        if self.bump_if_keyword("\\bysub") {
            self.expect_token(Token::LParen)?;
            let superset = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let subset = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let element = self.parse_sexp()?;
            self.expect_token(Token::RParen)?;
            return Ok(SExp::SubsetElim {
                element: Box::new(element),
                subset: Box::new(subset),
                superset: Box::new(superset),
            });
        }

        if self.bump_if_keyword("\\refl") {
            return Ok(SExp::IdRefl {
                element: Box::new(self.parse_postfix()?),
            });
        }

        // \\idelim <left: SExp> "=" <right: SExp> r"\with" <var: Ident> ":" <ty: SExp> "=>" <predicate: SExp>
        if self.bump_if_keyword("\\idelim") {
            let left = self.parse_application()?;
            self.expect_token(Token::Equal)?; // expect '='
            let right = self.parse_sexp()?;
            self.expect_keyword("\\with")?; // expect '\with'
            let var = self.expect_ident()?;
            self.expect_token(Token::Colon)?; // expect ':'
            let ty = self.parse_equality()?;
            self.expect_token(Token::DoubleArrow)?; // expect '=>'
            let predicate = self.parse_sexp()?;
            let (base, equality) = self.parse_by(|parser| {
                let base = parser.parse_named_by_term("base")?;
                parser.expect_token(Token::Comma)?;
                let equality = parser.parse_named_by_term("equality")?;
                Ok((base, equality))
            })?;
            return Ok(SExp::IdElim {
                left: Box::new(left),
                right: Box::new(right),
                var,
                ty: Box::new(ty),
                predicate: Box::new(predicate),
                base: Box::new(base),
                equality: Box::new(equality),
            });
        }

        if self.bump_if_keyword("\\choiceeq") {
            let element = self.parse_arrow()?;
            self.expect_keyword("\\of")?;
            let set = self.parse_sexp()?;
            let (existence, uniqueness) = self.parse_choice_proofs()?;
            return Ok(SExp::ChoiceEq {
                set: Box::new(set),
                element: Box::new(element),
                existence: Box::new(existence),
                uniqueness: Box::new(uniqueness),
            });
        }

        Err(ParseError {
            kind: ParseErrorKind::ExpectedExpressionStartingWithKeyword,
            start: self.span_at(self.pos).start,
            end: self.span_at(self.pos).end,
            source: None,
        })
    }

    fn parse_token_match_pattern(&mut self) -> Result<TokenMatchPattern, ParseError> {
        if self.bump_if_token(Token::Hole) {
            return Ok(TokenMatchPattern::Default);
        }
        let mut parser = Parser::new(&self.tokens[self.pos..]);
        let atom = parser.parse_macro_pattern_atom()?;
        self.set_position(self.pos + parser.pos);
        match atom {
            MacroSeqAtom::Seq(items) => Ok(TokenMatchPattern::Sequence(items)),
            atom @ (MacroSeqAtom::Tok(_) | MacroSeqAtom::Quoted(_)) => {
                Ok(TokenMatchPattern::Token(atom))
            }
            _ => Err(self.error(ParseErrorKind::ExpectedFixedTokenSequencePatternOr)),
        }
    }

    // { (| <branch>)* }: the next pipe or closing brace ends each branch body.
    // Branch delimiters are shared by \match, \tmatch, and \induction.
    // Each caller parses its own branch head and body, committing on errors.
    fn parse_branches<T>(
        &mut self,
        mut parse_branch: impl FnMut(&mut Self) -> Result<T, ParseError>,
    ) -> Result<Vec<T>, ParseError> {
        self.expect_token(Token::LBrace)?;
        let mut branches = Vec::new();
        while !self.bump_if_token(Token::RBrace) {
            self.expect_token(Token::Pipe)?;
            let branch = parse_branch(self)?;
            branches.push(branch);
        }
        Ok(branches)
    }

    fn parse_block(&mut self) -> Result<Block, ParseError> {
        let mut statements = Vec::new();

        loop {
            if self.bump_if_keyword("\\fun") {
                // r"\fun" ("(" RightBind ")")* "\then"
                let mut binds: Vec<RightBind> = Vec::new();
                while self.peek() == Some(&Token::LParen) {
                    let bind = self.parse_simple_binds_paren()?;
                    binds.extend(bind);
                }
                self.expect_keyword("\\then")?;
                statements.push(Statement::Fun(binds));
                continue;
            }

            if self.bump_if_keyword("\\let") {
                let start = self.span_at(self.pos - 1).start;
                // r"\let" <var: Ident> ":" <ty: SExp> ":=" <body: SExp> "\then"
                let var = self.expect_ident()?;
                self.expect_token(Token::Colon)?; // expect ':'
                let ty = self.parse_sexp()?;
                self.expect_token(Token::Assign)?; // expect ':='
                let body = self.parse_sexp()?;
                self.expect_keyword("\\then")?;
                let span = SourceSpan {
                    start,
                    end: self.span_at(self.pos - 1).end,
                };
                statements.push(Statement::Let {
                    span,
                    var,
                    ty,
                    body,
                });
                continue;
            }

            if self.bump_if_keyword("\\bind") {
                // r"\bind" <var: Ident> ":" <ty: SExp> "<-" <computation: SExp> "\then"
                let var = self.expect_binder_ident()?;
                self.expect_token(Token::Colon)?;
                let ty = self.parse_sexp()?;
                self.expect_token(Token::BindArrow)?;
                let computation = self.parse_sexp()?;
                self.expect_keyword("\\then")?;
                statements.push(Statement::Bind {
                    var,
                    ty,
                    computation,
                });
                continue;
            }

            if self.bump_if_keyword("\\enough") {
                let map_ty = self.parse_sexp()?;
                let map = self.parse_by(Self::parse_sexp)?;
                self.expect_keyword("\\then")?;
                statements.push(Statement::Sufficient { map, map_ty });
                continue;
            }

            if self.bump_if_keyword("\\takefrom") {
                let var = self.expect_binder_ident()?;
                self.expect_token(Token::Colon)?;
                let ty = self.parse_sexp()?;
                self.expect_keyword("\\by")?;
                let existence = self.parse_sexp()?;
                self.expect_keyword("\\then")?;
                statements.push(Statement::TakeFrom { var, ty, existence });
                continue;
            }

            if self.bump_if_keyword("\\return") {
                // r"\return" <exp: SExp>
                let result = self.parse_sexp()?;
                return Ok(Block {
                    statements,
                    result: Box::new(result),
                });
            }

            break; // No more block statements.
        }

        Err(ParseError {
            kind: ParseErrorKind::ExpectedBlockStatementOrReturn,
            start: self.span_at(self.pos).start,
            end: self.span_at(self.pos).end,
            source: None,
        })
    }

    // general parameter passing expression is here
    // "[" (SExp ("," SExp)*)? "]"
    fn parse_parameter(&mut self) -> Result<Vec<SExp>, ParseError> {
        self.expect_token(Token::LBracket)?; // expect '['
        let mut params = Vec::new();
        while self.peek() != Some(&Token::RBracket) {
            params.push(self.parse_sexp()?);
            if !self.bump_if_token(Token::Comma) {
                break;
            }
        }
        self.expect_token(Token::RBracket)?; // expect ']'
        Ok(params)
    }

    fn starts_module_call_at(&self, position: usize) -> bool {
        let token = |offset: usize| self.tokens.get(position + offset).map(|token| token.kind);
        matches!(token(0), Some(Token::Ident(_)))
            && token(1) == Some(Token::LBracket)
            && (matches!(
                (token(2), token(3)),
                (Some(Token::Ident(_)), Some(Token::Assign))
            ) || (token(2) == Some(Token::RBracket) && token(3) == Some(Token::Period)))
    }

    fn starts_module_expression(&self) -> bool {
        matches!(
            self.peek(),
            Some(Token::Period | Token::KeyWord("\\root" | "\\parent"))
        ) || self.starts_module_call_at(self.pos)
            || (matches!(self.peek(), Some(Token::Ident(_)))
                && self
                    .tokens
                    .get(self.pos + 1)
                    .is_some_and(|t| t.kind == Token::Period)
                && self.starts_module_call_at(self.pos + 2))
    }

    fn parse_module_expression_access(&mut self) -> Result<LocalAccess, ParseError> {
        let start = self.span_at(self.pos).start;
        let mut path = if self.bump_if_keyword("\\root") {
            self.expect_token(Token::Period)?;
            ModuleInstantiatePath::FromRoot { calls: Vec::new() }
        } else if self.bump_if_token(Token::Period) {
            ModuleInstantiatePath::FromCurrent {
                back_parent: 0,
                calls: Vec::new(),
            }
        } else if self.peek() == Some(&Token::KeyWord("\\parent")) {
            let mut back_parent = 0;
            while self.bump_if_keyword("\\parent") {
                self.expect_token(Token::Period)?;
                back_parent += 1;
            }
            ModuleInstantiatePath::FromCurrent {
                back_parent,
                calls: Vec::new(),
            }
        } else if self
            .tokens
            .get(self.pos + 1)
            .is_some_and(|t| t.kind == Token::Period)
        {
            let import_name = self.expect_ident()?;
            self.expect_token(Token::Period)?;
            ModuleInstantiatePath::FromImport {
                import_name,
                calls: Vec::new(),
            }
        } else {
            ModuleInstantiatePath::FromCurrent {
                back_parent: 0,
                calls: Vec::new(),
            }
        };
        let calls = match &mut path {
            ModuleInstantiatePath::FromRoot { calls }
            | ModuleInstantiatePath::FromCurrent { calls, .. }
            | ModuleInstantiatePath::FromImport { calls, .. } => calls,
        };
        while self.starts_module_call_at(self.pos) {
            let name = self.expect_ident()?;
            self.expect_token(Token::LBracket)?;
            let mut arguments = Vec::new();
            if !self.bump_if_token(Token::RBracket) {
                loop {
                    let parameter = self.expect_ident()?;
                    self.expect_token(Token::Assign)?;
                    arguments.push((parameter, self.parse_sexp()?));
                    if self.bump_if_token(Token::RBracket) {
                        break;
                    }
                    self.expect_token(Token::Comma)?;
                }
            }
            calls.push((name, arguments));
            self.expect_token(Token::Period)?;
        }
        let mut child = self.expect_ident()?;
        if self.bump_if_token(Token::Caret) {
            child.0.push('^');
        }
        Ok(LocalAccess::Instantiated {
            span: SourceSpan {
                start,
                end: self.span_at(self.pos - 1).end,
            },
            path: Box::new(path),
            child,
        })
    }

    // A local or imported name, optionally followed by explicit Set reflection.
    fn parse_access_path(&mut self) -> Result<LocalAccess, ParseError> {
        if self.starts_module_expression() {
            return self.parse_module_expression_access();
        }
        let start = self.span_at(self.position()).start;
        let first = self.expect_ident()?;
        let (namespace, mut name) = if self.bump_if_token(Token::Period) {
            (Some(first), self.expect_ident()?)
        } else {
            (None, first)
        };
        if self.bump_if_token(Token::Caret) {
            name.0.push('^');
        }
        let span = SourceSpan {
            start,
            end: self.span_at(self.position() - 1).end,
        };
        Ok(match namespace {
            Some(access) => LocalAccess::Named {
                span,
                access,
                child: name,
            },
            None => LocalAccess::Current { access: name, span },
        })
    }

    fn parse_record_body(&mut self) -> Result<Vec<(Identifier, SExp)>, ParseError> {
        let mut fields = Vec::new();

        self.expect_token(Token::LBrace)?; // expect '{'
        while !self.bump_if_token(Token::RBrace) {
            let field_name = self.expect_ident()?;
            self.expect_token(Token::Assign)?;
            let field_exp = self.parse_sexp()?;
            fields.push((field_name, field_exp));

            if !self.bump_if_token(Token::Comma) {
                self.expect_token(Token::RBrace)?; // expect '}'
                break;
            }
        }

        Ok(fields)
    }

    // parse a single atom
    // 1-A. `x`, `x.y`, `x [e1, ..., en]`, `x.ctor [e1, ..., en]`
    // 1-B. `x::ctor`, `x.y::ctor`, `x.y[params]::ctor`
    // 1-C. `x <field_body>`, `x.y <field_body>`, `x.y[params] <field_body>`
    // 2. `(<expr>)`, `\( ... \)`, `name!{ ... }`
    // 3. something start with keyword (sort, etc.)
    fn parse_atom(&mut self) -> Result<SExp, ParseError> {
        match self.peek() {
            Some(Token::MacroVar(_)) => {
                if !self.allow_macro_parameters {
                    return Err(ParseError {
                        kind: ParseErrorKind::MacroCapturesAreOnlyValidInMacroTemplates,
                        start: self.tokens[self.pos].start,
                        end: self.tokens[self.pos].end,
                        source: None,
                    });
                }
                let token = self.next().expect("peeked token exists");
                let Token::MacroVar(name) = token.kind else {
                    unreachable!()
                };
                Ok(SExp::MacroParameter(Identifier(name[1..].to_string())))
            }
            Some(Token::Hole) => {
                let token = self.next().expect("peeked token exists");
                Ok(SExp::Meta {
                    kind: SurfaceMeta::Implicit,
                    span: SourceSpan {
                        start: token.start,
                        end: token.end,
                    },
                })
            }
            Some(Token::Metavariable(_)) => {
                let token = self.next().expect("peeked token exists");
                let Token::Metavariable(spelling) = token.kind else {
                    unreachable!()
                };
                let suffix = &spelling[1..];
                let kind = if spelling == "?" {
                    SurfaceMeta::Goal
                } else if suffix.bytes().all(|byte| byte.is_ascii_digit()) {
                    let number = suffix.parse::<u32>().map_err(|_| ParseError {
                        kind: ParseErrorKind::MetavariableNumberOverflow {
                            text: spelling.to_owned(),
                        },
                        start: token.start,
                        end: token.end,
                        source: None,
                    })?;
                    SurfaceMeta::Named(number)
                } else {
                    return Err(ParseError {
                        kind: ParseErrorKind::ExpectedOrFollowedByDigits,
                        start: token.start,
                        end: token.end,
                        source: None,
                    });
                };
                Ok(SExp::Meta {
                    kind,
                    span: SourceSpan {
                        start: token.start,
                        end: token.end,
                    },
                })
            }
            Some(Token::Ident(_) | Token::Period | Token::KeyWord("\\root" | "\\parent")) => {
                if let (Some(name), Some(bang)) =
                    (self.tokens.get(self.pos), self.tokens.get(self.pos + 1))
                    && matches!(bang.kind, Token::Exclamation)
                    && name.end == bang.start
                {
                    let name = self.expect_ident()?;
                    self.expect_token(Token::Exclamation)?;
                    self.expect_token(Token::LBrace)?;
                    let tokens = self.parse_macro_sequence_until(&Token::RBrace)?;
                    self.expect_token(Token::RBrace)?;
                    return Ok(SExp::NamedMacro { name, tokens });
                }
                // `x`, `x.y`, `x [e1, ..., en]`, `x.ctor [e1, ..., en]`
                let access = self.parse_access_path()?;
                let parameters = self.parse_optional_parameters()?;

                let starts_record_body = match (
                    self.tokens.get(self.pos).map(|token| token.kind),
                    self.tokens.get(self.pos + 1).map(|token| token.kind),
                    self.tokens.get(self.pos + 2).map(|token| token.kind),
                ) {
                    (Some(Token::LBrace), Some(Token::RBrace), _) => {
                        self.allow_empty_record_literal
                    }
                    (Some(Token::LBrace), Some(Token::Ident(_)), Some(Token::Assign)) => true,
                    _ => false,
                };
                if starts_record_body {
                    let fields = self.parse_record_body()?;
                    return Ok(SExp::RecordTypeCtor {
                        access,
                        parameters,
                        fields,
                    });
                }

                // field access case or record construction case
                if self.bump_if_token(Token::RecordConstructor) {
                    let start = self.span_at(self.position() - 1).start;
                    let field = if self.bump_if_token(Token::Caret) {
                        Identifier("#^".into())
                    } else {
                        Identifier("#".into())
                    };
                    return Ok(SExp::AssociatedAccess {
                        span: SourceSpan {
                            start,
                            end: self.span_at(self.position() - 1).end,
                        },
                        base: Box::new(SExp::AccessPath { access, parameters }),
                        field,
                    });
                }
                if self.bump_if_token(Token::DoubleColon) {
                    let start = self.span_at(self.position()).start;
                    // field access case
                    let mut field_name = self.expect_associated_name()?;
                    if self.bump_if_token(Token::Caret) {
                        field_name.0.push('^');
                    }
                    return Ok(SExp::AssociatedAccess {
                        span: SourceSpan {
                            start,
                            end: self.span_at(self.position() - 1).end,
                        },
                        base: Box::new(SExp::AccessPath { access, parameters }),
                        field: field_name,
                    });
                }

                Ok(SExp::AccessPath { access, parameters })
            }
            Some(Token::Macro("#")) => {
                self.next();
                let field = self.expect_ident()?;
                let span = self.span_at(self.position() - 1);
                self.expect_token(Token::LBrace)?;
                let value = self.parse_sexp()?;
                self.expect_token(Token::RBrace)?;
                Ok(SExp::InferredProjection {
                    value: Box::new(value),
                    field,
                    span,
                })
            }
            Some(Token::LBrace) => {
                let bind = self.parse_binding(Token::LBrace, Token::RBrace)?;
                let Bind::Subset { var, ty, predicate } = bind else {
                    return Err(self.error(ParseErrorKind::ExpectedSubsetTypeXAWhereP));
                };
                Ok(SExp::SubSet {
                    var,
                    set: ty,
                    predicate,
                })
            }
            Some(Token::LParen) => {
                self.next(); // consume '('
                let expr = self.parse_sexp()?;
                self.expect_token(Token::RParen)?; // expect ')'
                Ok(expr)
            }
            Some(Token::MathLParen) => {
                self.next(); // consume '\('
                let tokens = self.parse_macro_sequence_until(&Token::MathRParen)?;
                self.expect_token(Token::MathRParen)?; // expect '\)'
                Ok(SExp::MathMacro { tokens })
            }
            Some(Token::KeyWord("\\return" | "\\thunk" | "\\force")) => self.parse_unary(),
            Some(Token::KeyWord("\\fun" | "\\forall" | "\\cfun")) => self.parse_lambda(),
            Some(Token::KeyWord(keyword)) if SORT_KEYWORDS.contains(keyword) => {
                // check if it's a reserved sort keyword
                self.parse_sort().map(SExp::Sort)
            }
            Some(Token::KeyWord(keyword)) if EXPRESSION_ATOM_KEYWORDS.contains(keyword) => {
                self.parse_keyword_head_atom()
            }
            Some(Token::KeyWord(keyword)) if PROOF_TERM_KEYWORDS.contains(keyword) => {
                self.parse_proof_term()
            }
            Some(Token::KeyWord(keyword)) => Err(ParseError {
                kind: ParseErrorKind::UnexpectedKeyword {
                    keyword: (*keyword).to_owned(),
                },
                start: self.span_at(self.pos).start,
                end: self.span_at(self.pos).end,
                source: None,
            }),
            _ => Err(ParseError {
                kind: ParseErrorKind::ExpectedAtom,
                start: self.span_at(self.pos).start,
                end: self.span_at(self.pos).end,
                source: None,
            }),
        }
    }

    // <atom> (("::" Ident) | "::#" | "#" Ident)*
    fn parse_postfix(&mut self) -> Result<SExp, ParseError> {
        let mut expr = self.parse_atom()?;
        loop {
            if self.bump_if_token(Token::Period) {
                let mut field = self.expect_ident()?;
                let span = self.span_at(self.position() - 1);
                if self.bump_if_token(Token::Caret) {
                    field.0.push('^');
                }
                let parameters = self.parse_optional_parameters()?;
                expr = SExp::MemberAccess {
                    base: Box::new(expr),
                    field,
                    parameters,
                    span,
                };
                continue;
            }
            if self.peek() == Some(&Token::Macro("#")) {
                // #field{value} starts a separate atom and is applied to expr.
                if matches!(
                    self.tokens.get(self.pos + 2).map(|token| token.kind),
                    Some(Token::LBrace)
                ) {
                    break;
                }
                self.next();
                let field = self.expect_ident()?;
                let span = self.span_at(self.position() - 1);
                expr = SExp::InferredProjection {
                    value: Box::new(expr),
                    field,
                    span,
                };
                continue;
            }
            if self.peek() == Some(&Token::LBrace)
                && matches!(
                    self.tokens.get(self.pos + 1).map(|t| &t.kind),
                    Some(Token::Ident(_))
                )
                && matches!(
                    self.tokens.get(self.pos + 2).map(|t| &t.kind),
                    Some(Token::Assign)
                )
            {
                let fields = self.parse_record_body()?;
                expr = SExp::MemberLiteral {
                    ty: Box::new(expr),
                    fields,
                };
                continue;
            }
            let mut field_name = if self.bump_if_token(Token::RecordConstructor) {
                Identifier("#".into())
            } else if self.bump_if_token(Token::DoubleColon) {
                self.expect_associated_name()?
            } else {
                break;
            };
            let start = self.span_at(self.position() - 1).start;
            if self.bump_if_token(Token::Caret) {
                field_name.0.push('^');
            }
            expr = SExp::AssociatedAccess {
                span: SourceSpan {
                    start,
                    end: self.span_at(self.position() - 1).end,
                },
                base: Box::new(expr),
                field: field_name,
            };
        }
        Ok(expr)
    }

    // <postfix> <postfix>*; application associates to the left.
    fn parse_application(&mut self) -> Result<SExp, ParseError> {
        let mut expr = self.parse_postfix()?;

        while self.starts_atom() {
            let arg = self.parse_postfix()?;
            expr = SExp::App {
                func: Box::new(expr),
                arg: Box::new(arg),
            };
        }

        Ok(expr)
    }

    // <application> ("=" <application>)?; equality does not chain.
    fn parse_equality(&mut self) -> Result<SExp, ParseError> {
        let left = self.parse_application()?;
        if self.bump_if_token(Token::Equal) {
            let right = self.parse_application()?;
            Ok(SExp::Equal {
                left: Box::new(left),
                right: Box::new(right),
            })
        } else {
            Ok(left)
        }
    }

    // Parse an annotation
    // Ident ("," Ident)* ":" SExp
    fn parse_annotate(&mut self) -> Result<(Vec<Identifier>, SExp), ParseError> {
        // 1. parse identifiers separated by commas
        let mut vars = vec![];
        vars.push(self.expect_binder_ident()?);

        while self.bump_if_token(Token::Comma) {
            vars.push(self.expect_binder_ident()?);
        }

        self.expect_token(Token::Colon)?; // expect ":"

        // 3. parse the type
        let ty = self.parse_sexp()?;

        Ok((vars, ty))
    }

    // parse multiple annotations separated by commas
    // trailing comma is allowed (it consumes trailing comma)
    fn parse_annotate_comma_separated_until(
        &mut self,
        end: Token<'a>,
    ) -> Result<Vec<RightBind>, ParseError> {
        let mut annotations = Vec::new();
        while self.peek().is_some() && self.peek() != Some(&end) {
            let (vars, ty) = self.parse_annotate()?;
            annotations.push(RightBind {
                vars,
                ty: Box::new(ty),
            });
            if !self.bump_if_token(Token::Comma) {
                break;
            }
        }
        Ok(annotations)
    }

    fn parse_annotate_comma_separated(&mut self) -> Result<Vec<RightBind>, ParseError> {
        self.parse_annotate_comma_separated_until(Token::RParen)
    }

    // "(" <multiple annotations comma separated> ")"
    fn parse_simple_binds_paren(&mut self) -> Result<Vec<RightBind>, ParseError> {
        self.parse_parenthesized(|parser| parser.parse_annotate_comma_separated())
    }

    pub(super) fn parse_simple_binds_advanced(
        &mut self,
    ) -> Result<(Vec<RightBind>, usize), ParseError> {
        let binds = self.parse_simple_binds_paren()?;
        let advanced_pos = self.pos;
        Ok((binds, advanced_pos))
    }

    pub(super) fn parse_simple_binds_bracketed_advanced(
        &mut self,
    ) -> Result<(Vec<RightBind>, usize), ParseError> {
        let binds = self.parse_bracketed(|parser| {
            parser.parse_annotate_comma_separated_until(Token::RBracket)
        })?;
        let advanced_pos = self.pos;
        Ok((binds, advanced_pos))
    }

    fn error(&self, kind: ParseErrorKind) -> ParseError {
        let span = self.span_at(self.pos);
        ParseError {
            kind,
            start: span.start,
            end: span.end,
            source: None,
        }
    }

    fn parse_optional_parameters(&mut self) -> Result<Vec<SExp>, ParseError> {
        if self.peek() == Some(&Token::LBracket) {
            self.parse_parameter()
        } else {
            Ok(Vec::new())
        }
    }

    fn starts_atom(&self) -> bool {
        match self.peek() {
            Some(
                Token::Ident(_)
                | Token::Period
                | Token::KeyWord("\\root" | "\\parent")
                | Token::Hole
                | Token::Metavariable(_)
                | Token::MacroVar(_)
                | Token::LParen
                | Token::MathLParen,
            ) => true,
            Some(Token::Macro("#")) => true,
            Some(Token::KeyWord(k)) => {
                SORT_KEYWORDS.contains(k)
                    || EXPRESSION_ATOM_KEYWORDS.contains(k)
                    || PROOF_TERM_KEYWORDS.contains(k)
            }
            _ => false,
        }
    }

    fn expect_associated_name(&mut self) -> Result<Identifier, ParseError> {
        if self.bump_if_token(Token::Macro("#")) {
            Ok(Identifier("#".into()))
        } else {
            self.expect_ident()
        }
    }

    fn parse_binding(&mut self, open: Token<'a>, close: Token<'a>) -> Result<Bind, ParseError> {
        self.expect_token(open)?;
        let (vars, ty) = self.parse_annotate()?;
        let bind = if self.bump_if_keyword(r"\where") {
            let [var] = vars.as_slice() else {
                return Err(self.error(ParseErrorKind::ExpectedSingleIdentifierInRefinementBinder));
            };
            let predicate = Box::new(self.parse_sexp()?);
            if self.bump_if_keyword(r"\as") {
                Bind::SubsetWithProof {
                    var: var.clone(),
                    ty: Box::new(ty),
                    predicate,
                    proof_var: self.expect_binder_ident()?,
                }
            } else {
                Bind::Subset {
                    var: var.clone(),
                    ty: Box::new(ty),
                    predicate,
                }
            }
        } else {
            Bind::Named(RightBind {
                vars,
                ty: Box::new(ty),
            })
        };
        self.expect_token(close)?;
        Ok(bind)
    }

    fn parse_unary(&mut self) -> Result<SExp, ParseError> {
        match self.next().unwrap().kind {
            Token::KeyWord("\\return") => Ok(SExp::Return {
                value: Box::new(self.parse_sexp()?),
            }),
            Token::KeyWord("\\thunk") => Ok(SExp::Thunk {
                computation: Box::new(self.parse_postfix()?),
            }),
            Token::KeyWord("\\force") => Ok(SExp::Force {
                value: Box::new(self.parse_postfix()?),
            }),
            _ => unreachable!(),
        }
    }

    fn parse_lambda(&mut self) -> Result<SExp, ParseError> {
        let keyword = self.next().unwrap().kind;
        let mut binds = vec![self.parse_binding(Token::LParen, Token::RParen)?];
        while self.peek() == Some(&Token::LParen) {
            binds.push(self.parse_binding(Token::LParen, Token::RParen)?);
        }
        self.expect_token(if keyword == Token::KeyWord(r"\forall") {
            Token::Arrow
        } else {
            Token::DoubleArrow
        })?;
        let mut body = self.parse_sexp()?;
        for bind in binds.into_iter().rev() {
            body = match keyword {
                Token::KeyWord(r"\forall") => SExp::Prod {
                    bind,
                    body: Box::new(body),
                },
                Token::KeyWord(r"\fun") => SExp::Lam {
                    bind,
                    body: Box::new(body),
                },
                _ => {
                    let Bind::Named(RightBind { vars, ty }) = bind else {
                        return Err(
                            self.error(ParseErrorKind::ProgramLambdaRequiresAPlainValueBinder)
                        );
                    };
                    for var in vars.into_iter().rev() {
                        body = SExp::ComputationLam {
                            var,
                            value_ty: ty.clone(),
                            body: Box::new(body),
                        };
                    }
                    body
                }
            };
        }
        Ok(body)
    }

    fn parse_program_binding(&mut self) -> Result<SExp, ParseError> {
        let sequence = self.next().unwrap().kind == Token::KeyWord(r"\bind");
        let var = self.expect_binder_ident()?;
        self.expect_token(Token::Colon)?;
        let value_ty = Box::new(self.parse_sexp()?);
        self.expect_token(if sequence {
            Token::BindArrow
        } else {
            Token::Assign
        })?;
        let rhs = Box::new(self.parse_sexp()?);
        self.expect_keyword(r"\in")?;
        let body = Box::new(self.parse_sexp()?);
        Ok(if sequence {
            SExp::Sequence {
                computation: rhs,
                var,
                value_ty,
                body,
            }
        } else {
            SExp::ValueLet {
                var,
                value_ty,
                value: rhs,
                body,
            }
        })
    }

    fn parse_arrow_nosubset(&mut self) -> Result<(Vec<RightBind>, SExp), ParseError> {
        let mut body = self.parse_sexp()?;
        let mut binds = Vec::new();
        while let SExp::Prod { bind, body: tail } = body {
            let Bind::Named(bind) = bind else {
                return Err(
                    self.error(ParseErrorKind::RefinementBindersAreNotAllowedInInductiveSignatures)
                );
            };
            binds.push(bind);
            body = *tail;
        }
        Ok((binds, body))
    }

    pub(super) fn parse_arrow_nosubset_advanced(
        &mut self,
    ) -> Result<(Vec<RightBind>, SExp, usize), ParseError> {
        let (binds, body) = self.parse_arrow_nosubset()?;
        Ok((binds, body, self.pos))
    }

    // Precedence, weakest first: assignment, arrows, equality, application, postfix, atom.
    // Both arrows associate to the right. Binding forms scope over a full expression.
    fn parse_sexp(&mut self) -> Result<SExp, ParseError> {
        let mut value = self.parse_arrow()?;
        loop {
            if self.bump_if_keyword(r"\of") {
                value = SExp::Ascribe {
                    term: Box::new(value),
                    ty: Box::new(self.parse_arrow()?),
                };
                continue;
            }
            if !self.bump_if_keyword(r"\assign") {
                break;
            }
            if !matches!(self.peek(), Some(Token::Metavariable(name)) if name.starts_with('_')) {
                return Err(self.error(ParseErrorKind::ExpectedNumberedMetavariableAfterAssign));
            }
            let SExp::Meta {
                kind: SurfaceMeta::Named(number),
                span,
            } = self.parse_atom()?
            else {
                return Err(self.error(ParseErrorKind::ExpectedNumberedMetavariableAfterAssign));
            };
            value = SExp::Assign {
                value: Box::new(value),
                number,
                span,
            };
        }
        Ok(value)
    }

    fn parse_arrow(&mut self) -> Result<SExp, ParseError> {
        if matches!(self.peek(), Some(Token::KeyWord(r"\let" | r"\bind"))) {
            return self.parse_program_binding();
        }
        let left = self.parse_equality()?;
        if self.bump_if_token(Token::Arrow) {
            Ok(SExp::Prod {
                bind: Bind::Named(RightBind {
                    vars: Vec::new(),
                    ty: Box::new(left),
                }),
                body: Box::new(self.parse_arrow()?),
            })
        } else if self.bump_if_token(Token::ComputationArrow) {
            Ok(SExp::ComputationFunction {
                domain: Box::new(left),
                codomain: Box::new(self.parse_arrow()?),
            })
        } else {
            Ok(left)
        }
    }

    pub(super) fn parse_sexp_advanced(&mut self) -> Result<(SExp, usize), ParseError> {
        let exp = self.parse_sexp()?;
        let advanced_pos = self.pos;
        Ok((exp, advanced_pos))
    }

    // parse marco tokens
    fn parse_macro_sequence_until(
        &mut self,
        close: &Token<'a>,
    ) -> Result<Vec<MacroExp>, ParseError> {
        let mut tokens = Vec::new();
        while self.peek().is_some() && self.peek() != Some(close) {
            tokens.push(self.parse_one_macro()?);
        }
        Ok(tokens)
    }

    fn parse_one_macro(&mut self) -> Result<MacroExp, ParseError> {
        if let Some(Token::MacroRest(name)) = self.peek() {
            if !self.allow_macro_parameters {
                return Err(self.error(ParseErrorKind::RestSplicesAreOnlyValidInMacroTemplates));
            }
            let name = Identifier(name[2..].to_string());
            self.next();
            return Ok(MacroExp::Splice(name));
        }

        if self.bump_if_token(Token::LBrace) {
            let exp = self.parse_sexp()?;
            self.expect_token(Token::RBrace)?;
            return Ok(MacroExp::RawExp(exp));
        }
        if self.peek() != Some(&Token::LParen) && self.starts_atom() {
            let exp = self.parse_postfix()?;
            if self.allow_macro_parameters
                && let SExp::AccessPath {
                    access: LocalAccess::Current { access, .. },
                    parameters,
                } = &exp
                && parameters.is_empty()
            {
                return Ok(MacroExp::TemplateName(access.clone()));
            }
            return Ok(MacroExp::RawExp(exp));
        }
        // 2. challenge one macro token
        // OthetSymbolStart or KeyWord which is not contained in *_KEYWORDS
        if let Some(Token::Macro(_)) = self.peek() {
            let sym = self.expect_othersymbol()?;
            return Ok(MacroExp::Tok(MacroToken(sym.to_string())));
        }
        if let Some(Token::QuotedMacro(value)) = self.peek() {
            let value = value[1..value.len() - 1].to_string();
            self.next();
            return Ok(MacroExp::Quoted(value));
        }
        // 3. Parended sequence of macro tokens
        if self.bump_if_token(Token::LParen) {
            let mut exps = Vec::new();
            while !self.bump_if_token(Token::RParen) {
                let exp = self.parse_one_macro()?;
                exps.push(exp);
            }
            return Ok(MacroExp::Seq(exps));
        }
        Err(ParseError {
            kind: ParseErrorKind::ExpectedMacroExpression,
            start: self.span_at(self.pos).start,
            end: self.span_at(self.pos).end,
            source: None,
        })
    }
}

impl<'a> TokenCursor<'a> for TermParser<'a> {
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
        #[cfg(test)]
        {
            self.consumed += position - self.pos;
        }
        self.pos = position;
    }
}

#[cfg(test)]
mod tests {
    use super::super::lex_all;
    use super::*;

    #[test]
    fn ascription_has_low_precedence_and_associates_left() {
        let SExp::Ascribe { term, ty } = complete(r"f x \of A -> B") else {
            panic!()
        };
        assert!(matches!(*term, SExp::App { .. }));
        assert!(matches!(*ty, SExp::Prod { .. }));
        let SExp::Ascribe { term, .. } = complete(r"a = b \of \Prop") else {
            panic!()
        };
        assert!(matches!(*term, SExp::Equal { .. }));
        let SExp::Ascribe { term, .. } = complete(r"a \of A \of B") else {
            panic!()
        };
        assert!(matches!(*term, SExp::Ascribe { .. }));
        let SExp::Assign { value, .. } = complete(r"a \of A \assign _1") else {
            panic!()
        };
        assert!(matches!(*value, SExp::Ascribe { .. }));
        let SExp::App { func, .. } = complete(r"(f \of A -> B) x") else {
            panic!()
        };
        assert!(matches!(*func, SExp::Ascribe { .. }));
    }

    fn complete_with<T>(
        input: &str,
        parse: impl FnOnce(&mut TermParser<'_>) -> Result<T, ParseError>,
    ) -> T {
        let tokens = lex_all(input).unwrap();
        let mut parser = TermParser::new(&tokens);
        let result = parse(&mut parser).unwrap_or_else(|error| panic!("{input}: {error:?}"));
        assert_eq!(parser.pos, tokens.len(), "unconsumed input: {input}");
        assert_eq!(parser.consumed, tokens.len());
        result
    }

    fn complete(input: &str) -> SExp {
        complete_with(input, |parser| parser.parse_sexp())
    }

    #[test]
    fn assignment_captures_the_arrow_and_supports_chaining() {
        let SExp::Assign {
            value, number: 2, ..
        } = complete(r"A -> B \assign _1 \assign _2")
        else {
            panic!("expected outer assignment");
        };
        let SExp::Assign {
            value, number: 1, ..
        } = *value
        else {
            panic!("expected inner assignment");
        };
        assert!(matches!(*value, SExp::Prod { .. }));
    }

    #[test]
    fn predictive_parser_consumes_nested_tokens_once() {
        for depth in [8, 24, 48] {
            complete(&format!("{}x{}", "(".repeat(depth), ")".repeat(depth)));
            complete(&format!(
                "{}x{}",
                r"\return(".repeat(depth),
                ")".repeat(depth)
            ));
            complete(&format!("{}c", r"\bind x: A <- f x \in ".repeat(depth)));
            complete(&format!(
                "{}c{}",
                r"\match x \in T \with { | ctor : ".repeat(depth),
                " }".repeat(depth)
            ));
        }
    }

    #[test]
    fn new_arrows_binders_and_prefix_precedence() {
        let SExp::ComputationFunction { codomain, .. } = complete(r"A ~> B ~> \F(C)") else {
            panic!()
        };
        assert!(matches!(*codomain, SExp::ComputationFunction { .. }));
        let SExp::Prod { body, .. } = complete(r"A -> B ~> \F(C)") else {
            panic!()
        };
        assert!(matches!(*body, SExp::ComputationFunction { .. }));
        let SExp::Lam {
            bind: Bind::SubsetWithProof { proof_var, .. },
            body,
        } = complete(r"\fun (x: A \where P x \as h) (y: B) => f x y")
        else {
            panic!()
        };
        assert_eq!(proof_var.0, "h");
        assert!(matches!(*body, SExp::Lam { .. }));
        assert!(matches!(
            complete(r"\exists {x: A \where P x}"),
            SExp::Exists {
                bind: Bind::Subset { .. }
            }
        ));
        let SExp::Return { value } = complete(r"\return C::pair x y") else {
            panic!()
        };
        assert!(matches!(*value, SExp::App { .. }));
        let SExp::App { func, .. } = complete(r"\force f x") else {
            panic!()
        };
        assert!(matches!(*func, SExp::Force { .. }));
        complete(r"\cfun (x: A) (y: B) => \return y");
    }

    #[test]
    fn atom_prefix_keywords_are_right_associative() {
        let SExp::ThunkType { computation_ty } = complete(r"\U \F A") else {
            panic!("expected an outer thunk type");
        };
        assert!(matches!(*computation_ty, SExp::ReturnType { .. }));

        let SExp::IdRefl { element } = complete(r"\refl \refl x") else {
            panic!("expected an outer reflexivity term");
        };
        assert!(matches!(*element, SExp::IdRefl { .. }));

        let SExp::Thunk { computation } = complete(r"\thunk \force suspended") else {
            panic!("expected an outer thunk");
        };
        assert!(matches!(*computation, SExp::Force { .. }));

        let SExp::App { func, .. } = complete(r"\refl f x") else {
            panic!("the second atom should be applied outside the prefix keyword");
        };
        assert!(matches!(*func, SExp::IdRefl { .. }));

        complete(r"\U(A ~> \F(B))");
        complete(r"\refl(f x)");
    }

    #[test]
    fn postfix_application_and_equality_precedence() {
        let SExp::Prod {
            bind: Bind::Named(bind),
            body,
        } = complete(r"f::apply x::value y = g z -> R ~> S")
        else {
            panic!("expected an arrow outside the equality");
        };
        assert!(matches!(*body, SExp::ComputationFunction { .. }));
        let SExp::Equal { left, right } = *bind.ty else {
            panic!("expected equality between applications");
        };
        assert!(matches!(*right, SExp::App { .. }));
        let SExp::App { func, .. } = *left else {
            panic!("expected application to y");
        };
        let SExp::App { func, arg } = *func else {
            panic!("application should associate to the left");
        };
        assert!(matches!(*func, SExp::AssociatedAccess { field, .. } if field.0 == "apply"));
        assert!(matches!(*arg, SExp::AssociatedAccess { field, .. } if field.0 == "value"));

        let SExp::AssociatedAccess { base, field, .. } = complete(r"(f x)::first::second") else {
            panic!("expected chained field access");
        };
        assert_eq!(field.0, "second");
        let SExp::AssociatedAccess { base, field, .. } = *base else {
            panic!("field access should associate to the left");
        };
        assert_eq!(field.0, "first");
        assert!(matches!(*base, SExp::App { .. }));

        let SExp::App { func, arg } = complete(r"x y #field z") else {
            panic!("expected application to z");
        };
        assert!(matches!(*arg, SExp::AccessPath { .. }));
        let SExp::App { func, arg } = *func else {
            panic!("expected application of x to the projected y");
        };
        assert!(matches!(*func, SExp::AccessPath { .. }));
        assert!(
            matches!(*arg, SExp::InferredProjection { field, value, .. } if field.0 == "field" && matches!(*value, SExp::AccessPath { .. }))
        );

        let SExp::InferredProjection { value, field, .. } = complete(r"(x y) #first #second")
        else {
            panic!("expected chained projection");
        };
        assert_eq!(field.0, "second");
        let SExp::InferredProjection { value, field, .. } = *value else {
            panic!("expected inner projection");
        };
        assert_eq!(field.0, "first");
        assert!(matches!(*value, SExp::App { .. }));

        let SExp::App { func, arg } = complete(r"x #field{y}") else {
            panic!("expected application of the existing projection atom");
        };
        assert!(matches!(*func, SExp::AccessPath { .. }));
        assert!(matches!(*arg, SExp::InferredProjection { field, .. } if field.0 == "field"));

        let SExp::AssociatedAccess { field, .. } = complete(r"Pair[A]::first^") else {
            panic!("expected reflected associated access");
        };
        assert_eq!(field.0, "first^");
        let SExp::AssociatedAccess { field, .. } = complete(r"Pair[A]::#^") else {
            panic!("expected reflected record constructor");
        };
        assert_eq!(field.0, "#^");

        let SExp::Prod {
            bind: Bind::Named(bind),
            ..
        } = complete(r"\exists f x = g y -> R")
        else {
            panic!("an unbraced existential should stop before the arrow");
        };
        assert!(matches!(*bind.ty, SExp::Exists { bind: Bind::Named(bind) }
            if matches!(*bind.ty, SExp::Equal { .. })));

        complete(r"(x = y) = z");
        complete(r"x = (y = z)");
        assert!(super::super::str_parse_exp(r"x = y = z").is_err());
    }

    #[test]
    fn program_bindings_scope_over_the_remaining_expression() {
        let SExp::ValueLet { var, body, .. } =
            complete(r"\let x: A := outer \in \bind y: B <- f x \in \return y")
        else {
            panic!()
        };
        assert_eq!(var.0, "x");
        let SExp::Sequence { var, body, .. } = *body else {
            panic!()
        };
        assert_eq!(var.0, "y");
        assert!(matches!(*body, SExp::Return { .. }));
        let SExp::Sequence {
            computation, body, ..
        } = complete(r"\bind x: A <- \bind y: A <- c \in f y \in g x")
        else {
            panic!()
        };
        assert!(matches!(*computation, SExp::Sequence { .. }));
        assert!(matches!(*body, SExp::App { .. }));
        complete(r"f (\thunk (\let x: A := a \in \return x))");
    }

    #[test]
    fn program_block_parses_statement_sequencing() {
        let SExp::Program(block) =
            complete(r"\program { \let x: A := a \then \bind y: B <- f x \then \return y }")
        else {
            panic!()
        };
        assert!(matches!(block.statements[0], Statement::Let { .. }));
        assert!(matches!(block.statements[1], Statement::Bind { .. }));
        assert!(matches!(*block.result, SExp::AccessPath { .. }));
    }

    #[test]
    fn block_fun_accepts_adjacent_binder_groups() {
        let SExp::Block(block) = complete(r"\block { \fun (x, y: A) (h: P x) \then \return h }")
        else {
            panic!("expected block");
        };
        let [Statement::Fun(binds)] = block.statements.as_slice() else {
            panic!("expected one fun statement");
        };
        assert_eq!(binds.len(), 2);
        assert_eq!(binds[0].vars.len(), 2);
        assert_eq!(binds[1].vars.len(), 1);
    }

    #[test]
    fn records_remain_unclassified_and_case_has_an_unambiguous_body() {
        let SExp::RecordTypeCtor { fields, .. } =
            complete(r"Future[A] { suspended := \thunk (\return x) }")
        else {
            panic!()
        };
        assert!(matches!(fields[0].1, SExp::Thunk { .. }));
        complete(r"Empty {}");
        complete(r"f ({ x : A \where P })");
        complete(r"\match x \in T \return R \with { | ctor : branch }");
        let SExp::ProgramCase { branches, .. } =
            complete(r"\match x \in T \with { | ctor a b : \return a }")
        else {
            panic!()
        };
        assert_eq!(branches[0].1.len(), 2);
        complete(r"\match x \in T \with { | empty : x | ctor a : \bind y: A <- f a \in g y }");
    }

    #[test]
    fn branch_forms_share_delimiters_and_preserve_nested_bodies() {
        for (prefix, head, template) in [
            (r"\match x \in T \with", "ctor a", false),
            (r"\match x \in T \return R \with", "ctor", false),
            (r"\tmatch token", "_", true),
        ] {
            let separator = if template { "=>" } else { ":" };
            for branches in [
                "{}".to_string(),
                format!(
                    "{{ | {head} {separator} \\match y \\in T \\with {{ | ctor : c }} | {head} {separator} f x = y }}"
                ),
            ] {
                let input = format!("{prefix} {branches}");
                let exp = complete_with(&input, |parser| {
                    parser.allow_macro_parameters = template;
                    parser.parse_sexp()
                });
                let bodies = match exp {
                    SExp::ProgramCase { branches, .. } => branches
                        .into_iter()
                        .map(|(_, _, body)| body)
                        .collect::<Vec<_>>(),
                    SExp::IndCase { branches, .. } => {
                        branches.into_iter().map(|(_, _, body)| body).collect()
                    }
                    SExp::TokenMatch { branches, .. } => {
                        branches.into_iter().map(|(_, body)| body).collect()
                    }
                    _ => panic!("expected a branch expression: {input}"),
                };
                if branches == "{}" {
                    assert!(bodies.is_empty());
                } else {
                    assert_eq!(bodies.len(), 2);
                    assert!(matches!(bodies[0], SExp::ProgramCase { .. }));
                    assert!(matches!(bodies[1], SExp::Equal { .. }));
                }
            }

            for (branches, bad) in [
                (
                    format!("{{ {head} {separator} x }}"),
                    head.split_whitespace().next().unwrap(),
                ),
                (format!("{{ | {head} {separator} ; }}"), ";"),
                (format!("{{ | {head} {separator} }}"), "}"),
                (
                    format!("{{ | {head} {separator} | {head} {separator} y }}"),
                    "|",
                ),
                (format!("{{ | {head} {separator} x"), ""),
            ] {
                let input = format!("{prefix} {branches}");
                let tokens = lex_all(&input).unwrap();
                let mut parser = if template {
                    TermParser::new_macro_template(&tokens)
                } else {
                    TermParser::new(&tokens)
                };
                let error = parser.parse_sexp().unwrap_err();
                assert_eq!(&input[error.start..error.end], bad, "{input}: {error:?}");
                assert_eq!(parser.consumed, parser.pos);
            }
        }
    }

    #[test]
    fn macro_groups_and_embedded_expressions_are_distinct() {
        let SExp::NamedMacro { tokens, .. } = complete(r"m!{(x) { f (g x) }}") else {
            panic!()
        };
        assert!(matches!(&tokens[0], MacroExp::Seq(xs) if xs.len() == 1));
        assert!(matches!(&tokens[1], MacroExp::RawExp(SExp::App { .. })));
        complete(r"\( (a + b) + { f (g x) } \)");
    }

    #[test]
    fn malformed_productions_commit_at_the_failing_token() {
        for (input, bad) in [
            (r"f[x, ;]", ";"),
            (r"\fun (x: A \where P \as ) => x", ")"),
            (r"T { field := ; }", ";"),
            (r"\match x \in T \with { | ctor x : ; }", ";"),
            (r"\match x \in T { | ctor : c }", "{"),
            (r"\match x \in T \with { | ctor : c; }", ";"),
            (r"m!{{ f (x ; }}", ";"),
            (r"\let x: A := a;", ";"),
            (r"\let x: A := a \in ;", ";"),
            (r"\bind x <- c \in d", "<-"),
            (r"\Set(12 x)", "x"),
        ] {
            let tokens = lex_all(input).unwrap();
            let mut parser = TermParser::new(&tokens);
            let error = parser.parse_sexp().unwrap_err();
            assert_eq!(&input[error.start..error.end], bad, "{input}: {error:?}");
            assert_eq!(parser.consumed, parser.pos);
        }
    }

    #[test]
    fn parse_annotate_test() {
        for input in [r"x: X", r"y: (A -> B)", r"x: h (X Y)", r"x, y, z: X -> Y"] {
            complete_with(input, |parser| parser.parse_annotate());
        }
    }

    #[test]
    fn parse_rightbinds_test() {
        for input in [r"x: X", r"x: X, y: Y", r"x, y: X -> Y, z: Z"] {
            complete_with(input, |parser| parser.parse_annotate_comma_separated());
        }
        for input in [r"(x: X)", r"(x: X, y: Y)", r"(x, y: X -> Y, z: Z)"] {
            complete_with(input, |parser| parser.parse_simple_binds_paren());
        }
    }

    #[test]
    fn parse_bind_test() {
        for input in [
            r"(x: X \where P)",
            r"(x: X \where p1 p2)",
            r"(x: X \where p1 p2 \as h)",
        ] {
            complete_with(input, |parser| {
                parser.parse_binding(Token::LParen, Token::RParen)
            });
        }
    }

    #[test]
    fn parse_equality_test() {
        for input in [r"x", r"x y", r"\into[A](x, X) \by { p }", r"x = y"] {
            complete_with(input, |parser| parser.parse_equality());
        }
    }

    #[test]
    fn parse_nosubset_arrow_test() {
        for input in [
            r"\forall (x: X) -> Y",
            r"\forall (x: X) -> \forall (y: Y) -> Z",
        ] {
            complete_with(input, |parser| parser.parse_arrow_nosubset());
        }
    }
    #[test]
    fn parse_atom_test() {
        fn print_and_unwrap(input: &'static str) {
            let lex = &lex_all(input).expect("lexing failed for atom test");
            let mut parser = TermParser::new(lex);
            let result = parser.parse_atom();
            match result {
                Ok(atomlike) => {
                    println!("Parsed SExp: {:?} => {:?}\n\n", input, atomlike);
                }
                Err(err) => {
                    panic!(" {:?}", err);
                }
            }
            assert!(parser.pos == parser.tokens.len());
        }
        print_and_unwrap(r"x");
        print_and_unwrap(r"(x)");
        print_and_unwrap(r"x.y");
        print_and_unwrap(r"x[ A, B, C ]");
        print_and_unwrap(r"x.y[ A, B ]");
        print_and_unwrap(r"Bool^");
        print_and_unwrap(r"types.Bool^[A]");
        print_and_unwrap(r"Bool^::true");
        print_and_unwrap(r"types.Wrap ^ [Bool ^]::wrap");
        print_and_unwrap(r"x { a := A, b := B }");
        print_and_unwrap(r"x.y { a := A, b := B }");
        print_and_unwrap(r"x.y[ A, B ] { a := A, b := B }");
        print_and_unwrap(r"x::y"); // Repeated :: is handled by parse_postfix.
        print_and_unwrap(r"List[Nat]::Nil");
        print_and_unwrap(r"list.List[Nat]::Nil");
        print_and_unwrap(r"Group[Nat] { mul := x, e := y }");
        print_and_unwrap(r"\( x + y \)");
        print_and_unwrap(r"mymacro!{ a + b c }");
    }

    fn print_and_unwrap(input: &'static str) {
        let lex = &lex_all(input).expect("lexing failed for exp test");
        let mut parser = TermParser::new(lex);
        let result = parser.parse_sexp();
        match result {
            Ok(atomlike) => {
                println!("Parsed SExp: {:?} => {:?}\n\n", input, atomlike);
            }
            Err(err) => {
                panic!(" {:?}", err);
            }
        }
        assert!(parser.pos == parser.tokens.len());
    }
    #[test]
    fn parse_exp_test() {
        // identifier and lambda calcluluses
        print_and_unwrap(r"x");
        print_and_unwrap(r"x y");
        print_and_unwrap(r"x (y z)");
        print_and_unwrap(r"(x y) z");
        print_and_unwrap(r"\forall (x: X) -> Y");
        print_and_unwrap(r"\fun (x: X) => y");
        print_and_unwrap(r"\forall (x: X) -> \fun (_: Y) => z");
        print_and_unwrap(r"X -> Z");
        print_and_unwrap(r"x y z -> Y");
        print_and_unwrap(r"(x y) -> Y");
        print_and_unwrap(r"\forall (x: X) -> \forall (y: Y) -> Z");
        print_and_unwrap(r"\forall (x: X \where P) -> \forall (y: Y) -> Z");
        print_and_unwrap(r"\forall (x: X \where P \as h) -> \forall (y: Y) -> Z");
        print_and_unwrap(r"\forall (x: F (P y) \where b (a u) \as h) -> \forall (y: Y) -> Z");
        print_and_unwrap(r"(X -> Y) Z (\fun (t: T) => z)");
        print_and_unwrap(r"(\fun (x: X) => y)");
        print_and_unwrap(r"\fun (x: X \where P) => y");
    }
    #[test]
    fn parse_access_and_record_test() {
        // access path and record construction
        print_and_unwrap(r"x");
        print_and_unwrap(r"x.y");
        print_and_unwrap(r"x[ A, B, C ]");
        print_and_unwrap(r"x.y[ A, B ]");
        print_and_unwrap(r"x { a := A, b := B }");
        print_and_unwrap(r"x.y { a := A, b := B }");
        print_and_unwrap(r"x.y[ A, B ] { a := A, b := B }");
        print_and_unwrap(r"x::y");
        print_and_unwrap(r"x::y::z");
        print_and_unwrap(r"List[Nat]::Nil");
        print_and_unwrap(r"list.List[Nat]::Nil");
        print_and_unwrap(r"Group[Nat] { mul := x, e := y }");
    }
    #[test]
    fn parse_special_exp_test() {
        // atom like: sort, access path, math macro, named macro
        print_and_unwrap("x");
        print_and_unwrap(r"\Prop");
        print_and_unwrap(r"\Set");
        print_and_unwrap(r"\Set(3)");
        print_and_unwrap(r"\Set(3) x");
        print_and_unwrap(r"x \Set(3)");
        print_and_unwrap(r"x.y");
        print_and_unwrap(r"x.a b (c. g)");
        print_and_unwrap(r"x \( y + z \) l");
        print_and_unwrap(r"x mymacro!{ a + b c } l");
        print_and_unwrap(r"x::y::z");
        print_and_unwrap(r"\into[A](x, X) \by { p }");
        print_and_unwrap(r"\exact(x, X)");
        print_and_unwrap(r"\refl(x)");
        print_and_unwrap(r"\idelim a = b \with x: X => P x \by { base: pa, equality: eq }");
        print_and_unwrap(r"\axiom:setext(A, B, ab, ba)");
        print_and_unwrap(r"\axiom:funext(f, g, pointwise)");
        print_and_unwrap(r"\axiom:classicalIndefiniteChoice(X, Y, inhabited)");
        print_and_unwrap(r"\choiceeq x \of X \by { existence: existsX, uniqueness: uniqueX }");
        print_and_unwrap(r"\choice X \by { existence: existsX, uniqueness: uniqueX }");
        print_and_unwrap(r"\take (x: X) => P \by { existsX }");
        print_and_unwrap(r"x = y");
    }

    #[test]
    fn parse_complex_cases_test() {
        print_and_unwrap(r"x::y x::y");
        print_and_unwrap(r"(x)::y");
        print_and_unwrap(r"x x::y");
        print_and_unwrap(r"x::y::z x::y::z");
    }
    #[test]
    fn parse_sexp_has_remaining() {
        // Delimiters belong to the enclosing production, including branch pipes.
        for delimiter in [";", "|", "{", "}", ")", ",", r"\in", r"\with"] {
            let input = format!("f x::value {delimiter}");
            let tokens = lex_all(&input).unwrap();
            let mut parser = TermParser::new(&tokens);
            assert!(matches!(parser.parse_sexp().unwrap(), SExp::App { .. }));
            assert_eq!(parser.pos, tokens.len() - 1, "{input}");
            let remaining = &tokens[parser.pos];
            assert_eq!(&input[remaining.start..remaining.end], delimiter);
            assert_eq!(parser.consumed, parser.pos);
        }
        let tokens = lex_all(r"x (( y: Y)").unwrap();
        assert!(TermParser::new(&tokens).parse_sexp().is_err());
    }
}
