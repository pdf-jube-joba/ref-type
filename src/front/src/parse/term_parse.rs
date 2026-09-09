use super::{
    EXPRESSION_ATOM_KEYWORDS, PROOF_TERM_KEYWORDS, ParseError, Parser, SORT_KEYWORDS, SpannedToken,
    Token, TokenCursor,
};
use crate::syntax::*;

pub(super) struct TermParser<'a> {
    tokens: &'a [SpannedToken<'a>],
    pos: usize,
    allow_macro_parameters: bool,
    #[cfg(test)]
    consumed: usize,
}

impl<'a> TermParser<'a> {
    pub(super) fn new(tokens: &'a [SpannedToken<'a>]) -> Self {
        Self {
            tokens,
            pos: 0,
            allow_macro_parameters: false,
            #[cfg(test)]
            consumed: 0,
        }
    }

    pub(super) fn new_macro_template(tokens: &'a [SpannedToken<'a>]) -> Self {
        Self {
            tokens,
            pos: 0,
            allow_macro_parameters: true,
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
                        msg: format!("invalid number: {}", num_str),
                        start: t.start,
                        end: t.end,
                    }),
                },
                other => Err(ParseError {
                    msg: format!("expected number, found {:?}", other),
                    start: t.start,
                    end: t.end,
                }),
            },
            None => Err(self.eof_error("number")),
        }
    }

    fn expect_othersymbol(&mut self) -> Result<&'a str, ParseError> {
        match self.next() {
            Some(t) => match &t.kind {
                Token::Macro(sym_str) => Ok(sym_str),
                other => Err(ParseError {
                    msg: format!("expected other symbol, found {:?}", other),
                    start: t.start,
                    end: t.end,
                }),
            },
            None => Err(self.eof_error("other symbol")),
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

    // Parse a parenthesized number (e.g., "(0)").
    fn parse_number_paren(&mut self) -> Result<usize, ParseError> {
        self.expect_token(Token::LParen)?;
        let number = self.expect_number()?;
        self.expect_token(Token::RParen)?;

        Ok(number)
    }

    // Parse a sort expression.
    // \Prop | \PropKind | \Set ( "(" <number> ")" )? | \SetKind ( "(" <number> ")" )?
    fn parse_sort(&mut self) -> Result<crate::raw::sort::Sort, ParseError> {
        if self.bump_if_keyword("\\Prop") {
            return Ok(crate::raw::sort::Sort::Prop);
        }
        if self.bump_if_keyword("\\PropKind") {
            return Ok(crate::raw::sort::Sort::PropKind);
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

            return Ok(crate::raw::sort::Sort::Set(number));
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
            return Ok(crate::raw::sort::Sort::SetKind(number));
        }
        Err(ParseError {
            msg: "expected sort keyword".into(),
            start: self.span_at(self.pos).start,
            end: self.span_at(self.pos).end,
        })
    }

    fn parse_keyword_head_atom(&mut self) -> Result<SExp, ParseError> {
        if self.bump_if_keyword(r"\tmatch") {
            if !self.allow_macro_parameters {
                return Err(self.error("token matching is only valid in named macro templates"));
            }
            let target = self.expect_ident()?;
            self.expect_token(Token::LBrace)?;
            let mut branches = Vec::new();
            while !self.bump_if_token(Token::RBrace) {
                self.expect_token(Token::Pipe)?;
                let pattern = if self.bump_if_token(Token::Hole) {
                    TokenMatchPattern::Default
                } else {
                    let mut parser = Parser::new(&self.tokens[self.pos..]);
                    let atom = parser.parse_macro_pattern_atom()?;
                    self.set_position(self.pos + parser.pos);
                    match atom {
                        MacroSeqAtom::Seq(items) => TokenMatchPattern::Sequence(items),
                        atom @ (MacroSeqAtom::Tok(_) | MacroSeqAtom::Quoted(_)) => {
                            TokenMatchPattern::Token(atom)
                        }
                        _ => return Err(self.error("expected fixed token, sequence pattern, or _")),
                    }
                };
                self.expect_token(Token::DoubleArrow)?;
                let body = self.parse_sexp()?;
                self.expect_token(Token::Semicolon)?;
                branches.push((pattern, body));
            }
            return Ok(SExp::TokenMatch { target, branches });
        }
        if self.bump_if_keyword("\\VType") {
            return Ok(SExp::ValueType);
        }
        if self.bump_if_keyword("\\U") {
            return self.parse_parenthesized(|parser| {
                parser.parse_sexp().map(|computation_ty| SExp::ThunkType {
                    computation_ty: Box::new(computation_ty),
                })
            });
        }
        if self.bump_if_keyword("\\F") {
            return self.parse_parenthesized(|parser| {
                parser.parse_sexp().map(|value_ty| SExp::ReturnType {
                    value_ty: Box::new(value_ty),
                })
            });
        }
        if self.bump_if_keyword(r"\record") {
            let access = self.parse_access_path()?;
            let parameters = self.parse_optional_parameters()?;
            let fields = self.parse_record_body()?;
            return Ok(SExp::RecordTypeCtor {
                access,
                parameters,
                fields,
            });
        }
        if self.bump_if_keyword(r"\match") {
            let scrutinee = self.parse_sexp()?;
            self.expect_keyword(r"\in")?;
            let path = self.parse_access_path()?;
            self.expect_keyword(r"\with")?;
            self.expect_token(Token::LBrace)?;
            let mut branches = Vec::new();
            while !self.bump_if_token(Token::RBrace) {
                self.expect_token(Token::Pipe)?;
                let constructor = self.expect_ident()?;
                let mut binders = Vec::new();
                while matches!(self.peek(), Some(Token::Ident(_))) {
                    binders.push(self.expect_ident()?);
                }
                self.expect_token(Token::DoubleArrow)?;
                let body = self.parse_sexp()?;
                self.expect_token(Token::Semicolon)?;
                branches.push((constructor, binders, body));
            }
            return Ok(SExp::ProgramCase {
                path,
                scrutinee: Box::new(scrutinee),
                branches,
            });
        }
        // simple cases (<keyword> "(" expressions with comma separated ")")
        if self.bump_if_keyword("\\Power") {
            return self.parse_parenthesized(|parser| {
                parser
                    .parse_sexp()
                    .map(|set| SExp::PowerSet { set: Box::new(set) })
            });
        }
        if self.bump_if_keyword("\\Subset") {
            return self.parse_parenthesized(|parser| {
                let var = parser.expect_ident()?;
                parser.expect_token(Token::Comma)?;
                let set = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let predicate = parser.parse_sexp()?;
                Ok(SExp::SubSet {
                    var,
                    set: Box::new(set),
                    predicate: Box::new(predicate),
                })
            });
        }
        if self.bump_if_keyword("\\Pred") {
            return self.parse_parenthesized(|parser| {
                let superset = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let subset = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let element = parser.parse_sexp()?;
                Ok(SExp::Pred {
                    superset: Box::new(superset),
                    subset: Box::new(subset),
                    element: Box::new(element),
                })
            });
        }
        if self.bump_if_keyword("\\Ty") {
            return self.parse_parenthesized(|parser| {
                let superset = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let subset = parser.parse_sexp()?;
                Ok(SExp::TypeLift {
                    superset: Box::new(superset),
                    subset: Box::new(subset),
                })
            });
        }
        if self.bump_if_keyword("\\subsetinto") {
            return self.parse_parenthesized(|parser| {
                let superset = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let subset = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let element = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let proof = parser.parse_sexp()?;
                Ok(SExp::SubsetIntro {
                    superset: Box::new(superset),
                    subset: Box::new(subset),
                    element: Box::new(element),
                    proof: Box::new(proof),
                })
            });
        }
        let program_form = self.bump_if_keyword("\\PRunStep");
        if program_form || self.bump_if_keyword("\\RunStep") {
            return self.parse_parenthesized(|parser| {
                let state_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let result_ty = parser.parse_sexp()?;
                Ok(if program_form {
                    SExp::PRunStep {
                        state_ty: Box::new(state_ty),
                        result_ty: Box::new(result_ty),
                    }
                } else {
                    SExp::RunStep {
                        state_ty: Box::new(state_ty),
                        result_ty: Box::new(result_ty),
                    }
                })
            });
        }
        let program_form = self.bump_if_keyword("\\Pcontinue");
        if program_form || self.bump_if_keyword("\\continue") {
            return self.parse_parenthesized(|parser| {
                let state_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let result_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let next = parser.parse_sexp()?;
                Ok(if program_form {
                    SExp::PContinue {
                        state_ty: Box::new(state_ty),
                        result_ty: Box::new(result_ty),
                        next: Box::new(next),
                    }
                } else {
                    SExp::Continue {
                        state_ty: Box::new(state_ty),
                        result_ty: Box::new(result_ty),
                        next: Box::new(next),
                    }
                })
            });
        }
        let program_form = self.bump_if_keyword("\\Pfinish");
        if program_form || self.bump_if_keyword("\\finish") {
            return self.parse_parenthesized(|parser| {
                let state_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let result_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let output = parser.parse_sexp()?;
                Ok(if program_form {
                    SExp::PFinish {
                        state_ty: Box::new(state_ty),
                        result_ty: Box::new(result_ty),
                        output: Box::new(output),
                    }
                } else {
                    SExp::Finish {
                        state_ty: Box::new(state_ty),
                        result_ty: Box::new(result_ty),
                        output: Box::new(output),
                    }
                })
            });
        }
        if self.bump_if_keyword("\\Acc") {
            return self.parse_parenthesized(|parser| {
                let state_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let result_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let step = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let state = parser.parse_sexp()?;
                Ok(SExp::Acc {
                    state_ty: Box::new(state_ty),
                    result_ty: Box::new(result_ty),
                    step: Box::new(step),
                    state: Box::new(state),
                })
            });
        }
        let program_form = self.bump_if_keyword("\\Prun");
        if program_form || self.bump_if_keyword("\\run") {
            let (state_ty, result_ty, step, initial) = self.parse_parenthesized(|parser| {
                let state_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let result_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let step = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let initial = parser.parse_sexp()?;
                Ok((state_ty, result_ty, step, initial))
            })?;
            let accessibility = if program_form && !self.bump_if_keyword("\\by") {
                None
            } else {
                if !program_form {
                    self.expect_keyword("\\by")?;
                }
                Some(Box::new(self.parse_sexp()?))
            };
            return Ok(if program_form {
                SExp::PRun {
                    state_ty: Box::new(state_ty),
                    result_ty: Box::new(result_ty),
                    step: Box::new(step),
                    initial: Box::new(initial),
                    accessibility,
                }
            } else {
                SExp::Run {
                    state_ty: Box::new(state_ty),
                    result_ty: Box::new(result_ty),
                    step: Box::new(step),
                    initial: Box::new(initial),
                    accessibility: accessibility.expect("required above"),
                }
            });
        }
        let program_form = self.bump_if_keyword("\\PrunCase");
        if program_form || self.bump_if_keyword("\\runCase") {
            let (state_ty, result_ty, step, initial, transition) =
                self.parse_parenthesized(|parser| {
                    let state_ty = parser.parse_sexp()?;
                    parser.expect_token(Token::Comma)?;
                    let result_ty = parser.parse_sexp()?;
                    parser.expect_token(Token::Comma)?;
                    let step = parser.parse_sexp()?;
                    parser.expect_token(Token::Comma)?;
                    let initial = parser.parse_sexp()?;
                    parser.expect_token(Token::Comma)?;
                    let transition = parser.parse_sexp()?;
                    Ok((state_ty, result_ty, step, initial, transition))
                })?;
            let proofs = if program_form && !self.bump_if_keyword("\\by") {
                None
            } else {
                if !program_form {
                    self.expect_keyword("\\by")?;
                }
                Some(self.parse_parenthesized(|parser| {
                    let accessibility = parser.parse_sexp()?;
                    parser.expect_token(Token::Comma)?;
                    let transition_equality = parser.parse_sexp()?;
                    Ok((Box::new(accessibility), Box::new(transition_equality)))
                })?)
            };
            return Ok(if program_form {
                let (accessibility, transition_equality) = proofs
                    .map(|(a, e)| (Some(a), Some(e)))
                    .unwrap_or((None, None));
                SExp::PRunCase {
                    state_ty: Box::new(state_ty),
                    result_ty: Box::new(result_ty),
                    step: Box::new(step),
                    initial: Box::new(initial),
                    transition: Box::new(transition),
                    accessibility,
                    transition_equality,
                }
            } else {
                let (accessibility, transition_equality) = proofs.expect("required above");
                SExp::RunCase {
                    state_ty: Box::new(state_ty),
                    result_ty: Box::new(result_ty),
                    step: Box::new(step),
                    initial: Box::new(initial),
                    transition: Box::new(transition),
                    accessibility,
                    transition_equality,
                }
            });
        }
        if self.bump_if_keyword("\\runStepRec") {
            return self.parse_parenthesized(|parser| {
                let state_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let result_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let motive = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let on_continue = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let on_finish = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let scrutinee = parser.parse_sexp()?;
                Ok(SExp::RunStepRec {
                    state_ty: Box::new(state_ty),
                    result_ty: Box::new(result_ty),
                    motive: Box::new(motive),
                    on_continue: Box::new(on_continue),
                    on_finish: Box::new(on_finish),
                    scrutinee: Box::new(scrutinee),
                })
            });
        }
        if self.bump_if_keyword("\\Box") {
            return self.parse_parenthesized(|parser| {
                parser.parse_sexp().map(|program_ty| SExp::BoxType {
                    program_ty: Box::new(program_ty),
                })
            });
        }
        if self.bump_if_keyword("\\box") {
            return self.parse_parenthesized(|parser| {
                let program_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let program = parser.parse_sexp()?;
                Ok(SExp::BoxProgram {
                    program_ty: Box::new(program_ty),
                    program: Box::new(program),
                })
            });
        }
        if self.bump_if_keyword("\\Force") {
            return self.parse_parenthesized(|parser| {
                let program_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let boxed = parser.parse_sexp()?;
                Ok(SExp::ForceBox {
                    program_ty: Box::new(program_ty),
                    boxed: Box::new(boxed),
                })
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
        // elimination of inductive type
        if self.bump_if_keyword("\\elim") {
            // r"\elim" <elim: SExp> r"\in" <path: Path> "\\return" <return_type: SExp>
            let elim = self.parse_sexp()?;
            self.expect_keyword("\\in")?; // expect '\in'
            let path = self.parse_access_path()?;
            self.expect_keyword("\\return")?; // expect '\\return'
            let return_type = self.parse_sexp()?;

            // body of case branches
            let mut cases = Vec::new();
            self.expect_token(Token::LBrace)?; // expect '{'
            // loop until '}'
            while !self.bump_if_token(Token::RBrace) {
                self.expect_token(Token::Pipe)?; // expect '|'
                let case_name = self.expect_ident()?; // expect case name
                self.expect_token(Token::DoubleArrow)?; // expect '=>'
                let case_type = self.parse_sexp()?; // parse case type
                self.expect_token(Token::Semicolon)?; // expect ';'
                cases.push((case_name, case_type));
            }

            return Ok(SExp::IndElim {
                path,
                elim: Box::new(elim),
                return_type: Box::new(return_type),
                cases,
            });
        }
        if self.bump_if_keyword("\\prec") {
            // r"\prec" "(" <sort: Sort> "," <path: AccessPath> <parameter>? ")"
            self.expect_token(Token::LParen)?;
            let sort = self.parse_sort()?;
            self.expect_token(Token::Comma)?;
            let path = self.parse_access_path()?;
            let parameters = self.parse_optional_parameters()?;

            self.expect_token(Token::RParen)?;

            return Ok(SExp::IndElimPrim {
                path,
                parameters,
                sort,
            });
        }
        // r"\exists" <binding>
        if self.bump_if_keyword("\\exists") {
            let bind = if self.peek() == Some(&Token::LBrace) {
                self.parse_binding(Token::LBrace, Token::RBrace)?
            } else {
                Bind::Named(RightBind {
                    vars: Vec::new(),
                    ty: Box::new(self.parse_combined()?),
                })
            };
            return Ok(SExp::Exists { bind });
        }
        // r"\take" <binding> "=>" <body>
        if self.bump_if_keyword("\\take") {
            let bind = self.parse_binding(Token::LParen, Token::RParen)?;
            self.expect_token(Token::DoubleArrow)?; // expect '=>'
            let body = self.parse_sexp()?;
            self.expect_keyword("\\by")?;
            self.expect_token(Token::LParen)?;
            let existence = self.parse_sexp()?;
            let uniqueness = self
                .bump_if_token(Token::Comma)
                .then(|| self.parse_sexp())
                .transpose()?;
            self.expect_token(Token::RParen)?;
            return Ok(match uniqueness {
                Some(uniqueness) => SExp::TakeSet {
                    bind,
                    body: Box::new(body),
                    existence: Box::new(existence),
                    uniqueness: Box::new(uniqueness),
                },
                None => SExp::TakeProp {
                    bind,
                    body: Box::new(body),
                    existence: Box::new(existence),
                },
            });
        }
        if self.bump_if_keyword("\\block") {
            self.expect_token(Token::LBrace)?; // expect '{'
            let block = self.parse_block()?;
            self.expect_token(Token::RBrace)?; // expect '}'
            return Ok(SExp::Block(block));
        }

        Err(ParseError {
            msg: "expected expression starting with keyword".into(),
            start: self.span_at(self.pos).start,
            end: self.span_at(self.pos).end,
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
                    msg: format!("unknown axiom: {}", name.as_str()),
                    start: self.span_at(self.pos).start,
                    end: self.span_at(self.pos).end,
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
            self.expect_token(Token::LParen)?; // expect '('
            let term = self.parse_sexp()?;
            self.expect_token(Token::RParen)?; // expect ')'
            return Ok(SExp::IdRefl {
                element: Box::new(term),
            });
        }

        // \\idelim "(" <left: SExp> "=" <right: SExp> r"\with" <var: Ident> ":" <ty: SExp> "=>" <predicate: SExp> ")"
        if self.bump_if_keyword("\\idelim") {
            self.expect_token(Token::LParen)?; // expect '('
            let left = self.parse_atom_sequence()?;
            self.expect_token(Token::Equal)?; // expect '='
            let right = self.parse_sexp()?;
            self.expect_keyword("\\with")?; // expect '\with'
            let var = self.expect_ident()?;
            self.expect_token(Token::Colon)?; // expect ':'
            let ty = self.parse_combined()?;
            self.expect_token(Token::DoubleArrow)?; // expect '=>'
            let predicate = self.parse_sexp()?;
            self.expect_token(Token::RParen)?; // expect ')'
            self.expect_keyword("\\by")?;
            self.expect_token(Token::LParen)?;
            let base = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let equality = self.parse_sexp()?;
            self.expect_token(Token::RParen)?;
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

        if self.bump_if_keyword("\\takeelim") {
            self.expect_token(Token::LParen)?;
            let func = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let element = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let domain = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let codomain = self.parse_sexp()?;
            self.expect_token(Token::RParen)?;
            self.expect_keyword("\\by")?;
            self.expect_token(Token::LParen)?;
            let existence = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let uniqueness = self.parse_sexp()?;
            self.expect_token(Token::RParen)?;
            return Ok(SExp::TakeEq {
                func: Box::new(func),
                domain: Box::new(domain),
                codomain: Box::new(codomain),
                element: Box::new(element),
                existence: Box::new(existence),
                uniqueness: Box::new(uniqueness),
            });
        }

        if self.bump_if_keyword("\\accintro") {
            self.expect_token(Token::LParen)?;
            let state_ty = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let result_ty = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let step = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let state = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let predecessors = self.parse_sexp()?;
            self.expect_token(Token::RParen)?;
            return Ok(SExp::AccIntro {
                state_ty: Box::new(state_ty),
                result_ty: Box::new(result_ty),
                step: Box::new(step),
                state: Box::new(state),
                predecessors: Box::new(predecessors),
            });
        }

        if self.bump_if_keyword("\\accdescent") {
            self.expect_token(Token::LParen)?;
            let state_ty = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let result_ty = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let step = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let from = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let to = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let accessibility = self.parse_sexp()?;
            self.expect_token(Token::Comma)?;
            let transition = self.parse_sexp()?;
            self.expect_token(Token::RParen)?;
            return Ok(SExp::AccDescent {
                state_ty: Box::new(state_ty),
                result_ty: Box::new(result_ty),
                step: Box::new(step),
                from: Box::new(from),
                to: Box::new(to),
                accessibility: Box::new(accessibility),
                transition: Box::new(transition),
            });
        }

        Err(ParseError {
            msg: "expected expression starting with keyword".into(),
            start: self.span_at(self.pos).start,
            end: self.span_at(self.pos).end,
        })
    }

    fn parse_block(&mut self) -> Result<Block, ParseError> {
        let mut statements = Vec::new();

        loop {
            if self.bump_if_keyword("\\fix") {
                // r"\fix" ("(" RightBind ")" ",")* ";"
                let mut binds: Vec<RightBind> = Vec::new();
                while self.peek() == Some(&Token::LParen) {
                    let bind = self.parse_simple_binds_paren()?;
                    binds.extend(bind);
                    if !self.bump_if_token(Token::Comma) {
                        break;
                    }
                }
                self.expect_token(Token::Semicolon)?; // expect ';'
                statements.push(Statement::Fix(binds));
                continue;
            }

            if self.bump_if_keyword("\\let") {
                // r"\let" <var: Ident> ":" <ty: SExp> ":=" <body: SExp> ";"
                let var = self.expect_ident()?;
                self.expect_token(Token::Colon)?; // expect ':'
                let ty = self.parse_sexp()?;
                self.expect_token(Token::Assign)?; // expect ':='
                let body = self.parse_sexp()?;
                self.expect_token(Token::Semicolon)?; // expect ';'
                statements.push(Statement::Let { var, ty, body });
                continue;
            }

            if self.bump_if_keyword("\\take") {
                // r"\take" <bind: Bind> r"\by" "(" proof ("," proof)? ")" ";"
                let bind = self.parse_binding(Token::LParen, Token::RParen)?;
                self.expect_keyword("\\by")?;
                self.expect_token(Token::LParen)?;
                let existence = self.parse_sexp()?;
                let uniqueness = self
                    .bump_if_token(Token::Comma)
                    .then(|| self.parse_sexp())
                    .transpose()?;
                self.expect_token(Token::RParen)?;
                self.expect_token(Token::Semicolon)?; // expect ';'
                statements.push(match uniqueness {
                    Some(uniqueness) => Statement::TakeSet {
                        bind,
                        existence,
                        uniqueness,
                    },
                    None => Statement::TakeProp { bind, existence },
                });
                continue;
            }

            if self.bump_if_keyword("\\return") {
                // r"\return" <exp: SExp> ";"
                let result = self.parse_sexp()?;
                self.expect_token(Token::Semicolon)?; // expect ';'
                return Ok(Block {
                    statements,
                    result: Box::new(result),
                });
            }

            break; // No more block statements.
        }

        Err(ParseError {
            msg: "expected block statement or \\return".into(),
            start: self.span_at(self.pos).start,
            end: self.span_at(self.pos).end,
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

    // parse an access path
    // 1. identifier | identifier "." identifier
    // ! no nesting of ".", it appears at most once
    fn parse_access_path(&mut self) -> Result<LocalAccess, ParseError> {
        // 1. expect first identifier
        let first_ident = self.expect_ident()?;
        // 2. if ".", expect more identifiers
        if self.bump_if_token(Token::Period) {
            // named scope access
            let next_ident = self.expect_ident()?;
            Ok(LocalAccess::Named {
                access: first_ident,
                child: next_ident,
            })
        } else {
            Ok(LocalAccess::Current {
                access: first_ident,
            })
        }
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
    // 2. `(<expr>)`, `$( ... $)`, `name!{ ... }`
    // 3. something start with keyword (sort, etc.)
    fn parse_atom(&mut self) -> Result<SExp, ParseError> {
        match self.peek() {
            Some(Token::MacroVar(_)) => {
                if !self.allow_macro_parameters {
                    return Err(ParseError {
                        msg: "macro captures are only valid in macro templates".into(),
                        start: self.tokens[self.pos].start,
                        end: self.tokens[self.pos].end,
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
            Some(Token::UnspecifiedVar(_)) => {
                let token = self.next().expect("peeked token exists");
                let Token::UnspecifiedVar(spelling) = token.kind else {
                    unreachable!()
                };
                let suffix = &spelling[1..];
                let kind = if suffix.is_empty() {
                    SurfaceMeta::Goal
                } else if suffix.bytes().all(|byte| byte.is_ascii_digit()) {
                    let number = suffix.parse::<u32>().map_err(|_| ParseError {
                        msg: format!("metavariable number is too large: {spelling}"),
                        start: token.start,
                        end: token.end,
                    })?;
                    SurfaceMeta::Named(number)
                } else {
                    return Err(ParseError {
                        msg: "expected `?` or `?` followed by digits".into(),
                        start: token.start,
                        end: token.end,
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
            Some(Token::Ident(_)) => {
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
                    return Ok(SExp::NamedMacro {
                        name,
                        tokens,
                        scope: None,
                        max_order: None,
                        depth: 0,
                    });
                }
                // `x`, `x.y`, `x [e1, ..., en]`, `x.ctor [e1, ..., en]`
                let access = self.parse_access_path()?;
                let parameters = self.parse_optional_parameters()?;

                // field access case or record construction case
                if self.bump_if_token(Token::DoubleColon) {
                    // field access case
                    let field_name = self.expect_ident()?;
                    return Ok(SExp::AssociatedAccess {
                        base: Box::new(SExp::AccessPath { access, parameters }),
                        field: field_name,
                    });
                }

                Ok(SExp::AccessPath { access, parameters })
            }
            Some(Token::LParen) => {
                self.next(); // consume '('
                let expr = self.parse_sexp()?;
                self.expect_token(Token::RParen)?; // expect ')'
                Ok(expr)
            }
            Some(Token::MathLParen) => {
                self.next(); // consume '$('
                let tokens = self.parse_macro_sequence_until(&Token::MathRParen)?;
                self.expect_token(Token::MathRParen)?; // expect '$)'
                Ok(SExp::MathMacro {
                    tokens,
                    scope: None,
                    max_order: None,
                    depth: 0,
                })
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
                msg: format!("unexpected keyword in atom: {}", keyword),
                start: self.span_at(self.pos).start,
                end: self.span_at(self.pos).end,
            }),
            _ => Err(ParseError {
                msg: "expected atom".into(),
                start: self.span_at(self.pos).start,
                end: self.span_at(self.pos).end,
            }),
        }
    }

    // parse field access
    // <atom>("::" Ident)?
    // this includes atom parsing
    fn field_access(&mut self) -> Result<SExp, ParseError> {
        let mut expr = self.parse_atom()?;
        while self.bump_if_token(Token::DoubleColon) {
            let field_name = self.expect_ident()?;
            expr = SExp::AssociatedAccess {
                base: Box::new(expr),
                field: field_name,
            };
        }
        Ok(expr)
    }

    // parse a sequence of atoms (AtomLike)
    // e.g. `x`, `(x)`, `x y`, `x (y z)`, `(x y) z`
    fn parse_atom_sequence(&mut self) -> Result<SExp, ParseError> {
        // 1. first atom
        let mut expr = self.field_access()?;

        while self.starts_atom() {
            let try_exp = self.field_access()?;
            expr = SExp::App {
                func: Box::new(expr),
                arg: Box::new(try_exp),
                piped: false,
            };
        }

        Ok(expr)
    }

    // parse a expression with
    // 1. record field access
    // 2. piped application ... <e: AsExp> "|" <e: AsExp>
    // 3. equal expression ... <e> "=" <e>
    fn parse_combined(&mut self) -> Result<SExp, ParseError> {
        fn piped(parser: &mut TermParser) -> Result<SExp, ParseError> {
            let mut expr = parser.parse_atom_sequence()?;

            while parser.bump_if_token(Token::Pipe) {
                let right = parser.parse_atom_sequence()?;
                expr = SExp::App {
                    arg: Box::new(expr),
                    func: Box::new(right),
                    piped: true,
                };
            }
            Ok(expr)
        }
        fn as_exp(parser: &mut TermParser) -> Result<SExp, ParseError> {
            piped(parser)
        }
        fn equal_exp(parser: &mut TermParser) -> Result<SExp, ParseError> {
            let left_exp = as_exp(parser)?;
            if parser.bump_if_token(Token::Equal) {
                let right_exp = as_exp(parser)?;
                Ok(SExp::Equal {
                    left: Box::new(left_exp),
                    right: Box::new(right_exp),
                })
            } else {
                Ok(left_exp)
            }
        }

        equal_exp(self)
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
    fn parse_annotate_comma_separated(&mut self) -> Result<Vec<RightBind>, ParseError> {
        let mut annotations = Vec::new();
        while self.peek().is_some() && self.peek() != Some(&Token::RParen) {
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

    fn error(&self, msg: &str) -> ParseError {
        let span = self.span_at(self.pos);
        ParseError {
            msg: msg.into(),
            start: span.start,
            end: span.end,
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
                | Token::Hole
                | Token::UnspecifiedVar(_)
                | Token::MacroVar(_)
                | Token::LParen
                | Token::MathLParen,
            ) => true,
            Some(Token::KeyWord(k)) => {
                SORT_KEYWORDS.contains(k)
                    || EXPRESSION_ATOM_KEYWORDS.contains(k)
                    || PROOF_TERM_KEYWORDS.contains(k)
            }
            _ => false,
        }
    }

    fn parse_binding(&mut self, open: Token<'a>, close: Token<'a>) -> Result<Bind, ParseError> {
        self.expect_token(open)?;
        let (vars, ty) = self.parse_annotate()?;
        let bind = if self.bump_if_keyword(r"\where") {
            let [var] = vars.as_slice() else {
                return Err(self.error("expected single identifier in refinement binder"));
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
                computation: Box::new(self.field_access()?),
            }),
            Token::KeyWord("\\force") => Ok(SExp::Force {
                value: Box::new(self.field_access()?),
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
                        return Err(self.error("Program lambda requires a plain value binder"));
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
                    self.error("refinement binders are not allowed in inductive signatures")
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

    fn parse_sexp(&mut self) -> Result<SExp, ParseError> {
        if matches!(self.peek(), Some(Token::KeyWord(r"\let" | r"\bind"))) {
            return self.parse_program_binding();
        }
        let left = self.parse_combined()?;
        if self.bump_if_token(Token::Arrow) {
            Ok(SExp::Prod {
                bind: Bind::Named(RightBind {
                    vars: Vec::new(),
                    ty: Box::new(left),
                }),
                body: Box::new(self.parse_sexp()?),
            })
        } else if self.bump_if_token(Token::ComputationArrow) {
            Ok(SExp::ComputationFunction {
                domain: Box::new(left),
                codomain: Box::new(self.parse_sexp()?),
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
                return Err(self.error("rest splices are only valid in macro templates"));
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
            let exp = self.parse_atom()?;
            if self.allow_macro_parameters
                && let SExp::AccessPath {
                    access: LocalAccess::Current { access },
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
            msg: "expected macro expression".into(),
            start: self.span_at(self.pos).start,
            end: self.span_at(self.pos).end,
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

    fn complete(input: &str) -> SExp {
        let tokens = lex_all(input).unwrap();
        let mut parser = TermParser::new(&tokens);
        let exp = parser.parse_sexp().unwrap();
        assert_eq!(parser.pos, tokens.len(), "unconsumed input: {input}");
        assert_eq!(parser.consumed, tokens.len());
        exp
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
                r"\match x \in T \with { | ctor => ".repeat(depth),
                "; }".repeat(depth)
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
    fn records_remain_unclassified_and_case_has_an_unambiguous_body() {
        let SExp::RecordTypeCtor { fields, .. } =
            complete(r"\record Future[A] { suspended := \thunk (\return x) }")
        else {
            panic!()
        };
        assert!(matches!(fields[0].1, SExp::Thunk { .. }));
        complete(r"\record Empty {}");
        complete(r"\elim x \in T \return R { | ctor => branch; }");
        let SExp::ProgramCase { branches, .. } =
            complete(r"\match x \in T \with { | ctor a b => \return a; }")
        else {
            panic!()
        };
        assert_eq!(branches[0].1.len(), 2);
        complete(
            r"\match x \in T \with { | empty => x | f; | ctor a => \bind y: A <- f a \in g y; }",
        );
    }

    #[test]
    fn macro_groups_and_embedded_expressions_are_distinct() {
        let SExp::NamedMacro { tokens, .. } = complete(r"m!{(x) { f (g x) }}") else {
            panic!()
        };
        assert!(matches!(&tokens[0], MacroExp::Seq(xs) if xs.len() == 1));
        assert!(matches!(&tokens[1], MacroExp::RawExp(SExp::App { .. })));
        complete(r"$( (a + b) + { f (g x) } $)");
    }

    #[test]
    fn malformed_productions_commit_at_the_failing_token() {
        for (input, bad) in [
            (r"f[x, ;]", ";"),
            (r"\fun (x: A \where P \as ) => x", ")"),
            (r"\record T { field := ; }", ";"),
            (r"\match x \in T \with { | ctor x => ; }", ";"),
            (r"\match x \in T { | ctor => c; }", "{"),
            (r"\match x \in T \with { | ctor => c }", "}"),
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
        fn print_and_unwrap_annotate(input: &'static str) {
            let lex = &lex_all(input).expect("lexing failed for annotate test");
            let mut parser = TermParser::new(lex);
            let result = parser.parse_annotate();
            match result {
                Ok((var, ty)) => {
                    println!("Parsed SExp: {:?} => {:?}: {:?}", input, var, ty);
                }
                Err(err) => {
                    panic!("Error: {:?}", err);
                }
            }
        }
        print_and_unwrap_annotate(r"x: X");
        print_and_unwrap_annotate(r"y: (A -> B)");
        print_and_unwrap_annotate(r"x: X Y | h");
        print_and_unwrap_annotate(r"x, y, z: X -> Y");
    }
    #[test]
    fn parse_rightbinds_test() {
        fn print_and_unwrap_rightbinds(input: &'static str) {
            let lex = &lex_all(input).expect("lexing failed for rightbinds test");
            let mut parser = TermParser::new(lex);
            let binds = parser.parse_annotate_comma_separated();
            println!("Parsed SExp: {:?} => {:?}", input, binds);
        }
        print_and_unwrap_rightbinds(r"x: X");
        print_and_unwrap_rightbinds(r"x: X, y: Y");
        print_and_unwrap_rightbinds(r"x, y: X -> Y, z: Z");

        // use simple_binds_paren
        fn print_and_unwrap_simplebinds_paren(input: &'static str) {
            let lex = &lex_all(input).expect("lexing failed for simplebinds paren test");
            let mut parser = TermParser::new(lex);
            let result = parser.parse_simple_binds_paren();
            match result {
                Ok(binds) => {
                    println!("Parsed SExp: {:?} => {:?}", input, binds);
                }
                Err(err) => {
                    panic!("Error: {:?}", err);
                }
            }
        }
        print_and_unwrap_simplebinds_paren(r"(x: X)");
        print_and_unwrap_simplebinds_paren(r"(x: X, y: Y)");
        print_and_unwrap_simplebinds_paren(r"(x, y: X -> Y, z: Z)");
    }

    #[test]
    fn parse_bind_test() {
        fn print_and_unwrap_subsetbind(input: &'static str) {
            let lex = &lex_all(input).expect("lexing failed for complex bind test");
            let mut parser = TermParser::new(lex);
            let result = parser.parse_binding(Token::LParen, Token::RParen);
            match result {
                Ok(bind) => {
                    println!("Parsed SExp: {:?} => {:?}", input, bind);
                }
                Err(err) => {
                    panic!("Error: {:?}", err);
                }
            }
        }
        print_and_unwrap_subsetbind(r"(x: X \where P)");
        print_and_unwrap_subsetbind(r"(x: X \where p1 p2)");
        print_and_unwrap_subsetbind(r"(x: X \where p1 p2 \as h)");
    }
    #[test]
    fn parse_combined_test() {
        fn print_and_unwrap_combined(input: &'static str) {
            let lex = &lex_all(input).expect("lexing failed for combined test");
            let mut parser = TermParser::new(lex);
            let result = parser.parse_combined();
            match result {
                Ok(atomlike) => {
                    println!("Parsed SExp: {:?} => {:?}\n\n", input, atomlike);
                }
                Err(err) => {
                    panic!(" {:?}", err);
                }
            }
        }
        print_and_unwrap_combined(r"x");
        print_and_unwrap_combined(r"x y");
        print_and_unwrap_combined(r"x | y");
        print_and_unwrap_combined(r"\subsetinto(A, X, x, p)");
        print_and_unwrap_combined(r"x = y");
        print_and_unwrap_combined(r"\subsetinto(A, X, x, p) | z = h");
    }
    #[test]
    fn parse_nosubset_arrow_test() {
        fn print_and_unwrap_nosubset(input: &'static str) {
            let lex = &lex_all(input).expect("lexing failed for nosubset arrow test");
            let mut parser = TermParser::new(lex);
            let result = parser.parse_arrow_nosubset();
            match result {
                Ok((binds, body)) => {
                    println!("Parsed SExp: {:?} => {:?} -> {:?}", input, binds, body);
                }
                Err(err) => {
                    panic!("Error: {:?}", err);
                }
            }
        }
        print_and_unwrap_nosubset(r"\forall (x: X) -> Y");
        print_and_unwrap_nosubset(r"\forall (x: X) -> \forall (y: Y) -> Z");
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
        print_and_unwrap(r"\record x { a := A, b := B }");
        print_and_unwrap(r"\record x.y { a := A, b := B }");
        print_and_unwrap(r"\record x.y[ A, B ] { a := A, b := B }");
        print_and_unwrap(r"x::y"); // x::y::z is "combined expression" ... not tested here
        print_and_unwrap(r"List[Nat]::Nil");
        print_and_unwrap(r"list.List[Nat]::Nil");
        print_and_unwrap(r"\record Group[Nat] { mul := x, e := y }");
        print_and_unwrap(r"$( x + y $)");
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
        print_and_unwrap(r"x | y");
        print_and_unwrap(r"x | f");
        print_and_unwrap(r"x x | y u | f g");
        print_and_unwrap(r"\forall (x: X) -> Y");
        print_and_unwrap(r"\fun (x: X) => y");
        print_and_unwrap(r"\forall (x: X) -> \fun (_: Y) => z");
        print_and_unwrap(r"X -> Z");
        print_and_unwrap(r"x y z -> Y");
        print_and_unwrap(r"(x y) -> Y");
        print_and_unwrap(r"x y | z -> Y");
        print_and_unwrap(r"\forall (x: X) -> \forall (y: Y) -> Z");
        print_and_unwrap(r"\forall (x: X \where P) -> \forall (y: Y) -> Z");
        print_and_unwrap(r"\forall (x: X \where P \as h) -> \forall (y: Y) -> Z");
        print_and_unwrap(r"\forall (x: P y | F \where (u | a) | b \as h) -> \forall (y: Y) -> Z");
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
        print_and_unwrap(r"\record x { a := A, b := B }");
        print_and_unwrap(r"\record x.y { a := A, b := B }");
        print_and_unwrap(r"\record x.y[ A, B ] { a := A, b := B }");
        print_and_unwrap(r"x::y");
        print_and_unwrap(r"x::y::z");
        print_and_unwrap(r"List[Nat]::Nil");
        print_and_unwrap(r"list.List[Nat]::Nil");
        print_and_unwrap(r"\record Group[Nat] { mul := x, e := y }");
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
        print_and_unwrap(r"x $( y + z $) l");
        print_and_unwrap(r"x mymacro!{ a + b c } l");
        print_and_unwrap(r"x::y::z");
        print_and_unwrap(r"\subsetinto(A, X, x, p)");
        print_and_unwrap(r"\exact(x, X)");
        print_and_unwrap(r"\refl(x)");
        print_and_unwrap(r"\idelim(a = b \with x: X => P x) \by (pa, eq)");
        print_and_unwrap(r"\axiom:setext(A, B, ab, ba)");
        print_and_unwrap(r"\axiom:funext(f, g, pointwise)");
        print_and_unwrap(r"\axiom:classicalIndefiniteChoice(X, Y, inhabited)");
        print_and_unwrap(r"\take (x: X) => f x \by (existsX, uniqueF)");
        print_and_unwrap(r"\take (x: X) => P \by (existsX)");
        print_and_unwrap(r"x = y");
        print_and_unwrap(r"\subsetinto(A, X, x, p) | z = h");
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
        // parse an expression with extra tokens remaining
        fn parse_middle(input: &str) {
            let tok = lex_all(input).unwrap();
            let mut parser = TermParser::new(&tok);
            let result = parser.parse_sexp();
            match result {
                Ok(exp) => {
                    println!("Parsed SExp: {:?} => {:?}", input, exp);
                    if parser.pos < parser.tokens.len() {
                        let extra = &parser.tokens[parser.pos];
                        println!(
                            "  Extra tokens after expression starting at {}..{}: {:?}",
                            extra.start, extra.end, extra.kind
                        );
                    } else {
                        println!("  No extra tokens remaining.");
                    }
                }
                Err(err) => {
                    panic!("Error: {:?}", err);
                }
            }
        }
        parse_middle(r"x ;");
        parse_middle(r"x {");
        let tokens = lex_all(r"x (( y: Y)").unwrap();
        assert!(TermParser::new(&tokens).parse_sexp().is_err());
        parse_middle(r"x::y x::y;");
    }
}
