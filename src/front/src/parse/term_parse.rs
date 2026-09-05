use super::{
    EXPRESSION_ATOM_KEYWORDS, PROOF_TERM_KEYWORDS, ParseError, SORT_KEYWORDS, SpannedToken, Token,
};
use crate::syntax::*;

pub struct TermParser<'a> {
    tokens: &'a [SpannedToken<'a>],
    pos: usize,
    allow_macro_parameters: bool,
}

impl<'a> TermParser<'a> {
    pub fn new(tokens: &'a [SpannedToken<'a>]) -> Self {
        Self {
            tokens,
            pos: 0,
            allow_macro_parameters: false,
        }
    }

    pub fn new_macro_template(tokens: &'a [SpannedToken<'a>]) -> Self {
        Self {
            tokens,
            pos: 0,
            allow_macro_parameters: true,
        }
    }

    fn peek(&self) -> Option<&Token<'a>> {
        self.tokens.get(self.pos).map(|t| &t.kind)
    }

    fn next(&mut self) -> Option<&SpannedToken<'a>> {
        let t = self.tokens.get(self.pos);
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    fn bump_if_token(&mut self, expect: &Token<'a>) -> bool
    where
        Token<'a>: PartialEq,
    {
        if let Some(tok) = self.peek()
            && tok == expect
        {
            self.pos += 1;
            return true;
        }
        false
    }

    fn bump_if_keyword(&mut self, kw: &str) -> bool {
        if let Some(Token::KeyWord(s)) = self.peek()
            && *s == kw
        {
            self.pos += 1;
            return true;
        }
        false
    }

    fn expect_token(&mut self, expect: Token<'a>) -> Result<SpannedToken<'a>, ParseError> {
        if let Some(t) = self.tokens.get(self.pos) {
            if t.kind == expect {
                self.pos += 1;
                Ok(t.clone())
            } else {
                Err(ParseError {
                    msg: format!("expected {:?}, found {:?}", expect, t.kind),
                    start: t.start,
                    end: t.end,
                })
            }
        } else {
            Err(ParseError::eof_error(&format!("{:?}", expect)))
        }
    }

    fn expect_keyword<'b>(&mut self, kw: &'b str) -> Result<&'a str, ParseError>
    where
        'b: 'a,
    {
        match self.next() {
            Some(t) => match &t.kind {
                Token::KeyWord(name) if *name == kw => Ok(*name),
                other => Err(ParseError {
                    msg: format!("expected keyword {kw}, found {:?}", other),
                    start: t.start,
                    end: t.end,
                }),
            },
            None => Err(ParseError::eof_error("keyword")),
        }
    }

    fn expect_ident(&mut self) -> Result<Identifier, ParseError> {
        match self.next() {
            Some(t) => match &t.kind {
                Token::Ident(name) => Ok(Identifier((*name).to_string())),
                other => Err(ParseError {
                    msg: format!("expected identifier, found {:?}", other),
                    start: t.start,
                    end: t.end,
                }),
            },
            None => Err(ParseError::eof_error("identifier")),
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
            None => Err(ParseError::eof_error("number")),
        }
    }

    fn expect_othersymbol(&mut self) -> Result<&'a str, ParseError> {
        match self.next() {
            Some(t) => match &t.kind {
                Token::MacroToken(sym_str) => Ok(sym_str),
                other => Err(ParseError {
                    msg: format!("expected other symbol, found {:?}", other),
                    start: t.start,
                    end: t.end,
                }),
            },
            None => Err(ParseError::eof_error("other symbol")),
        }
    }

    // Try to parse with the given parsing function.
    // ... rollbacks on failure.
    fn try_parse<T, F>(&mut self, parse_fn: F) -> Result<Option<T>, ParseError>
    where
        F: Fn(&mut Self) -> Result<T, ParseError>,
    {
        let save_pos = self.pos;
        match parse_fn(self) {
            Ok(result) => Ok(Some(result)),
            Err(_) => {
                self.pos = save_pos; // rollback
                Ok(None)
            }
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

    // Try to parse a parenthesized number (e.g., "(0)").
    fn parse_number_paren(&mut self) -> Result<usize, ParseError> {
        self.expect_token(Token::LParen)?;
        let number = self.expect_number()?;
        self.expect_token(Token::RParen)?;

        Ok(number)
    }

    // Parse a sort expression.
    // \Prop | \PropKind | \Set ( "(" <number> ")" )? | \SetKind ( "(" <number> ")" )?
    fn parse_sort(&mut self) -> Result<kernel::sort::Sort, ParseError> {
        if self.bump_if_keyword("\\Prop") {
            return Ok(kernel::sort::Sort::Prop);
        }
        if self.bump_if_keyword("\\PropKind") {
            return Ok(kernel::sort::Sort::PropKind);
        }
        if self.bump_if_keyword("\\Set") {
            let number = self
                .try_parse(|parser| parser.parse_number_paren())?
                .unwrap_or_default();

            return Ok(kernel::sort::Sort::Set(number));
        }
        if self.bump_if_keyword("\\SetKind") {
            let number = self
                .try_parse(|parser| parser.parse_number_paren())?
                .unwrap_or_default();
            return Ok(kernel::sort::Sort::SetKind(number));
        }
        Err(ParseError {
            msg: "expected sort keyword".into(),
            start: self.pos,
            end: self.pos,
        })
    }

    fn parse_keyword_head_atom(&mut self) -> Result<SExp, ParseError> {
        if self.bump_if_keyword("\\Type") || self.bump_if_keyword("\\VType") {
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
        if self.bump_if_keyword("\\CFun") {
            return self.parse_parenthesized(|parser| {
                let domain = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let codomain = parser.parse_sexp()?;
                Ok(SExp::ComputationFunction {
                    domain: Box::new(domain),
                    codomain: Box::new(codomain),
                })
            });
        }
        if self.bump_if_keyword("\\thunk") {
            return self.parse_parenthesized(|parser| {
                parser.parse_sexp().map(|computation| SExp::Thunk {
                    computation: Box::new(computation),
                })
            });
        }
        if self.bump_if_keyword("\\return") {
            return self.parse_parenthesized(|parser| {
                parser.parse_sexp().map(|value| SExp::Return {
                    value: Box::new(value),
                })
            });
        }
        if self.bump_if_keyword("\\force") {
            return self.parse_parenthesized(|parser| {
                parser.parse_sexp().map(|value| SExp::Force {
                    value: Box::new(value),
                })
            });
        }
        if self.bump_if_keyword("\\clam") {
            return self.parse_parenthesized(|parser| {
                let var = parser.expect_ident()?;
                parser.expect_token(Token::Comma)?;
                let value_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let body = parser.parse_sexp()?;
                Ok(SExp::ComputationLam {
                    var,
                    value_ty: Box::new(value_ty),
                    body: Box::new(body),
                })
            });
        }
        if self.bump_if_keyword("\\capp") {
            return self.parse_parenthesized(|parser| {
                let computation = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let value = parser.parse_sexp()?;
                Ok(SExp::ComputationApp {
                    computation: Box::new(computation),
                    value: Box::new(value),
                })
            });
        }
        if self.bump_if_keyword("\\sequence") {
            return self.parse_parenthesized(|parser| {
                let computation = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let var = parser.expect_ident()?;
                parser.expect_token(Token::Comma)?;
                let value_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let body = parser.parse_sexp()?;
                Ok(SExp::Sequence {
                    computation: Box::new(computation),
                    var,
                    value_ty: Box::new(value_ty),
                    body: Box::new(body),
                })
            });
        }
        if self.bump_if_keyword("\\vlet") {
            return self.parse_parenthesized(|parser| {
                let var = parser.expect_ident()?;
                parser.expect_token(Token::Comma)?;
                let value = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let body = parser.parse_sexp()?;
                Ok(SExp::ValueLet {
                    var,
                    value: Box::new(value),
                    body: Box::new(body),
                })
            });
        }
        if self.bump_if_keyword("\\vcase") {
            self.expect_token(Token::LParen)?;
            let path = self.parse_access_path()?;
            self.expect_token(Token::Comma)?;
            let scrutinee = self.parse_sexp()?;
            self.expect_token(Token::RParen)?;
            self.expect_token(Token::LBrace)?;
            let mut branches = Vec::new();
            while !self.bump_if_token(&Token::RBrace) {
                self.expect_token(Token::Pipe)?;
                let constructor = self.expect_ident()?;
                self.expect_token(Token::LParen)?;
                let mut binders = Vec::new();
                if !self.bump_if_token(&Token::RParen) {
                    loop {
                        binders.push(self.expect_ident()?);
                        if self.bump_if_token(&Token::RParen) {
                            break;
                        }
                        self.expect_token(Token::Comma)?;
                    }
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
        if self.bump_if_keyword("\\RunStep") {
            return self.parse_parenthesized(|parser| {
                let state_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let result_ty = parser.parse_sexp()?;
                Ok(SExp::RunStep {
                    state_ty: Box::new(state_ty),
                    result_ty: Box::new(result_ty),
                })
            });
        }
        if self.bump_if_keyword("\\continue") {
            return self.parse_parenthesized(|parser| {
                let state_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let result_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let next = parser.parse_sexp()?;
                Ok(SExp::Continue {
                    state_ty: Box::new(state_ty),
                    result_ty: Box::new(result_ty),
                    next: Box::new(next),
                })
            });
        }
        if self.bump_if_keyword("\\finish") {
            return self.parse_parenthesized(|parser| {
                let state_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let result_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let output = parser.parse_sexp()?;
                Ok(SExp::Finish {
                    state_ty: Box::new(state_ty),
                    result_ty: Box::new(result_ty),
                    output: Box::new(output),
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
        if self.bump_if_keyword("\\RfType") {
            return Err(ParseError {
                msg: "\\RfType was removed: reflection is now a meta-level map".into(),
                start: self.pos.saturating_sub(1),
                end: self.pos,
            });
        }
        if self.bump_if_keyword("\\RfTerm") {
            return Err(ParseError {
                msg: "\\RfTerm was removed: reflection is now a meta-level map".into(),
                start: self.pos.saturating_sub(1),
                end: self.pos,
            });
        }
        if self.bump_if_keyword("\\run") {
            return self.parse_parenthesized(|parser| {
                let state_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let result_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let step = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let initial = parser.parse_sexp()?;
                if parser.bump_if_token(&Token::Comma) {
                    return Err(ParseError {
                        msg: "five-argument \\run was removed; put the Acc witness in a trailing proof block".into(),
                        start: parser.pos,
                        end: parser.pos,
                    });
                }
                Ok(SExp::Run {
                    state_ty: Box::new(state_ty),
                    result_ty: Box::new(result_ty),
                    step: Box::new(step),
                    initial: Box::new(initial),
                })
            });
        }
        if self.bump_if_keyword("\\runCase") {
            return self.parse_parenthesized(|parser| {
                let state_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let result_ty = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let step = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let initial = parser.parse_sexp()?;
                parser.expect_token(Token::Comma)?;
                let transition = parser.parse_sexp()?;
                if parser.bump_if_token(&Token::Comma) {
                    return Err(ParseError {
                        msg: "legacy annotated \\runCase was removed; use a proof block".into(),
                        start: parser.pos,
                        end: parser.pos,
                    });
                }
                Ok(SExp::RunCase {
                    state_ty: Box::new(state_ty),
                    result_ty: Box::new(result_ty),
                    step: Box::new(step),
                    initial: Box::new(initial),
                    transition: Box::new(transition),
                })
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
        if self.bump_if_keyword("\\Proof") {
            let proposition = self.parse_atom()?;
            return Ok(SExp::Proof {
                proposition: Box::new(proposition),
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
            // "\elim" <elim: SExp> "\in" <path: Path> "\\return" <return_type: SExp>
            let elim = self.parse_sexp()?;
            self.expect_keyword("\\in")?; // expect '\in'
            let path = self.parse_access_path()?;
            self.expect_keyword("\\return")?; // expect '\\return'
            let return_type = self.parse_sexp()?;

            // body of case branches
            let mut cases = Vec::new();
            self.expect_token(Token::LBrace)?; // expect '{'
            // loop until '}'
            while !self.bump_if_token(&Token::RBrace) {
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
            // "\prec" "(" <sort: Sort> "," <path: AccessPath> <parameter>? ")"
            self.expect_token(Token::LParen)?;
            let sort = self.parse_sort()?;
            self.expect_token(Token::Comma)?;
            let path = self.parse_access_path()?;
            let parameters = self
                .try_parse(|parser| parser.parse_parameter())?
                .unwrap_or_default();

            self.expect_token(Token::RParen)?;

            return Ok(SExp::IndElimPrim {
                path,
                parameters,
                sort,
            });
        }
        // "\exists" <binding>
        if self.bump_if_keyword("\\exists") {
            let bind = self.parse_left_arrow_head()?;
            return Ok(SExp::Exists { bind });
        }
        // "\take" <binding> "=>" <body>
        if self.bump_if_keyword("\\take") {
            let bind = self.parse_left_arrow_head()?;
            self.expect_token(Token::DoubleArrow)?; // expect '=>'
            let body = self.parse_sexp()?;
            self.expect_keyword("\\by")?;
            self.expect_token(Token::LParen)?;
            let existence = self.parse_sexp()?;
            let uniqueness = self
                .bump_if_token(&Token::Comma)
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
            start: self.pos,
            end: self.pos,
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
                    start: self.pos,
                    end: self.pos,
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

        // \\idelim "(" <left: SExp> "=" <right: SExp> "\with" <var: Ident> ":" <ty: SExp> "=>" <predicate: SExp> ")"
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
            start: self.pos,
            end: self.pos,
        })
    }

    fn parse_block(&mut self) -> Result<Block, ParseError> {
        let mut statements = Vec::new();

        loop {
            if self.bump_if_keyword("\\fix") {
                // "\fix" ("(" RightBind ")" ",")* ";"
                let mut binds: Vec<RightBind> = Vec::new();
                while let Ok(bind) = self.parse_simple_binds_paren() {
                    binds.extend(bind);
                    if !self.bump_if_token(&Token::Comma) {
                        break;
                    }
                }
                self.expect_token(Token::Semicolon)?; // expect ';'
                statements.push(Statement::Fix(binds));
                continue;
            }

            if self.bump_if_keyword("\\let") {
                // "\let" <var: Ident> ":" <ty: SExp> ":=" <body: SExp> ";"
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
                // "\take" <bind: Bind> "\by" "(" proof ("," proof)? ")" ";"
                let bind = self.parse_left_arrow_head()?;
                self.expect_keyword("\\by")?;
                self.expect_token(Token::LParen)?;
                let existence = self.parse_sexp()?;
                let uniqueness = self
                    .bump_if_token(&Token::Comma)
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
                // "\return" <exp: SExp> ";"
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
            start: self.pos,
            end: self.pos,
        })
    }

    // general parameter passing expression is here
    // "[" (SExp ("," SExp)*)? "]"
    fn parse_parameter(&mut self) -> Result<Vec<SExp>, ParseError> {
        self.expect_token(Token::LBracket)?; // expect '['
        let mut params = Vec::new();
        while let Ok(param) = self.parse_sexp() {
            params.push(param);
            if !self.bump_if_token(&Token::Comma) {
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
        if self.bump_if_token(&Token::Period) {
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
        while !self.bump_if_token(&Token::RBrace) {
            let field_name = self.expect_ident()?;
            self.expect_token(Token::Assign)?;
            let field_exp = self.parse_sexp()?;
            fields.push((field_name, field_exp));

            if !self.bump_if_token(&Token::Comma) {
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
                let parameters = self
                    .try_parse(|parser| parser.parse_parameter())?
                    .unwrap_or_default();

                // field access case or record construction case
                if self.bump_if_token(&Token::DoubleColon) {
                    // field access case
                    let field_name = self.expect_ident()?;
                    return Ok(SExp::AssociatedAccess {
                        base: Box::new(SExp::AccessPath { access, parameters }),
                        field: field_name,
                    });
                }

                match self.try_parse(|parser| parser.parse_record_body())? {
                    Some(fields) => {
                        // record construction
                        Ok(SExp::RecordTypeCtor {
                            access,
                            parameters,
                            fields,
                        })
                    }
                    None => Ok(SExp::AccessPath { access, parameters }),
                }
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
                start: self.pos,
                end: self.pos,
            }),
            _ => Err(ParseError {
                msg: "expected atom".into(),
                start: self.pos,
                end: self.pos,
            }),
        }
    }

    // parse field access
    // <atom>("::" Ident)?
    // this includes atom parsing
    fn field_access(&mut self) -> Result<SExp, ParseError> {
        let mut expr = self.parse_atom()?;
        while self.bump_if_token(&Token::DoubleColon) {
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

        while let Some(try_exp) = self.try_parse(|parser| parser.field_access())? {
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

            while parser.bump_if_token(&Token::Pipe) {
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
            if parser.bump_if_token(&Token::Equal) {
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

    // Try to parse an annotation
    // Ident ("," Ident)* ":" SExp
    fn parse_annotate(&mut self) -> Result<(Vec<Identifier>, SExp), ParseError> {
        // 1. parse identifiers separated by commas
        let mut vars = vec![];
        vars.push(self.expect_binder_ident()?);

        while self.bump_if_token(&Token::Comma) {
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
        let mut annotations = vec![];

        // this implementation allows trailing commas
        while let Some((vars, ty)) = self.try_parse(|parser| parser.parse_annotate())? {
            annotations.push(RightBind {
                vars,
                ty: Box::new(ty),
            });

            // allow trailing comma
            self.bump_if_token(&Token::Comma);
        }

        Ok(annotations)
    }

    // "(" <multiple annotations comma separated> ")"
    fn parse_simple_binds_paren(&mut self) -> Result<Vec<RightBind>, ParseError> {
        self.parse_parenthesized(|parser| parser.parse_annotate_comma_separated())
    }

    pub fn parse_simple_binds_advanced(&mut self) -> Result<(Vec<RightBind>, usize), ParseError> {
        let binds = self.parse_simple_binds_paren()?;
        let advanced_pos = self.pos;
        Ok((binds, advanced_pos))
    }

    // subset like bind
    // "(" "(" Ident ":" SExp ")" "|" SExp ")"
    // "(" "(" Ident ":" SExp ")" "|" Ident ":" SExp ")"
    // rollback is handled by caller
    fn parse_subsetbind(&mut self) -> Result<Bind, ParseError> {
        // check "(" "(" <annotate> ... otherwise error

        self.expect_token(Token::LParen)?; // expect '('
        self.expect_token(Token::LParen)?; // expect '('

        let (first_var, first_ty) = self.parse_annotate()?;

        let [var] = first_var.as_slice() else {
            return Err(ParseError {
                msg: "expected single identifier in subset bind".into(),
                start: self.pos,
                end: self.pos,
            });
        };

        // there is "(" "(" <annot> ")" ... now ")" and "|" expected
        self.expect_token(Token::RParen)?; // expect ')'
        self.expect_token(Token::Pipe)?; // expect '|'

        // try to parse proof style first (annotation)
        // fail => it is rollbacked to after '|'
        if let Some((vars, exp)) = self.try_parse(|parser| parser.parse_annotate())? {
            let [proof_var] = vars.as_slice() else {
                return Err(ParseError {
                    msg: "expected single identifier in subset bind proof var".into(),
                    start: self.pos,
                    end: self.pos,
                });
            };
            self.expect_token(Token::RParen)?; // expect ')'
            return Ok(Bind::SubsetWithProof {
                var: var.clone(),
                ty: Box::new(first_ty),
                predicate: Box::new(exp),
                proof_var: proof_var.clone(),
            });
        }
        // usual subset bind => parse exp
        let predicate = self.parse_sexp()?;
        self.expect_token(Token::RParen)?; // expect ')'
        Ok(Bind::Subset {
            var: var.clone(),
            ty: Box::new(first_ty),
            predicate: Box::new(predicate),
        })
    }

    // parse an arrow expression
    // e.g. `bind -> x` or `bind => x` or just piped atom sequence
    fn parse_arrow_expr(&mut self) -> Result<SExp, ParseError> {
        let left_head = self.parse_left_arrow_head()?;

        if self.bump_if_token(&Token::Arrow) {
            let right = self.parse_sexp()?;
            return Ok(SExp::Prod {
                bind: left_head,
                body: Box::new(right),
            });
        }

        if self.bump_if_token(&Token::DoubleArrow) {
            let right = self.parse_sexp()?;
            return Ok(SExp::Lam {
                bind: left_head,
                body: Box::new(right),
            });
        }

        Err(ParseError {
            msg: "expected '->' or '=>' after bind".into(),
            start: self.pos,
            end: self.pos,
        })
    }

    // parse arrow expression without subset-style binds on the right-hand side
    // e.g. ([<rightbind> | <sexp>] "->")* <sexp>
    fn parse_arrow_nosubset(&mut self) -> Result<(Vec<RightBind>, SExp), ParseError> {
        let mut binds = vec![];
        // parse right binds until fail
        loop {
            let bind = match self.try_parse(|parser| parser.parse_simple_binds_paren())? {
                Some(b) => b,
                None => {
                    let maybe_body = self.parse_combined()?;
                    if self.bump_if_token(&Token::Arrow) {
                        // continue parsing binds
                        binds.push(RightBind {
                            vars: vec![],
                            ty: Box::new(maybe_body),
                        });
                        continue;
                    } else {
                        return Ok((binds, maybe_body));
                    }
                }
            };
            binds.extend(bind);
            self.expect_token(Token::Arrow)?; // expect '->' after each bind
        }
    }

    pub fn parse_arrow_nosubset_advanced(
        &mut self,
    ) -> Result<(Vec<RightBind>, SExp, usize), ParseError> {
        let (binds, body) = self.parse_arrow_nosubset()?;
        let advanced_pos = self.pos;
        Ok((binds, body, advanced_pos))
    }

    // parse the left-hand side of an arrow expression
    // may be a bind or a simple expression or a parenthesized expression
    // e.g. `x y -> z`, `(x y) -> z`, `(x: y) -> z`, `((x: y) | P) -> z`
    fn parse_left_arrow_head(&mut self) -> Result<Bind, ParseError> {
        // 1. try to parse susbet bind
        if let Some(bind) = self.try_parse(|parser| parser.parse_subsetbind())? {
            return Ok(bind);
        }

        // 2. try to parse named bind
        if let Some(rightbinds) = self.try_parse(|parser| parser.parse_simple_binds_paren())? {
            let [rightbind] = rightbinds.as_slice() else {
                return Err(ParseError {
                    msg: "expected single right bind in named bind".into(),
                    start: self.pos,
                    end: self.pos,
                });
            };
            return Ok(Bind::Named(rightbind.clone()));
        }

        // 3. otherwise, parse simple expression as a bind
        let expr = self.parse_combined()?;
        Ok(Bind::Named(RightBind {
            vars: vec![],
            ty: expr.into(),
        }))
    }

    fn parse_sexp_withgoals(&mut self) -> Result<SExp, ParseError> {
        self.try_parse(|p| p.parse_arrow_expr())?
            .map_or_else(|| self.parse_combined(), Ok)
    }

    fn parse_sexp(&mut self) -> Result<SExp, ParseError> {
        self.parse_sexp_withgoals()
    }

    pub fn parse_sexp_advanced(&mut self) -> Result<(SExp, usize), ParseError> {
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
        // 1, challenge atom
        let save = self.pos;
        if let Ok(atom) = self.parse_atom() {
            return Ok(MacroExp::Exp(atom));
        }
        self.pos = save;
        // 2. challenge one macro token
        // OthetSymbolStart or KeyWord which is not contained in *_KEYWORDS
        if let Some(Token::MacroToken(_)) = self.peek() {
            let sym = self.expect_othersymbol()?;
            return Ok(MacroExp::Tok(MacroToken(sym.to_string())));
        }
        if let Some(Token::QuotedMacroToken(value)) = self.peek() {
            let value = value[1..value.len() - 1].to_string();
            self.next();
            return Ok(MacroExp::Quoted(value));
        }
        // 3. Parended sequence of macro tokens
        if self.bump_if_token(&Token::LParen) {
            let mut exps = Vec::new();
            while !self.bump_if_token(&Token::RParen) {
                let exp = self.parse_one_macro()?;
                exps.push(exp);
            }
            return Ok(MacroExp::Seq(exps));
        }
        Err(ParseError {
            msg: "expected macro expression".into(),
            start: self.pos,
            end: self.pos,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::lex_all;
    use super::*;
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
            let result = parser.parse_annotate_comma_separated();
            match result {
                Ok(binds) => {
                    println!("Parsed SExp: {:?} => {:?}", input, binds);
                }
                Err(err) => {
                    panic!("Error: {:?}", err);
                }
            }
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
            let result = parser.parse_subsetbind();
            match result {
                Ok(bind) => {
                    println!("Parsed SExp: {:?} => {:?}", input, bind);
                }
                Err(err) => {
                    panic!("Error: {:?}", err);
                }
            }
        }
        print_and_unwrap_subsetbind(r"((x: X) | P)");
        print_and_unwrap_subsetbind(r"((x: X) | p1 p2)");
        print_and_unwrap_subsetbind(r"((x: X) | h: p1 p2)");
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
        print_and_unwrap_nosubset(r"(x: X) -> Y");
        print_and_unwrap_nosubset(r"(x: X) -> (y: Y) -> Z");
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
        print_and_unwrap(r"x { a := A, b := B }");
        print_and_unwrap(r"x.y { a := A, b := B }");
        print_and_unwrap(r"x.y[ A, B ] { a := A, b := B }");
        print_and_unwrap(r"x::y"); // x::y::z is "combined expression" ... not tested here
        print_and_unwrap(r"List[Nat]::Nil");
        print_and_unwrap(r"list.List[Nat]::Nil");
        print_and_unwrap(r"Group[Nat] { mul := x, e := y }");
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
        print_and_unwrap(r"(x: X) -> Y");
        print_and_unwrap(r"(x: X) => y");
        print_and_unwrap(r"(x: X) -> Y => z");
        print_and_unwrap(r"X -> Z");
        print_and_unwrap(r"x y z -> Y");
        print_and_unwrap(r"(x y) -> Y");
        print_and_unwrap(r"x y | z -> Y");
        print_and_unwrap(r"(x: X) -> (y: Y) -> Z");
        print_and_unwrap(r"((x: X) | P) -> (y: Y) -> Z");
        print_and_unwrap(r"((x: X) | h: P) -> (y: Y) -> Z");
        print_and_unwrap(r"((x: P y | F) | h: (u | a) | b ) -> (y: Y) -> Z");
        print_and_unwrap(r"(X -> Y) Z ((t: T) => z)");
        print_and_unwrap(r"((x: X) => y)");
        print_and_unwrap(r"((x: X) | P) => y");
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
        parse_middle(r"x (( y: Y)");
        parse_middle(r"x::y x::y;");
    }
}
