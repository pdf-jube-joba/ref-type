use super::{
    BLOCK_KEYWORDS, EXPRESSION_ATOM_KEYWORDS, EXPRESSION_SEPARATION_KEYWORDS, PROGRAM_KEYWORDS,
    PROOF_COMMAND_KEYWORDS, ParseError, SORT_KEYWORDS, SpannedToken, Token,
};
use crate::syntax::*;

pub struct TermParser<'a> {
    tokens: &'a [SpannedToken<'a>],
    pos: usize,
}

impl<'a> TermParser<'a> {
    pub fn new(tokens: &'a [SpannedToken<'a>]) -> Self {
        Self { tokens, pos: 0 }
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

    // Helper to parse a parenthesized expression.
    // "(" <some: parse_inner> ")" where parse_inner is given as a closure.
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
        self.expect_token(Token::LParen);
        let number = self.expect_number()?;
        self.expect_token(Token::RParen)?;

        Ok(number)
    }

    // Parse a sort expression.
    // \Prop | \PropKind | \Set ( "(" <number> ")" )? | \SetKind ( "(" <number> ")" )?
    fn parse_sort(&mut self) -> Result<kernel::exp::Sort, ParseError> {
        if self.bump_if_keyword("\\Prop") {
            return Ok(kernel::exp::Sort::Prop);
        }
        if self.bump_if_keyword("\\PropKind") {
            return Ok(kernel::exp::Sort::PropKind);
        }
        if self.bump_if_keyword("\\Set") {
            let number = match self.try_parse(|parser| parser.parse_number_paren())? {
                Some(n) => n,
                None => 0,
            };

            return Ok(kernel::exp::Sort::Set(number));
        }
        if self.bump_if_keyword("\\SetKind") {
            let number = match self.try_parse(|parser| parser.parse_number_paren())? {
                Some(n) => n,
                None => 0,
            };
            return Ok(kernel::exp::Sort::SetKind(number));
        }

        Err(ParseError {
            msg: "expected sort keyword".into(),
            start: self.pos,
            end: self.pos,
        })
    }

    fn parse_keyword_head_atom(&mut self) -> Result<SExp, ParseError> {
        // simple cases (<keyword> "(" expressions with comma separated ")")
        if self.bump_if_keyword("\\Proof") {
            return self.parse_parenthesized(|parser| {
                parser.parse_sexp().map(|term| SExp::ProveLater {
                    prop: Box::new(term),
                })
            });
        }
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
        // elimination of inductive type
        if self.bump_if_keyword("\\elim") {
            // "\elim" <elim: SExp> "\in" <path: Path> "\\return" <return_type: SExp>
            let elim = self.parse_sexp()?;
            self.expect_keyword("\\in")?; // expect '\in'
            let (path, _parameters) = self.parse_access_path()?;
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
            // "\prec" "(" <sort: Sort> "," <path: AccessPath> ")"
            self.expect_token(Token::LParen)?;
            let sort = self.parse_sort()?;
            self.expect_token(Token::Comma)?;
            let (path, parameters) = self.parse_access_path()?;
            self.expect_token(Token::RParen)?;

            let parameters = parameters.unwrap_or_default();

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
            return Ok(SExp::Take {
                bind,
                body: Box::new(body),
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

    fn parse_proof_command(&mut self) -> Result<SProveCommandBy, ParseError> {
        if self.bump_if_keyword("\\term") {
            self.expect_token(Token::LParen)?; // expect '('
            let term = self.parse_sexp()?;
            self.expect_token(Token::RParen)?; // expect ')'
            return Ok(SProveCommandBy::Construct {
                term: Box::new(term),
            });
        }

        if self.bump_if_keyword("\\exact") {
            self.expect_token(Token::LParen)?; // expect '('
            let term = self.parse_sexp()?;
            self.expect_token(Token::Comma)?; // expect ','
            let set = self.parse_sexp()?;
            self.expect_token(Token::RParen)?; // expect ')'
            return Ok(SProveCommandBy::Exact {
                term: Box::new(term),
                set: Box::new(set),
            });
        }

        if self.bump_if_keyword("\\refl") {
            self.expect_token(Token::LParen)?; // expect '('
            let term = self.parse_sexp()?;
            self.expect_token(Token::RParen)?; // expect ')'
            return Ok(SProveCommandBy::IdRefl {
                term: Box::new(term),
            });
        }

        // \\idelim "(" <left: SExp> "=" <right: SExp> "\with" <var: Ident> ":" <ty: SExp> "=>" <predicate: SExp> ")"
        if self.bump_if_keyword("\\idelim") {
            self.expect_token(Token::LParen)?; // expect '('
            let left = self.parse_sexp()?;
            self.expect_token(Token::Equal)?; // expect '='
            let right = self.parse_sexp()?;
            self.expect_keyword("\\with")?; // expect '\with'
            let var = self.expect_ident()?;
            self.expect_token(Token::Colon)?; // expect ':'
            let ty = self.parse_sexp()?;
            self.expect_token(Token::DoubleArrow)?; // expect '=>'
            let predicate = self.parse_sexp()?;
            self.expect_token(Token::RParen)?; // expect ')'
            return Ok(SProveCommandBy::IdElim {
                left: Box::new(left),
                right: Box::new(right),
                var,
                ty: Box::new(ty),
                predicate: Box::new(predicate),
            });
        }

        if self.bump_if_keyword("\\takeelim") {
            todo!("takeelim proof command not implemented yet");
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
                while let Ok(bind) = self.parse_simple_bind_paren() {
                    binds.push(bind);
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
                // "\take" <bind: Bind> ";"
                let bind = self.parse_left_arrow_head()?;
                self.expect_token(Token::Semicolon)?; // expect ';'
                statements.push(Statement::Take { bind });
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

    // parse an access path
    // 1. identifier | identifier "[" (SExp ("," SExp)*)? "]" ... current scope
    // 2. identifier "." identifier | identifier . identifier "{" (SExp ("," SExp)*)? "}" ... named scope
    // ! no nesting of ".", it appears at most once
    fn parse_access_path(&mut self) -> Result<(LocalAccess, Option<Vec<SExp>>), ParseError> {
        // 1. expect first identifier
        let first_ident = self.expect_ident()?;
        // 2. if ".", expect more identifiers
        let next_ident: Option<Identifier> = if self.bump_if_token(&Token::Period) {
            // named scope access
            let next_ident = self.expect_ident()?;
            Some(next_ident)
        } else {
            None
        };

        let save_pos = self.pos;

        // trying to parse parameters
        // may be fail => rollback
        let parameters = if self.bump_if_token(&Token::LBracket) {
            // parse parameters inside '{' ... '}'
            let mut params = Vec::new();
            while let Ok(param) = self.parse_sexp() {
                params.push(param);
                if !self.bump_if_token(&Token::Comma) {
                    break;
                }
            }
            if self.bump_if_token(&Token::RBracket) {
                // successfully closed
            } else {
                // rollback if not closed
                self.pos = save_pos;
            }
            params
        } else {
            Vec::new()
        };

        let local_access = match next_ident {
            Some(child) => LocalAccess::Named {
                access: first_ident,
                child,
            },
            None => LocalAccess::Current {
                access: first_ident,
            },
        };
        Ok((
            local_access,
            if parameters.is_empty() {
                None
            } else {
                Some(parameters)
            },
        ))
    }

    // parse a single atom
    // e.g. `x`, `x.y`, `x.y.z`, `(x)`, `$( ... )$`, `! name { ... }`
    // or something start with keyword (sort, etc.)
    fn parse_atom(&mut self) -> Result<SExp, ParseError> {
        match self.peek() {
            Some(Token::Ident(_)) => {
                let (access_path, parameters) = self.parse_access_path()?;
                if self.bump_if_token(&Token::Field) {
                    // constructor access
                    let ctor_name = self.expect_ident()?;
                    let parameters = parameters.unwrap_or_default();
                    Ok(SExp::IndCtor {
                        path: access_path,
                        parameters,
                        ctor_name,
                    })
                } else {
                    Ok(SExp::AccessPath {
                        access: access_path,
                        parameters: parameters.unwrap_or_default(),
                    })
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
                // parse inner macro token sequence
                let mut tokens = vec![];
                while let Ok(tok) = self.parse_one_macro() {
                    tokens.push(tok);
                }
                self.expect_token(Token::MathRParen)?; // expect ')$'
                Ok(SExp::MathMacro { tokens })
            }
            Some(Token::Exclamation) => {
                self.next(); // consume '!'
                let name = self.expect_ident()?;
                self.expect_token(Token::LBrace)?; // expect '{'
                // parse inner macro token sequence
                let mut tokens = vec![];
                while let Ok(tok) = self.parse_one_macro() {
                    tokens.push(tok);
                }
                self.expect_token(Token::RBrace)?; // expect '}'
                Ok(SExp::NamedMacro { name, tokens })
            }
            Some(Token::KeyWord(keyword)) if SORT_KEYWORDS.contains(keyword) => {
                // check if it's a reserved sort keyword
                self.parse_sort().map(SExp::Sort)
            }
            Some(Token::KeyWord(keyword)) if EXPRESSION_ATOM_KEYWORDS.contains(keyword) => {
                self.parse_keyword_head_atom()
            }
            Some(Token::KeyWord(keyword)) if PROOF_COMMAND_KEYWORDS.contains(keyword) => {
                Ok(SExp::ProofTermRaw(self.parse_proof_command()?))
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

    // parse a sequence of atoms (AtomLike)
    // e.g. `x`, `(x)`, `x y`, `x (y z)`, `(x y) z`
    fn parse_atom_sequence(&mut self) -> Result<SExp, ParseError> {
        // 1. first atom
        let mut expr = self.parse_atom()?;

        loop {
            let save = self.pos;
            match self.parse_atom() {
                Ok(next_atom) => {
                    expr = SExp::App {
                        func: Box::new(expr),
                        arg: Box::new(next_atom),
                        piped: false,
                    };
                }
                Err(_) => {
                    // if not atom, rollback and break
                    self.pos = save;
                    break;
                }
            }
        }

        Ok(expr)
    }

    // parse a expression with
    // 1. piped application ... <e: AtomSeq> "|" <e: AtomSeq>
    // 2. as expression ... <e: PipedAtomSeq> "\as" <e: PipedAtomSeq>
    // 3. equal expression ... <e: AsExp> "=" <e: AsExp>
    fn parse_combined(&mut self) -> Result<SExp, ParseError> {
        fn piped(parser: &mut TermParser) -> Result<SExp, ParseError> {
            let mut expr = parser.parse_atom_sequence()?;
            // 1. parse first atom sequence

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
            let from_exp = piped(parser)?;
            if parser.bump_if_keyword("\\as") {
                let to_exp = piped(parser)?;
                Ok(SExp::Cast {
                    exp: Box::new(from_exp),
                    to: Box::new(to_exp),
                })
            } else {
                Ok(from_exp)
            }
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
        vars.push(self.expect_ident()?);

        while self.bump_if_token(&Token::Comma) {
            vars.push(self.expect_ident()?);
        }

        self.expect_token(Token::Colon)?; // expect ":"

        // 3. parse the type
        let ty = self.parse_sexp()?;

        Ok((vars, ty))
    }

    // "(" Ident ("," Ident)* ":" SExp ")"
    fn parse_simple_bind_paren(&mut self) -> Result<RightBind, ParseError> {
        self.expect_token(Token::LParen)?; // expect '('
        let (vars, ty) = self.parse_annotate()?;
        self.expect_token(Token::RParen)?; // expect ')'
        Ok(RightBind {
            vars,
            ty: Box::new(ty),
        })
    }

    pub fn parse_simple_binds_advanced(&mut self) -> Result<(RightBind, usize), ParseError> {
        let binds = self.parse_simple_bind_paren()?;
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
        self.expect_token(Token::RParen)?;

        self.expect_token(Token::Pipe)?; // expect '|'

        let save_pos = self.pos;

        // try to parse proof style first (annotation)
        match self.parse_annotate() {
            Ok((vars, predicate)) => {
                let [var] = vars.as_slice() else {
                    return Err(ParseError {
                        msg: "expected single identifier in subset bind".into(),
                        start: self.pos,
                        end: self.pos,
                    });
                };
                Ok(Bind::SubsetWithProof {
                    var: var.clone(),
                    ty: Box::new(first_ty),
                    predicate: Box::new(predicate),
                    proof_var: var.clone(),
                })
            }
            Err(_) => {
                // rollback to after '|'
                self.pos = save_pos;
                let predicate = self.parse_sexp()?;
                Ok(Bind::Subset {
                    var: var.clone(),
                    ty: Box::new(first_ty),
                    predicate: Box::new(predicate),
                })
            }
        }
    }

    // binder complex case
    // "(" Ident ":"" SExp ")"
    // "(" "(" Ident ":" SExp ")" "|" SExp ")"
    // "(" "(" Ident ":" SExp ")" "|" Ident ":" SExp ")"
    fn try_parse_complex_bind(&mut self) -> Result<Option<Bind>, ParseError> {
        let save_pos = self.pos;

        // try subset bind first
        // "(" "("
        if let Ok(bind) = self.parse_subsetbind() {
            return Ok(Some(bind));
        }
        // rollback if not
        self.pos = save_pos;

        // try simple bind next
        // "("
        if let Some(bind) = self.parse_simple_bind_paren()? {
            return Ok(Some(Bind::Named(bind)));
        }
        // rollback if neither worked
        self.pos = save_pos;
        Ok(None)
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

        match left_head {
            Bind::Anonymous { ty } => Ok(*ty),
            _ => Err(ParseError {
                msg: "expected '->' or '=>' after bind".into(),
                start: self.pos,
                end: self.pos,
            }),
        }
    }

    // parse arrow expression with right binds
    // e.g. <rightbinds> "->" <body>
    fn parse_arrow_expr_rightbind(&mut self) -> Result<(Vec<RightBind>, SExp), ParseError> {
        let mut binds = vec![];
        // parse right binds until fail
        loop {
            let save_pos = self.pos;
            if let Some(bind) = self.try_parse_simple_bind_paren()? {
                binds.push(bind);
            } else {
                self.pos = save_pos;
                break;
            }
            self.expect_token(Token::Arrow)?; // expect '->' after each bind
        }
        let body = self.parse_sexp()?;
        Ok((binds, body))
    }

    pub fn parse_arrow_rightbinds_advanced(
        &mut self,
    ) -> Result<(Vec<RightBind>, SExp, usize), ParseError> {
        let (binds, body) = self.parse_arrow_expr_rightbind()?;
        let advanced_pos = self.pos;
        Ok((binds, body, advanced_pos))
    }

    // ("(" <Ident> ":" <SExp> ")"" "->")* | (<SExp> "->")*
    // it consumes "->" after each bind
    fn parse_rightbind_arrow_lefts(&mut self) -> Result<Vec<RightBind>, ParseError> {
        let mut binds = Vec::new();
        loop {
            let save_pos = self.pos;
            if let Some(bind) = self.try_parse_simple_bind_paren()? {
                if self.bump_if_token(&Token::Arrow) {
                    binds.push(bind);
                    continue;
                } else {
                    self.pos = save_pos;
                    break;
                }
            }

            // try to parse anonymous bind
            let expr = match self.parse_combined() {
                Ok(e) => e,
                Err(_) => {
                    self.pos = save_pos;
                    break;
                }
            };
            if self.bump_if_token(&Token::Arrow) {
                binds.push(RightBind {
                    vars: vec![],
                    ty: Box::new(expr),
                });
                continue;
            } else {
                self.pos = save_pos;
                break;
            }
        }
        Ok(binds)
    }

    // parse the left-hand side of an arrow expression
    // may be a bind or a simple expression or a parenthesized expression
    // e.g. `x y -> z`, `(x y) -> z`, `(x: y) -> z`, `((x: y) | P) -> z`
    fn parse_left_arrow_head(&mut self) -> Result<Bind, ParseError> {
        // 1. try to parse complex bind first
        if let Some(bind) = self.try_parse_complex_bind()? {
            return Ok(bind);
        }

        // 2. otherwise, parse simple expression as a bind
        let expr = self.parse_combined()?;
        Ok(Bind::Anonymous { ty: Box::new(expr) })
    }

    fn parse_sexp(&mut self) -> Result<SExp, ParseError> {
        let sexp = self.parse_arrow_expr()?;
        if self.bump_if_keyword("\\with") {
            // \\with "{" ("\\goal" <simple_bind_parend>* ":" <sexp> ":=" <sexp> ";" )* "}"
            self.expect_token(Token::LBrace)?; // expect '{'
            let mut proofs = vec![];
            while self.bump_if_keyword("\\goal") {
                // parse iteration of <simple_bind_parend>*
                let mut binds = vec![];
                while let Some(bind) = self.try_parse_simple_bind_paren()? {
                    binds.push(bind);
                }
                self.expect_token(Token::Colon)?;
                let goal = self.parse_sexp()?;
                self.expect_token(Token::Assign)?;
                let proofby = self.parse_proof_command()?;
                self.expect_token(Token::Semicolon)?;
                proofs.push(GoalProof {
                    extended_ctx: binds,
                    goal,
                    proofby,
                });
            }
            self.expect_token(Token::RBrace)?; // expect '}'
            Ok(SExp::WithProofs {
                exp: Box::new(sexp),
                proofs,
            })
        } else {
            Ok(sexp)
        }
    }

    fn try_parse_sexp(&mut self) -> Result<Option<SExp>, ParseError> {
        let save_pos = self.pos;
        match self.parse_sexp() {
            Ok(exp) => Ok(Some(exp)),
            Err(_) => {
                self.pos = save_pos;
                Ok(None)
            }
        }
    }

    pub fn parse_sexp_advanced(&mut self) -> Result<(SExp, usize), ParseError> {
        let exp = self.parse_sexp()?;
        let advanced_pos = self.pos;
        Ok((exp, advanced_pos))
    }

    // parse marco tokens
    fn parse_one_macro(&mut self) -> Result<MacroExp, ParseError> {
        // 1, challenge atom
        if let Ok(atom) = self.parse_atom() {
            return Ok(MacroExp::Exp(atom));
        }
        // 2. challenge one macro token
        // OthetSymbolStart or KeyWord which is not contained in *_KEYWORDS
        if let Some(Token::MacroToken(_)) = self.peek() {
            let sym = self.expect_othersymbol()?;
            return Ok(MacroExp::Tok(MacroToken(sym.to_string())));
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
    fn parse_bind_test() {
        fn print_and_unwrap_complex_bind(input: &'static str) {
            let lex = &lex_all(input).expect("lexing failed for complex bind test");
            let mut parser = TermParser::new(lex);
            let result = parser.try_parse_complex_bind();
            match result {
                Ok(Some(bind)) => {
                    println!("Parsed SExp: {:?} => {:?}", input, bind);
                }
                Ok(None) => {
                    panic!("Failed to parse complex bind: {}", input);
                }
                Err(err) => {
                    panic!("Error: {:?}", err);
                }
            }
        }
        print_and_unwrap_complex_bind(r"(x: X)");
        print_and_unwrap_complex_bind(r"((x: X) | P)");
        print_and_unwrap_complex_bind(r"((x: X) | p1 p2)");
        print_and_unwrap_complex_bind(r"((x: X) | h: p1 p2)");
    }
    fn print_and_unwrap(input: &'static str) {
        let lex = &lex_all(input).expect("lexing failed for exp test");
        let mut parser = TermParser::new(lex);
        let result = parser.parse_sexp();
        match result {
            Ok(atomlike) => {
                println!("Parsed SExp: {:?} => {:?}", input, atomlike);
            }
            Err(err) => {
                panic!(" {:?}", err);
            }
        }
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
    fn parse_special_exp_test() {
        // atom like: sort, access path, math macro, named macro
        print_and_unwrap("x");
        print_and_unwrap(r"\Prop");
        print_and_unwrap(r"\Set");
        print_and_unwrap(r"\Set(3)");
        print_and_unwrap(r"\Set(3) x");
        print_and_unwrap(r"x \Set(3)");
        print_and_unwrap(r"x.y.z");
        print_and_unwrap(r"x.a b (c. g)");
        print_and_unwrap(r"x $( y + z )$ l");
        print_and_unwrap(r"x ! mymacro { a + b c } l");
        // parse as, equal
        print_and_unwrap(r"x \as Y");
        print_and_unwrap(r"x = y");
        print_and_unwrap(r"x \as Y | z = h");
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
    }
}
