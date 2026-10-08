use super::*;
use syntax::sort::Sort;

fn product(parameters: &[RightBind], mut body: SExp) -> SExp {
    for bind in parameters.iter().rev() {
        body = SExp::Prod {
            bind: Bind::Named(bind.clone()),
            body: Box::new(body),
        };
    }
    body
}

fn apply(func: SExp, arg: SExp) -> SExp {
    SExp::App {
        func: Box::new(func),
        arg: Box::new(arg),
    }
}

impl Resolver {
    fn existence_proposition(&mut self) -> RightBind {
        let mut name = Identifier("<existence-proposition>".into());
        self.binding(&mut name);
        RightBind {
            vars: vec![name],
            ty: Box::new(SExp::Sort(Sort::Prop)),
        }
    }

    pub(super) fn structure_existence(&mut self, ty: &SExp) -> SExp {
        let proposition = self.existence_proposition();
        let result = variable(proposition.vars[0].clone());
        let continuation = product(
            &[RightBind {
                vars: vec![Identifier("<existence-witness>".into())],
                ty: Box::new(ty.clone()),
            }],
            result.clone(),
        );
        product(
            &[
                proposition,
                RightBind {
                    vars: Vec::new(),
                    ty: Box::new(continuation),
                },
            ],
            result,
        )
    }

    pub(super) fn structure_exists_intro(
        &mut self,
        ty: &SExp,
        element: &SExp,
        locals: &[LocalScope],
    ) -> Result<SExp, Diagnostic> {
        let mut parameters = vec![RightBind {
            vars: vec![Identifier("<existence-witness>".into())],
            ty: Box::new(ty.clone()),
        }];
        self.expand_structure_parameters(&mut parameters, &mut locals.to_vec(), false)?;
        let input = self.last_inputs[0].clone();
        let (arguments, checks) = self.callback_arguments(&input, element, locals)?;
        let proposition = self.existence_proposition();
        let result = variable(proposition.vars[0].clone());
        let mut continuation = Identifier("<existence-continuation>".into());
        self.binding(&mut continuation);
        let body = arguments
            .into_iter()
            .fold(variable(continuation.clone()), apply);
        Ok(abstract_parameters(
            &[
                proposition,
                RightBind {
                    vars: vec![continuation],
                    ty: Box::new(product(&parameters, result)),
                },
            ],
            SExp::Checked {
                checks,
                body: Box::new(body),
            },
        ))
    }

    pub(super) fn structure_exists_elim(
        &mut self,
        bind: &RightBind,
        body: &SExp,
        existence: &SExp,
    ) -> SExp {
        apply(
            apply(
                SExp::Ascribe {
                    term: Box::new(existence.clone()),
                    ty: Box::new(self.structure_existence(&bind.ty)),
                },
                SExp::Meta {
                    kind: SurfaceMeta::Implicit,
                    span: SourceSpan::default(),
                },
            ),
            SExp::Lam {
                bind: Bind::Named(bind.clone()),
                body: Box::new(body.clone()),
            },
        )
    }
}
