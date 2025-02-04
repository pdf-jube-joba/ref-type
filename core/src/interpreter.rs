use crate::context::GlobalContext;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Interpreter {
    global_context: GlobalContext,
}

