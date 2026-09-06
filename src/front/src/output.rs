use kernel::{
    exp::Exp,
    program::{Computation, ComputationType, ValueType},
};

#[derive(Debug, Clone)]
pub enum Output {
    Message(String),
    Exp(Exp),
    ValueType(ValueType),
    ComputationType(ComputationType),
    Computation(Computation),
    OutOfFuel(Computation),
}
