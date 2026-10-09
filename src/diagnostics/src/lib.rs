//! Portable diagnostic data for API responses and saved semantic results.
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct DiagnosticData {
    pub code: String,
    pub arguments: BTreeMap<String, Value>,
    pub causes: Vec<DiagnosticData>,
}
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(untagged)]
pub enum Value {
    Text(String),
    Unsigned(u64),
    Bool(bool),
    List(Vec<Value>),
    Diagnostic(Box<DiagnosticData>),
}
impl DiagnosticData {
    pub fn new(code: impl Into<String>) -> Self {
        Self {
            code: code.into(),
            arguments: BTreeMap::new(),
            causes: Vec::new(),
        }
    }
    pub fn with(mut self, name: impl Into<String>, value: impl Into<Value>) -> Self {
        self.arguments.insert(name.into(), value.into());
        self
    }
    pub fn caused_by(mut self, cause: Self) -> Self {
        self.causes.push(cause);
        self
    }
}
impl From<String> for Value {
    fn from(value: String) -> Self {
        Self::Text(value)
    }
}
impl From<&str> for Value {
    fn from(value: &str) -> Self {
        Self::Text(value.to_owned())
    }
}
impl From<usize> for Value {
    fn from(value: usize) -> Self {
        Self::Unsigned(value as u64)
    }
}
impl From<u32> for Value {
    fn from(value: u32) -> Self {
        Self::Unsigned(value.into())
    }
}
impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Self::Bool(value)
    }
}
impl From<DiagnosticData> for Value {
    fn from(value: DiagnosticData) -> Self {
        Self::Diagnostic(Box::new(value))
    }
}

pub trait DiagnosticError: std::error::Error {
    fn diagnostic_data(&self) -> DiagnosticData;
}
