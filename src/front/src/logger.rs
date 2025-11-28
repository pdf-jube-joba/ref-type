use kernel::exp::{Context, DerivationFail, DerivationSuccess, Exp};
use serde::Serialize;

#[derive(Debug, Clone, Serialize)]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
}

#[derive(Debug, Clone, Serialize)]
pub enum LogPayload {
    Message, // 純粋なテキストメッセージだけ
    DerivationSuccess(DerivationSuccess),
    DerivationFail(DerivationFail),
    Exp(Exp),
    Ctx(Context),
}

#[derive(Debug, Clone, Serialize)]
pub struct LogRecord {
    pub level: LogLevel,
    pub tags: Vec<String>,
    pub message: String,
    pub payload: LogPayload,
}

pub struct Logger {
    records: Vec<LogRecord>,
}

impl Default for Logger {
    fn default() -> Self {
        Self::new()
    }
}

impl Logger {
    /// 新しい空のロガー
    pub fn new() -> Self {
        Self {
            records: Vec::new(),
        }
    }

    pub fn records(&self) -> &[LogRecord] {
        &self.records
    }
    pub fn into_records(self) -> Vec<LogRecord> {
        self.records
    }
    pub fn clear(&mut self) {
        self.records.clear();
    }

    pub fn push(&mut self, record: LogRecord) {
        self.records.push(record);
    }

    pub fn record(
        &mut self,
        level: LogLevel,
        tags: Vec<String>,
        message: String,
        payload: LogPayload,
    ) {
        let record = LogRecord {
            level,
            tags,
            message,
            payload,
        };
        self.push(record);
    }

    pub fn reduce_one(&mut self, e: Exp) -> Option<Exp> {
        self.record(
            LogLevel::Trace,
            vec!["reduce_one".to_string()],
            "reduce_one called".to_string(),
            LogPayload::Exp(e.clone()),
        );

        let reduced = kernel::calculus::reduce_one(&e);
        match reduced {
            Some(reduced_exp) => {
                self.record(
                    LogLevel::Debug,
                    vec!["reduce_one".to_string()],
                    "reduce_one success".to_string(),
                    LogPayload::Exp(reduced_exp.clone()),
                );
                Some(reduced_exp)
            }
            None => {
                self.record(
                    LogLevel::Info,
                    vec!["reduce_one".to_string()],
                    "reduce_one no reduction possible".to_string(),
                    LogPayload::Message,
                );
                None
            }
        }
    }

    pub fn normalize(&mut self, e: Exp) -> Exp {
        self.record(
            LogLevel::Trace,
            vec!["normalize".to_string()],
            "normalize called".to_string(),
            LogPayload::Exp(e.clone()),
        );

        let normalized = kernel::calculus::normalize(&e);
        self.record(
            LogLevel::Debug,
            vec!["normalize".to_string()],
            "normalize success".to_string(),
            LogPayload::Exp(normalized.clone()),
        );
        normalized
    }

    // call kernel::derivation::check and log the result and log derivation
    pub fn infer(&mut self, ctx: &Context, exp: &Exp) -> Option<Exp> {
        self.record(
            LogLevel::Trace,
            vec!["infer".to_string()],
            "infer called".to_string(),
            LogPayload::Exp(exp.clone()),
        );
        self.record(
            LogLevel::Trace,
            vec!["infer".to_string()],
            "context for infer".to_string(),
            LogPayload::Ctx(ctx.clone()),
        );

        let infer_ty = kernel::derivation::infer(ctx, exp);
        match infer_ty {
            Ok(derivation_success) => {
                let result: Option<Exp> = derivation_success.type_of().cloned();
                let payload = LogPayload::DerivationSuccess(derivation_success);
                self.record(
                    LogLevel::Debug,
                    vec!["infer".to_string()],
                    "infer success".to_string(),
                    payload,
                );
                result
            }
            Err(derivation_fail) => {
                let payload = LogPayload::DerivationFail(*derivation_fail);
                self.record(
                    LogLevel::Error,
                    vec!["infer".to_string()],
                    "infer failed".to_string(),
                    payload,
                );
                None
            }
        }
    }
    pub fn check(&mut self, ctx: &Context, exp: &Exp, expected_type: &Exp) -> bool {
        self.record(
            LogLevel::Trace,
            vec!["check".to_string()],
            "check called".to_string(),
            LogPayload::Exp(exp.clone()),
        );
        self.record(
            LogLevel::Trace,
            vec!["check".to_string()],
            "expected type for check".to_string(),
            LogPayload::Exp(expected_type.clone()),
        );

        let result = kernel::derivation::check(ctx, exp, expected_type);
        match result {
            Ok(derivation_success) => {
                let payload = LogPayload::DerivationSuccess(derivation_success);
                self.record(
                    LogLevel::Debug,
                    vec!["check".to_string()],
                    "check success".to_string(),
                    payload,
                );
                true
            }
            Err(derivation_fail) => {
                let payload = LogPayload::DerivationFail(*derivation_fail);
                self.record(
                    LogLevel::Error,
                    vec!["check".to_string()],
                    "check failed".to_string(),
                    payload,
                );
                false
            }
        }
    }
    pub fn check_wellformed_indspec(
        &mut self,
        ctx: &Context,
        indspec: &kernel::inductive::InductiveTypeSpecs,
    ) -> bool {
        self.record(
            LogLevel::Trace,
            vec!["check_wellformed_indspec".to_string()],
            "check_wellformed_indspec called".to_string(),
            LogPayload::Message,
        );

        let result = kernel::inductive::acceptable_typespecs(ctx, indspec);
        match result {
            Ok(derivation_success) => {
                let payload = LogPayload::DerivationSuccess(derivation_success);
                self.record(
                    LogLevel::Debug,
                    vec!["check_wellformed_indspec".to_string()],
                    "check_wellformed_indspec success".to_string(),
                    payload,
                );
                true
            }
            Err(derivation_fail) => {
                let payload = LogPayload::DerivationFail(*derivation_fail);
                self.record(
                    LogLevel::Error,
                    vec!["check_wellformed_indspec".to_string()],
                    "check_wellformed_indspec failed".to_string(),
                    payload,
                );
                false
            }
        }
    }
    pub fn log_msg(&mut self, level: LogLevel, tags: Vec<String>, message: String) {
        self.record(level, tags, message, LogPayload::Message);
    }
}

#[macro_export]
macro_rules! log_record {
    ($ctx:expr, $level:expr, [$($tag:expr),*], $payload:expr, $($arg:tt)*) => {{
        let msg  = format!($($arg)*);
        let tags = vec![$($tag.to_string()),*];
        $ctx.record(
            $level,
            tags,
            msg,
            $payload,
        );
    }};
}

#[macro_export]
macro_rules! log_msg {
    ($ctx:expr, $level:expr, [$($tag:expr),*], $($arg:tt)*) => {{
        let msg = format!($($arg)*);
        let tags = vec![$($tag.to_string()),*];
        $ctx.record(
            $level,
            tags,
            msg,
            $crate::logger::LogPayload::Message,
        );
    }};
}

#[macro_export]
macro_rules! log_derivation_success {
    ($ctx:expr, $level:expr, [$($tag:expr),*], $der:expr, $($arg:tt)*) => {{
        let msg = format!($($arg)*);
        let tags = vec![$($tag.to_string()),*];
        $ctx.record(
            $level,
            tags,
            msg,
            $crate::logger::LogPayload::DerivationSuccess($der),
        );
    }};
}

#[macro_export]
macro_rules! log_derivation_fail {
    ($ctx:expr, $level:expr, [$($tag:expr),*], $der:expr, $($arg:tt)*) => {{
        let msg = format!($($arg)*);
        let tags = vec![$($tag.to_string()),*];
        $ctx.record(
            $level,
            tags,
            msg,
            $crate::logger::LogPayload::DerivationFail($der),
        );
    }};
}
