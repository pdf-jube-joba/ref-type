use kernel::exp::{Context, Exp};
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

    // Call the kernel. Detailed typing diagnostics are emitted as tracing spans.
    pub fn infer(&mut self, ctx: &Context, exp: &Exp) -> Option<Exp> {
        let infer_ty = kernel::derivation::infer(ctx, exp);
        match infer_ty {
            Ok(ty) => Some(ty),
            Err(derivation_fail) => {
                self.record(
                    LogLevel::Error,
                    vec!["infer".to_string()],
                    format!("infer failed: {:?}", derivation_fail),
                    LogPayload::Message,
                );
                None
            }
        }
    }
    pub fn check(&mut self, ctx: &Context, exp: &Exp, expected_type: &Exp) -> bool {
        let result = kernel::derivation::check(ctx, exp, expected_type);
        match result {
            Ok(()) => true,
            Err(derivation_fail) => {
                self.record(
                    LogLevel::Error,
                    vec!["check".to_string()],
                    format!("check failed: {:?}", derivation_fail),
                    LogPayload::Message,
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
