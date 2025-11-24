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
    Check {
        ctx: Context,
        exp: Exp,
        ty: Exp,
        result: bool,
    },
    Infer {
        ctx: Context,
        exp: Exp,
        result: Option<Exp>,
    },
    Reduce {
        exp: Exp,
        result: Option<Exp>,
    },
    Normal {
        exp: Exp,
        result: Exp,
    },
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

impl Logger {
    /// 新しい空のロガー
    pub fn new() -> Self {
        Self {
            records: Vec::new(),
        }
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

    pub fn records(&self) -> &[LogRecord] {
        &self.records
    }

    /// ログを取り出してクリアしたい場合などに
    pub fn into_records(self) -> Vec<LogRecord> {
        self.records
    }

    /// 必要ならクリア
    pub fn clear(&mut self) {
        self.records.clear();
    }

    pub fn with_infer(&mut self, ctx: &Context, exp: &Exp) -> Option<Exp> {
        let infer_ty = kernel::derivation::infer(ctx, exp);
        match infer_ty {
            Ok(derivation_success) => {
                let result: Option<Exp> = derivation_success.type_of().cloned();
                let payload = LogPayload::Infer {
                    ctx: ctx.clone(),
                    exp: exp.clone(),
                    result: result.clone(),
                };
                self.record(
                    LogLevel::Debug,
                    vec!["query".to_string(), "infer".to_string()],
                    format!("Infer query for expression: {:?}", exp),
                    payload,
                );
                result
            }
            Err(derivation_fail) => {
                let payload = LogPayload::Infer {
                    ctx: ctx.clone(),
                    exp: exp.clone(),
                    result: None,
                };
                self.record(
                    LogLevel::Warn,
                    vec!["query".to_string(), "infer".to_string()],
                    format!("Infer query failed for expression: {:?}", exp),
                    payload,
                );
                None
            }
        }
    }
}

#[macro_export]
macro_rules! log_msg {
    ($ctx:expr, $level:expr, [$($tag:expr),*], $($arg:tt)*) => {{
        let msg = format!($($arg)*);
        let tags = vec![$($tag.to_string()),*];
        $ctx.logger().record(
            $level,
            tags,
            msg,
            $crate::logging::LogPayload::Message,
        );
    }};
}

#[macro_export]
macro_rules! log_derivation_success {
    ($ctx:expr, $level:expr, [$($tag:expr),*], $der:expr, $($arg:tt)*) => {{
        let msg = format!($($arg)*);
        let tags = vec![$($tag.to_string()),*];
        $ctx.logger().record(
            $level,
            tags,
            msg,
            $crate::logging::LogPayload::DerivationSuccess($der),
        );
    }};
}

#[macro_export]
macro_rules! log_derivation_fail {
    ($ctx:expr, $level:expr, [$($tag:expr),*], $der:expr, $($arg:tt)*) => {{
        let msg = format!($($arg)*);
        let tags = vec![$($tag.to_string()),*];
        $ctx.logger().record(
            $level,
            tags,
            msg,
            $crate::logging::LogPayload::DerivationFail($der),
        );
    }};
}
