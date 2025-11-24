use kernel::exp::{DerivationFail, DerivationSuccess};
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
}

#[derive(Debug, Clone, Serialize)]
pub struct LogRecord {
    pub level: LogLevel,
    pub tags: Vec<String>,
    pub message: String,

    pub module: &'static str,
    pub file: &'static str,
    pub line: u32,

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
        module: &'static str,
        file: &'static str,
        line: u32,
    ) {
        let record = LogRecord {
            level,
            tags,
            message,
            module,
            file,
            line,
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
            module_path!(),
            file!(),
            line!(),
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
            module_path!(),
            file!(),
            line!(),
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
            module_path!(),
            file!(),
            line!(),
        );
    }};
}
