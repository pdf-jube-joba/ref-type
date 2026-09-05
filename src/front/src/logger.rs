use crate::metavariables::MetaGoal;
use kernel::{
    derivation::{CheckSession, Judgement},
    environment::CrateEnv,
    exp::{Context, Exp},
    ids::ModuleId,
    sort::Sort,
};
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
    Goals(Vec<MetaGoal>),
}

#[derive(Debug, Clone, Serialize)]
pub struct LogRecord {
    pub level: LogLevel,
    pub tags: Vec<String>,
    pub message: String,
    pub payload: LogPayload,
}

#[derive(Default)]
pub struct Logger {
    records: Vec<LogRecord>,
}

impl Logger {
    pub fn records(&self) -> &[LogRecord] {
        &self.records
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
        self.records.push(record);
    }

    pub fn reduce_one(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        ctx: &mut Context,
        e: Exp,
    ) -> Option<Exp> {
        self.record(
            LogLevel::Trace,
            vec!["reduce_one".to_string()],
            "reduce_one called".to_string(),
            LogPayload::Exp(e),
        );

        let is_computation = matches!(
            CheckSession::new(env, module, ctx).infer_any(e),
            Ok(Judgement::Computation { .. })
        );
        let reduced = if is_computation {
            kernel::calculus::reduce_computation_once(env, e)
        } else {
            kernel::calculus::reduce_one(env, e)
        };
        match reduced {
            Some(reduced_exp) => {
                self.record(
                    LogLevel::Debug,
                    vec!["reduce_one".to_string()],
                    "reduce_one success".to_string(),
                    LogPayload::Exp(reduced_exp),
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

    pub fn normalize(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        ctx: &mut Context,
        e: Exp,
    ) -> Exp {
        self.record(
            LogLevel::Trace,
            vec!["normalize".to_string()],
            "normalize called".to_string(),
            LogPayload::Exp(e),
        );

        let is_computation = matches!(
            CheckSession::new(env, module, ctx).infer_any(e),
            Ok(Judgement::Computation { .. })
        );
        let normalized = if is_computation {
            match kernel::calculus::evaluate_computation(env, e) {
                kernel::calculus::Evaluation::Normal(result) => result,
                kernel::calculus::Evaluation::OutOfFuel(result) => {
                    self.record(
                        LogLevel::Warn,
                        vec!["normalize".to_string()],
                        "Program evaluation exhausted its reduction budget".to_string(),
                        LogPayload::Exp(result),
                    );
                    result
                }
            }
        } else {
            kernel::calculus::normalize(env, e)
        };
        self.record(
            LogLevel::Debug,
            vec!["normalize".to_string()],
            "normalize success".to_string(),
            LogPayload::Exp(normalized),
        );
        normalized
    }

    // Call the kernel. Detailed typing diagnostics are emitted as tracing spans.
    pub fn infer(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        ctx: &mut Context,
        exp: Exp,
    ) -> Option<Exp> {
        let infer_ty = CheckSession::new(env, module, ctx).infer(exp);
        match infer_ty {
            Ok(ty) => {
                self.record(
                    LogLevel::Debug,
                    vec!["infer".to_string()],
                    "infer success".to_string(),
                    LogPayload::Exp(ty),
                );
                Some(ty)
            }
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
    pub fn infer_sort(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        ctx: &mut Context,
        exp: Exp,
    ) -> Option<Sort> {
        match CheckSession::new(env, module, ctx).infer_sort(exp) {
            Ok(sort) => Some(sort),
            Err(derivation_fail) => {
                self.record(
                    LogLevel::Error,
                    vec!["infer_sort".to_string()],
                    format!("infer sort failed: {:?}", derivation_fail),
                    LogPayload::Message,
                );
                None
            }
        }
    }

    pub fn infer_any(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        ctx: &mut Context,
        exp: Exp,
    ) -> Option<Judgement> {
        match CheckSession::new(env, module, ctx).infer_any(exp) {
            Ok(judgement) => {
                let payload = match judgement {
                    Judgement::Pts { ty }
                    | Judgement::Value { ty }
                    | Judgement::Computation { ty } => LogPayload::Exp(ty),
                    Judgement::ValueType | Judgement::ComputationType => LogPayload::Message,
                };
                self.record(
                    LogLevel::Debug,
                    vec!["infer".to_string()],
                    format!("infer success: {judgement:?}"),
                    payload,
                );
                Some(judgement)
            }
            Err(derivation_fail) => {
                self.record(
                    LogLevel::Error,
                    vec!["infer".to_string()],
                    format!("infer failed: {derivation_fail:?}"),
                    LogPayload::Message,
                );
                None
            }
        }
    }
    pub fn check(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        ctx: &mut Context,
        exp: Exp,
        expected_type: Exp,
    ) -> bool {
        let mut session = CheckSession::new(env, module, ctx);
        let result = if matches!(env.arena().get(expected_type), kernel::exp::Node::Sort(_))
            || session.infer_sort(expected_type).is_ok()
        {
            session.check_pts(exp, expected_type)
        } else if session.check_value_type(expected_type).is_ok() {
            session.check_value(exp, expected_type)
        } else if session.check_computation_type(expected_type).is_ok() {
            session.check_computation(exp, expected_type)
        } else {
            Err(Box::new(kernel::derivation::JudgementError::caused(
                "expected type has no PTS or Program type judgement",
            )))
        };
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
