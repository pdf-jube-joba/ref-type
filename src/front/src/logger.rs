use crate::metavariables::MetaGoal;
use kernel::{
    derivation::CheckSession,
    environment::CrateEnv,
    exp::{Exp, ExpContext, ExpJudgement},
    ids::ModuleId,
    program::{Computation, ComputationType, Value, ValueType},
    program_calculus::Evaluation,
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
    Message,
    Exp(Exp),
    ValueType(ValueType),
    ComputationType(ComputationType),
    Value(Value),
    Computation(Computation),
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
        self.records.push(LogRecord {
            level,
            tags,
            message,
            payload,
        });
    }

    pub fn reduce_one(&mut self, env: &CrateEnv, exp: Exp) -> Option<Exp> {
        self.record(
            LogLevel::Trace,
            vec!["reduce_one".into()],
            "reduce_one called".into(),
            LogPayload::Exp(exp),
        );
        let reduced = kernel::calculus::reduce_one(env, exp);
        match reduced {
            Some(result) => self.record(
                LogLevel::Debug,
                vec!["reduce_one".into()],
                "reduce_one success".into(),
                LogPayload::Exp(result),
            ),
            None => self.record(
                LogLevel::Info,
                vec!["reduce_one".into()],
                "reduce_one no reduction possible".into(),
                LogPayload::Message,
            ),
        }
        reduced
    }

    pub fn normalize(&mut self, env: &CrateEnv, exp: Exp) -> Exp {
        let result = kernel::calculus::normalize(env, exp);
        self.record(
            LogLevel::Debug,
            vec!["normalize".into()],
            "normalize success".into(),
            LogPayload::Exp(result),
        );
        result
    }

    pub fn evaluate_computation(
        &mut self,
        env: &CrateEnv,
        computation: Computation,
    ) -> Computation {
        let (result, exhausted) =
            match kernel::program_calculus::evaluate_computation(env, computation) {
                Evaluation::Normal(result) => (result, false),
                Evaluation::OutOfFuel(result) => (result, true),
            };
        self.record(
            if exhausted {
                LogLevel::Warn
            } else {
                LogLevel::Debug
            },
            vec!["program evaluation".into()],
            if exhausted {
                "Program evaluation exhausted its reduction budget".into()
            } else {
                "Program evaluation success".into()
            },
            LogPayload::Computation(result),
        );
        result
    }

    pub fn infer(
        &mut self,
        env: &CrateEnv,
        module: ModuleId,
        ctx: &mut ExpContext,
        exp: Exp,
    ) -> Option<Exp> {
        match CheckSession::new(env, module, ctx).infer_pts(exp) {
            Ok(ty) => {
                self.record(
                    LogLevel::Debug,
                    vec!["infer".into()],
                    "infer success".into(),
                    LogPayload::Exp(ty),
                );
                Some(ty)
            }
            Err(error) => {
                self.record(
                    LogLevel::Error,
                    vec!["infer".into()],
                    format!("infer failed: {error:?}"),
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
        ctx: &mut ExpContext,
        exp: Exp,
    ) -> Option<Sort> {
        match CheckSession::new(env, module, ctx).infer_sort(exp) {
            Ok(sort) => Some(sort),
            Err(error) => {
                self.record(
                    LogLevel::Error,
                    vec!["infer_sort".into()],
                    format!("infer sort failed: {error:?}"),
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
        ctx: &mut ExpContext,
        exp: Exp,
    ) -> Option<ExpJudgement> {
        match CheckSession::new(env, module, ctx).infer_exp_judgement(exp) {
            Ok(judgement) => {
                self.record(
                    LogLevel::Debug,
                    vec!["infer".into()],
                    "Set/Prop inference success".into(),
                    LogPayload::Exp(judgement.ty),
                );
                Some(judgement)
            }
            Err(error) => {
                self.record(
                    LogLevel::Error,
                    vec!["infer".into()],
                    format!("infer failed: {error:?}"),
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
        ctx: &mut ExpContext,
        exp: Exp,
        expected_type: Exp,
    ) -> bool {
        match CheckSession::new(env, module, ctx).check_pts(exp, expected_type) {
            Ok(()) => true,
            Err(error) => {
                self.record(
                    LogLevel::Error,
                    vec!["check".into()],
                    format!("check failed: {error:?}"),
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
        let msg = format!($($arg)*);
        let tags = vec![$($tag.to_string()),*];
        $ctx.record($level, tags, msg, $payload);
    }};
}

#[macro_export]
macro_rules! log_msg {
    ($ctx:expr, $level:expr, [$($tag:expr),*], $($arg:tt)*) => {{
        $crate::log_record!($ctx, $level, [$($tag),*], $crate::logger::LogPayload::Message, $($arg)*);
    }};
}
