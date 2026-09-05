use crate::Log;
use front::logger::{LogLevel, LogPayload, LogRecord};

mod for_kernel;

pub fn log_record_to_log(
    env: &kernel::environment::CrateEnv,
    record: &front::logger::LogRecord,
) -> Log {
    match &record.payload {
        LogPayload::Exp(exp) => Log::Message(format_record(
            record,
            Some(format!("exp = {}", for_kernel::format_exp(env, *exp))),
        )),
        LogPayload::Ctx(ctx) => Log::Message(format_record(
            record,
            Some(format!("ctx = [{}]", for_kernel::format_ctx(env, ctx))),
        )),
        LogPayload::ValueType(ty) => Log::Message(format_record(
            record,
            Some(format!(
                "value type = {}",
                for_kernel::format_value_type(env, *ty)
            )),
        )),
        LogPayload::ComputationType(ty) => Log::Message(format_record(
            record,
            Some(format!(
                "computation type = {}",
                for_kernel::format_computation_type(env, *ty)
            )),
        )),
        LogPayload::Value(value) => Log::Message(format_record(
            record,
            Some(format!("value = {}", for_kernel::format_value(env, *value))),
        )),
        LogPayload::Computation(computation) => Log::Message(format_record(
            record,
            Some(format!(
                "computation = {}",
                for_kernel::format_computation(env, *computation)
            )),
        )),
        LogPayload::ProgramCtx(ctx) => Log::Message(format_record(
            record,
            Some(format!(
                "program ctx = [{}]",
                for_kernel::format_program_ctx(env, ctx)
            )),
        )),
        LogPayload::Message => Log::Message(format_record(record, None)),
        LogPayload::Goals(goals) => {
            let error = if goals
                .iter()
                .any(|goal| matches!(goal.flavor, front::metavariables::MetaFlavor::Implicit))
            {
                front::metavariables::ElaborationError::AmbiguousImplicit(goals.clone())
            } else {
                front::metavariables::ElaborationError::UnsolvedGoals(goals.clone())
            };
            Log::Message(format_record(
                record,
                Some(front::metavariables::format_elaboration_error(env, &error)),
            ))
        }
    }
}

fn format_record(record: &LogRecord, extra: Option<String>) -> String {
    let mut base = format!(
        "{} {}",
        record_prefix(&record.level, &record.tags),
        record.message
    );
    if let Some(extra) = extra
        && !extra.is_empty()
    {
        base.push_str(" | ");
        base.push_str(&extra);
    }
    base
}

fn record_prefix(level: &LogLevel, tags: &[String]) -> String {
    let mut prefix = format!("[{:?}]", level);
    if !tags.is_empty() {
        prefix.push(' ');
        prefix.push('[');
        prefix.push_str(&tags.join(", "));
        prefix.push(']');
    }
    prefix
}
