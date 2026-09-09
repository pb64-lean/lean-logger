import Loggers
import OpenTelemetry.Context

namespace Loggers.OpenTelemetry

open _root_.OpenTelemetry

private instance : Inhabited AttributeValue := ⟨.empty⟩

private def integer (value : Int) : AttributeValue :=
  if -(2^63 : Int) ≤ value && value < 2^63 then .int value.toInt64
  else .string (toString value)

mutual
  /-- Preserve arbitrary-precision integers exactly when they exceed OTLP int64. -/
  partial def value : LogValue → AttributeValue
    | .null => .empty
    | .str text => .string text
    | .int number => integer number
    | .nat number => integer number
    | .float number => if number.isNaN || number.isInf then .empty else .double number
    | .bool flag => .bool flag
    | .arr entries => .array (entries.map value)
    | .obj entries => .kvlist (bindings entries)

  partial def bindings (entries : Array (String × LogValue)) : Array Attribute :=
    entries.foldl (fun output (key, val) =>
      if key.isEmpty then output else
        (output.filter (·.key != key)).push { key, value := value val }) #[]
end

private def severity : Level → Logs.SeverityNumber
  | .trace => .trace | .debug => .debug | .info => .info | .warn => .warn | .error => .error

private partial def causeValue (cause : Cause) : AttributeValue :=
  .kvlist (#[.string "summary" cause.summary] ++
    (cause.detail.map (fun detail => #[⟨"detail", value detail⟩])).getD #[] ++
    (cause.inner.map (fun inner => #[⟨"inner", causeValue inner⟩])).getD #[])

/-- Conversion consumes a strict event, never application thunks. Physical
source paths are omitted. Context is supplied explicitly at the event boundary. -/
def event (entry : LogEvent) (context : Context := {}) : Logs.Event :=
  let nanoseconds := entry.timestamp.toNanosecondsSinceUnixEpoch.val
  context.correlate {
    timeUnixNano := nanoseconds.toNat.toUInt64
    severityNumber := severity entry.level
    severityText := entry.level.toUpperString
    scope := { name := entry.logger }
    body := some (.string entry.message)
    attributes := #[
      .string "code.namespace" entry.provenance.module.toString,
      .string "code.function.name" entry.provenance.declaration.toString,
      .kvlist "log.context" (bindings entry.context.toArray),
      .kvlist "log.fields" (bindings entry.fields.toArray)
    ] ++ (entry.cause.map (fun cause => #[⟨"exception", causeValue cause⟩])).getD #[]
  }

/-- The appender borrows the destination; closing it flushes but never closes
the shared OTel provider/channel. All export failures are isolated by Logger. -/
def appender (destination : Logs.Logger) (contextOf : LogEvent → Context := fun _ => {})
    (flush : IO Unit := pure ()) : Runtime.AppenderSpec :=
  Runtime.AppenderSpec.custom "opentelemetry" fun _ => pure {
    append := fun entry => destination.failureIsolated.emit (event entry (contextOf entry))
    flush
  }

end Loggers.OpenTelemetry
