import Loggers.OpenTelemetry
import Std.Sync.Mutex

private def check (ok : Bool) (detail : String) : IO Unit :=
  unless ok do throw (IO.userError detail)

def main : IO Unit := do
  let output ← Std.Mutex.new (#[] : Array OpenTelemetry.Logs.Event)
  let flushes ← Std.Mutex.new (0 : Nat)
  let some span := OpenTelemetry.SpanContext.parse?
      "00-0af7651916cd43dd8448eb211c80319c-b7ad6b7169203331-01"
    | throw (IO.userError "invalid test traceparent")
  let context := OpenTelemetry.Context.root.withSpan span
  let spec := Loggers.OpenTelemetry.appender
    ⟨fun entry => output.atomically (modify (·.push entry))⟩ (fun _ => context)
    (flushes.atomically (modify (· + 1)))
  let started ← spec.start {}
  started.append {
    timestamp := Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch 123
    level := .warn
    logger := "consumer"
    provenance := { declaration := `handler, module := `Service }
    message := "message"
    fields := [("answer", .nat 42), ("answer", .nat 43)]
  }
  started.close
  let events ← output.atomically get
  let some result := events[0]? | throw (IO.userError "no event exported")
  check (result.timeUnixNano == 123 && result.severityNumber == .warn &&
    result.traceId == span.traceId && result.spanId == span.spanId) "event conversion"
  check ((← flushes.atomically get) == 1) "borrowed provider flush"
  check (Loggers.OpenTelemetry.value (.nat (2^64)) == .string "18446744073709551616") "integer precision"
  check (Loggers.OpenTelemetry.bindings #[("x", .nat 1), ("x", .nat 2)] ==
    #[OpenTelemetry.Attribute.int "x" 2]) "last-wins unique field keys"
  let failing ← (Loggers.OpenTelemetry.appender ⟨fun _ => throw (IO.userError "failure")⟩).start {}
  failing.append {
    timestamp := Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch 0
    level := .info, logger := "test", provenance := { declaration := `test, module := `Test }, message := "safe"
  }
  failing.close
  IO.println "lean-logger OpenTelemetry integration passed"
