import Loggers

open Loggers
open Loggers.Format
open Loggers.Runtime

private def fail (message : String) : IO α :=
  throw <| IO.userError message

private def program : Logger [] Unit :=
  pushNew "requestId" "r-17" do
    log! .info "request accepted"
      (fields := fields! ["outcome" := "ok", "durationMs" := (9 : Nat)])

def main : IO Unit := do
  let events ← IO.mkRef (#[] : Array LogEvent)
  let capture := AppenderSpec.custom "capture" fun _ => pure {
    append := fun event => events.modify (·.push event)
  }
  Loggers.run {
    appenders := #[capture]
    now := pure (Std.Time.Timestamp.ofMillisecondsSinceUnixEpoch 1234)
  } program
  let captured ← events.get
  let some event := captured[0]?
    | fail "the public runtime did not emit an event"
  unless captured.size == 1 do
    fail s!"expected one event, got {captured.size}"
  unless event.context == [("requestId", .str "r-17")] do
    fail "typed context did not survive the public facade"
  unless event.fields == [("outcome", .str "ok"), ("durationMs", .nat 9)] do
    fail "typed event fields did not survive the public facade"
  let rendered := json event
  unless rendered.contains "\"context\":{\"requestId\":\"r-17\"}" do
    fail "JSON did not preserve the context namespace"
  unless rendered.contains "\"fields\":{\"outcome\":\"ok\",\"durationMs\":9}" do
    fail "JSON did not preserve the event-field namespace"
  let layout := pattern% (contextSchema := ["requestId"])
    (fieldSchema := ["outcome", "durationMs"])
    "%level %X{requestId} %field{outcome} %msg"
  unless layout event == "INFO r-17 ok request accepted" do
    fail "the compiled pattern produced unexpected output"
