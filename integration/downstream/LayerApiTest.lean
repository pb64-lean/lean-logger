import Loggers.Core
import Loggers.Format
import Loggers.Runtime
import Loggers.Testkit

open Loggers
open Loggers.Format
open Loggers.Runtime
open Loggers.Testkit

private def fail (message : String) : IO α :=
  throw <| IO.userError message

private def event (timestamp : Std.Time.Timestamp) : LogEvent := {
  timestamp
  level := .info
  logger := "Layer.Consumer"
  provenance := {
    declaration := `event
    module := `LayerApiTest
  }
  message := "layer event"
}

def main : IO Unit := do
  let clock ← ManualClock.new 17
  let capture ← Capture.new
  let child : StartedAppender := {
    name := "layer-capture"
    append := capture.append
  }
  let appender ← AsyncAppender.start child
    (options := { capacity := 2, overflowPolicy := .block })
  unless (← appender.offer (event (← clock.now))).isAdmitted do
    fail "layer appender rejected an event"
  appender.close
  let captured ← capture.events
  let some logged := captured[0]?
    | fail "layer capture was empty"
  unless captured.size == 1 && (json logged).contains "\"layer event\"" do
    fail "layer targets produced an unexpected event"
