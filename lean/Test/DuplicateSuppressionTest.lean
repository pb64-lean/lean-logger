import Std.Sync.Mutex
import Loggers.Runtime.AsyncAppender
import Loggers.Runtime.DuplicateSuppression
import Loggers.Testkit

open Loggers
open Loggers.Runtime
open Loggers.Testkit
open Std.Time

namespace Test.DuplicateSuppression

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def expect (condition : Bool) (message : String) : IO Unit :=
  unless condition do fail message

private def expectEq [BEq α] [Repr α] (actual expected : α) (label : String) : IO Unit :=
  unless actual == expected do
    fail s!"{label}: expected {repr expected}, got {repr actual}"

private def waitTask (task : Task (Except IO.Error α)) : IO α := do
  match ← IO.wait task with
  | .ok value => pure value
  | .error error => throw error

private partial def waitUntil (condition : IO Bool) : IO Unit := do
  if ← condition then
    pure ()
  else
    waitUntil condition

private def expectError (action : IO Unit) (fragment : String) (label : String) : IO Unit := do
  try
    action
    fail s!"{label}: expected failure"
  catch error =>
    expect ((toString error).contains fragment)
      s!"{label}: unexpected error: {error}"

private def timestampAt (nanoseconds : Nat) : Timestamp :=
  Timestamp.ofNanosecondsSinceUnixEpoch (.ofNat nanoseconds)

private def siteA : Provenance := {
  declaration := `Test.DuplicateSuppression.siteA
  module := `Test.DuplicateSuppression
}

private def siteB : Provenance := {
  declaration := `Test.DuplicateSuppression.siteB
  module := `Test.DuplicateSuppression
}

private def event
    (message : String)
    (timestamp : Timestamp := timestampAt 0)
    (logger : String := "suppression-test")
    (provenance : Provenance := siteA)
    (level : Level := .info)
    (cause : Option Cause := none)
    (context : List (String × LogValue) := [])
    (eventFields : List (String × LogValue) := []) : LogEvent := {
  timestamp
  level
  logger
  provenance
  message
  cause
  context
  «fields» := eventFields
}

private def messages (capture : Capture) : IO (Array String) := do
  return (← capture.events).map fun captured => captured.message

private def field? (logged : LogEvent) (name : String) : Option LogValue :=
  (logged.fields.find? fun field => field.1 == name).map (·.2)

private def expectPhase (logged : LogEvent) (phase label : String) : IO Unit :=
  expectEq (field? logged "suppressionPhase") (some (.str phase)) label

private def expectSuppressedCount (logged : LogEvent) (count : Nat) (label : String) : IO Unit :=
  expectEq (field? logged "suppressedCount") (some (.nat count)) label

private def captureSuppressor
    (options : DuplicateSuppressionOptions)
    (services : RuntimeServices := {}) : IO (DuplicateSuppressor × Capture) := do
  let capture ← Capture.new
  let child : StartedAppender := {
    name := "capture"
    append := capture.append
  }
  pure (← DuplicateSuppressor.start child services options, capture)

private def expectValidationError
    (options : DuplicateSuppressionOptions)
    (expected : DuplicateSuppressionConfigError)
    (label : String) : IO Unit :=
  match options.validate with
  | .error actual => expectEq actual expected label
  | .ok () => fail s!"{label}: expected validation failure"

private def testValidation : IO Unit := do
  expectValidationError
    { allowedPerWindow := 0 }
    .zeroAllowedPerWindow
    "zero allowance"
  expectValidationError
    { window := Duration.ofNanoseconds 0 }
    .nonPositiveWindow
    "zero window"
  expectValidationError
    { window := Duration.ofNanoseconds (-1) }
    .nonPositiveWindow
    "negative window"
  expectValidationError
    { capacity := 0 }
    .zeroCapacity
    "zero capacity"
  expectValidationError
    { stableFields := [""] }
    (.invalidStableField "")
    "invalid stable field"
  expectValidationError
    { stableFields := ["tenant", "tenant"] }
    (.duplicateStableField "tenant")
    "duplicate stable field"

  let child : StartedAppender := {
    name := "invalid"
    append := fun _ => pure ()
  }
  expectError
    (discard <| DuplicateSuppressor.start child (options := { capacity := 0 }))
    "capacity must be positive"
    "invalid start"

private def testStableKeySelection : IO Unit := do
  let (suppressor, capture) ← captureSuppressor {
    allowedPerWindow := 1
    window := Duration.ofNanoseconds 100
    capacity := 4
    stableFields := ["tenant"]
  }
  suppressor.append <| event "first"
    (context := [("requestId", .str "request-a")])
    (eventFields := [("tenant", .str "a"), ("attempt", .nat 1)])
  suppressor.append <| event "second"
    (timestamp := timestampAt 1)
    (context := [("requestId", .str "request-b")])
    (eventFields := [("tenant", .str "a"), ("attempt", .nat 2)])
  suppressor.append <| event "third"
    (timestamp := timestampAt 2)
    (context := [("requestId", .str "request-c")])
    (eventFields := [("tenant", .str "b"), ("attempt", .nat 2)])

  expectEq (← messages capture)
    #["first", "duplicate event suppression started", "third"]
    "stable-field key selection"
  let captured ← capture.events
  expectPhase captured[1]! "start" "suppression-start phase"
  let stats ← suppressor.stats
  expectEq stats.trackedKeys 2 "stable-field tracked keys"
  expectEq stats.admitted 2 "stable-field admissions"
  expectEq stats.suppressed 1 "context and nonallowlisted exclusion"
  suppressor.close

private def testTopLevelKeyDimensions : IO Unit := do
  let (suppressor, capture) ← captureSuppressor {
    allowedPerWindow := 1
    window := Duration.ofNanoseconds 100
    capacity := 8
  }
  suppressor.append <| event "base"
  suppressor.append <| event "logger" (timestamp := timestampAt 1) (logger := "other")
  suppressor.append <| event "provenance" (timestamp := timestampAt 2) (provenance := siteB)
  suppressor.append <| event "level" (timestamp := timestampAt 3) (level := .warn)
  suppressor.append <| event "cause-one" (timestamp := timestampAt 4)
    (cause := some { summary := "one", detail := some (.str "detail-a") })
  suppressor.append <| event "cause-two" (timestamp := timestampAt 5)
    (cause := some { summary := "two", detail := some (.str "detail-a") })
  suppressor.append <| event "same-cause-summary" (timestamp := timestampAt 6)
    (cause := some { summary := "two", detail := some (.str "detail-b") })

  expectEq (← messages capture) #[
    "base", "logger", "provenance", "level", "cause-one", "cause-two",
    "duplicate event suppression started"
  ] "top-level key dimensions"
  let stats ← suppressor.stats
  expectEq stats.trackedKeys 6 "top-level tracked keys"
  expectEq stats.admitted 6 "top-level distinct admissions"
  expectEq stats.suppressed 1 "cause-detail exclusion"
  suppressor.close

private def testWindowThresholdAndResumption : IO Unit := do
  let (suppressor, capture) ← captureSuppressor {
    allowedPerWindow := 2
    window := Duration.ofNanoseconds 10
    capacity := 2
  }
  suppressor.append <| event "first" (timestamp := timestampAt 0)
  suppressor.append <| event "second" (timestamp := timestampAt 1)
  suppressor.append <| event "third" (timestamp := timestampAt 2)
  suppressor.append <| event "fourth" (timestamp := timestampAt 3)
  suppressor.append <| event "resumed" (timestamp := timestampAt 10)

  expectEq (← messages capture) #[
    "first",
    "second",
    "duplicate event suppression started",
    "duplicate event suppression summary",
    "resumed"
  ] "threshold and timestamp window"
  let captured ← capture.events
  expectPhase captured[2]! "start" "first denial marker"
  expectPhase captured[3]! "resumed" "resumption phase"
  expectSuppressedCount captured[3]! 2 "resumption count"
  let stats ← suppressor.stats
  expectEq stats.admitted 3 "window admissions"
  expectEq stats.suppressed 2 "window suppressions"
  expectEq stats.suppressionStarts 1 "single suppression-start record"
  expectEq stats.summaries 1 "resumption summary count"
  suppressor.close

private def testDeterministicLruEviction : IO Unit := do
  let (suppressor, capture) ← captureSuppressor {
    allowedPerWindow := 1
    window := Duration.ofNanoseconds 100
    capacity := 2
    stableFields := ["key"]
  }
  let keyed (message key : String) (time : Nat) :=
    event message (timestamp := timestampAt time) (eventFields := [("key", .str key)])
  suppressor.append <| keyed "a" "a" 0
  suppressor.append <| keyed "b" "b" 1
  suppressor.append <| keyed "a-duplicate" "a" 2
  suppressor.append <| keyed "c" "c" 3
  suppressor.append <| keyed "b-again" "b" 4

  expectEq (← messages capture) #[
    "a",
    "b",
    "duplicate event suppression started",
    "c",
    "duplicate event suppression summary",
    "b-again"
  ] "deterministic LRU delivery"
  let captured ← capture.events
  expectPhase captured[4]! "evicted" "eviction summary phase"
  expectSuppressedCount captured[4]! 1 "eviction summary count"
  let stats ← suppressor.stats
  expectEq stats.trackedKeys 2 "bounded table size"
  expectEq stats.evictions 2 "LRU eviction count"
  expectEq stats.summaries 1 "eviction summary counter"
  suppressor.close

private def testConcurrentCloseAndFinalCounts : IO Unit := do
  let capture ← Capture.new
  let closeGate ← Gate.new
  let closeCalls ← IO.mkRef 0
  let child : StartedAppender := {
    name := "close"
    append := capture.append
    close := do
      closeCalls.modify (· + 1)
      closeGate.enter
  }
  let suppressor ← DuplicateSuppressor.start child (options := {
    allowedPerWindow := 1
    window := Duration.ofNanoseconds 100
    capacity := 2
    stableFields := ["key"]
  })
  let keyed (message key : String) (time : Nat) :=
    event message (timestamp := timestampAt time) (eventFields := [("key", .str key)])
  suppressor.append <| keyed "a" "a" 0
  suppressor.append <| keyed "a-denied-one" "a" 1
  suppressor.append <| keyed "a-denied-two" "a" 2
  suppressor.append <| keyed "b" "b" 3
  suppressor.append <| keyed "b-denied" "b" 4

  let closeOne ← IO.asTask suppressor.close
  let closeTwo ← IO.asTask suppressor.close
  closeGate.waitEntered
  expect (!(← IO.hasFinished closeOne)) "owner close returned before child retirement"
  expect (!(← IO.hasFinished closeTwo)) "concurrent close did not await shared result"
  expectEq (← messages capture) #[
    "a",
    "duplicate event suppression started",
    "b",
    "duplicate event suppression started",
    "duplicate event suppression summary",
    "duplicate event suppression summary"
  ] "final close summaries"
  let captured ← capture.events
  expectPhase captured[4]! "closed" "LRU close-summary phase"
  expectSuppressedCount captured[4]! 2 "LRU close-summary count"
  expectPhase captured[5]! "closed" "MRU close-summary phase"
  expectSuppressedCount captured[5]! 1 "MRU close-summary count"

  closeGate.release
  discard <| waitTask closeOne
  discard <| waitTask closeTwo
  suppressor.close
  expectEq (← closeCalls.get) 1 "exact child close"
  expectEq (← (suppressor.stats)).phase .closed "closed phase"
  expectEq (← (suppressor.stats)).trackedKeys 0 "closed table cleared"
  expectEq (← messages capture).size 6 "idempotent final summaries"

private def testFailedCloseResult : IO Unit := do
  let closeCalls ← IO.mkRef 0
  let child : StartedAppender := {
    name := "failed-close"
    append := fun _ => pure ()
    close := do
      closeCalls.modify (· + 1)
      throw (IO.userError "close failed")
  }
  let suppressor ← DuplicateSuppressor.start child
  expectError suppressor.close "close failed" "first failed close"
  expectError suppressor.close "close failed" "repeated failed close"
  let stats ← suppressor.stats
  expectEq stats.phase .failed "failed close phase"
  expectEq stats.closeFailures 1 "failed close counter"
  expectEq (← closeCalls.get) 1 "shared failed close result"

private def testNonrecursiveDiagnostics : IO Unit := do
  let diagnosticCalls ← IO.mkRef 0
  let services : RuntimeServices := {
    diagnostic := fun diagnostic => do
      diagnosticCalls.modify (· + 1)
      throw <| IO.userError s!"diagnostic rejected: {diagnostic.message}"
  }
  let child : StartedAppender := {
    name := "failing-child"
    append := fun _ => throw (IO.userError "append failed")
  }
  let suppressor ← DuplicateSuppressor.start child services (options := {
    allowedPerWindow := 1
    window := Duration.ofNanoseconds 100
    capacity := 1
  })
  suppressor.append <| event "first"
  suppressor.append <| event "denied" (timestamp := timestampAt 1)
  suppressor.close
  let stats ← suppressor.stats
  expectEq stats.childFailures 3 "isolated child failures"
  expectEq (← diagnosticCalls.get) 3 "nonrecursive diagnostic count"
  expectEq stats.phase .closed "append failures do not fail lifecycle"

private def testBlockingAsyncComposition : IO Unit := do
  let gate ← Gate.new
  let capture ← Capture.new
  let terminal : StartedAppender := {
    name := "blocking-terminal"
    append := fun logged => do
      if logged.message == "first" then gate.enter
      capture.append logged
  }
  let async ← AsyncAppender.start terminal
    (options := { capacity := 1, overflowPolicy := .block })
  let suppressor ← DuplicateSuppressor.start async.asStarted (options := {
    allowedPerWindow := 100
    window := Duration.ofNanoseconds 100
    capacity := 1
  })
  suppressor.append <| event "first"
  gate.waitEntered
  suppressor.append <| event "second" (timestamp := timestampAt 1)
  let producer ← IO.asTask (do
    suppressor.append <| event "third" (timestamp := timestampAt 2)) .dedicated
  waitUntil do
    let stats ← async.stats
    pure (stats.offered == 3)
  expect (!(← IO.hasFinished producer)) "producer did not block at full async child"

  let closer ← IO.asTask suppressor.close
  discard <| waitTask producer
  expect (!(← IO.hasFinished closer)) "close crossed the blocked terminal child"
  gate.release
  discard <| waitTask closer
  expectEq (← messages capture) #["first", "second"] "async close drain"
  expectEq (← async.stats).rejected 1 "blocked child admission wake"
  expectEq (← suppressor.stats).childFailures 1 "rejected child delivery accounting"
  expectEq (← suppressor.stats).phase .closed "composed close phase"

private def testAppenderDecoration : IO Unit := do
  let capture ← Capture.new
  let spec := (AppenderSpec.custom "decorated" fun _ => pure {
    append := capture.append
  }).suppressDuplicates {
    allowedPerWindow := 1
    window := Duration.ofNanoseconds 100
    capacity := 1
  }
  let appender ← spec.start {}
  appender.append <| event "first"
  appender.append <| event "second" (timestamp := timestampAt 1)
  appender.close
  expectEq (← messages capture) #[
    "first",
    "duplicate event suppression started",
    "duplicate event suppression summary"
  ] "appender-spec decoration"
  let captured ← capture.events
  expectPhase captured[2]! "closed" "decorator final summary"
  expectSuppressedCount captured[2]! 1 "decorator final count"

def runAll : IO Unit := do
  testValidation
  testStableKeySelection
  testTopLevelKeyDimensions
  testWindowThresholdAndResumption
  testDeterministicLruEviction
  testConcurrentCloseAndFinalCounts
  testFailedCloseResult
  testNonrecursiveDiagnostics
  testBlockingAsyncComposition
  testAppenderDecoration

end Test.DuplicateSuppression

def main : IO Unit :=
  Test.DuplicateSuppression.runAll
