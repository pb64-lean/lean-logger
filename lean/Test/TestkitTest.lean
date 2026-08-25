import Loggers.Testkit

open Loggers
open Loggers.Testkit
open Std.Time

namespace Test.Testkit

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

private def testManualClock : IO Unit := do
  let initial := Timestamp.ofNanosecondsSinceUnixEpoch 10
  let clock ← ManualClock.new initial
  expectEq (← clock.now) initial "initial manual time"

  let advanced ← clock.advance (Duration.ofNanoseconds 7)
  let expected := Timestamp.ofNanosecondsSinceUnixEpoch 17
  expectEq advanced expected "advanced result"
  expectEq (← clock.now) expected "advanced state"

  let replacement := Timestamp.ofNanosecondsSinceUnixEpoch 100
  clock.set replacement
  expectEq (← clock.now) replacement "replaced manual time"

private def testConcurrentClockAdvance : IO Unit := do
  let clock ← ManualClock.create
  let count := 64
  let tasks ← (List.range count).mapM fun _ =>
    IO.asTask do
      discard <| clock.advance (Duration.ofNanoseconds 1)
  for task in tasks do
    discard <| waitTask task
  expectEq (← clock.now)
    (Timestamp.ofNanosecondsSinceUnixEpoch (.ofNat count))
    "atomic manual-clock advances"

private def event (message : String) : LogEvent :=
  { timestamp := 0
    level := .info
    logger := "testkit"
    provenance := {
      declaration := `Test.Testkit.event
      module := `Test.Testkit
    }
    message }

private def testCapture : IO Unit := do
  let capture ← Capture.new
  capture.append (event "first")
  let firstSnapshot ← capture.events
  capture.append (event "second")
  expectEq (firstSnapshot.map fun captured => captured.message)
    #["first"] "snapshot stability"
  let secondSnapshot ← capture.events
  expectEq (secondSnapshot.map fun captured => captured.message)
    #["first", "second"] "capture order"
  capture.clear
  expectEq (← capture.events) #[] "capture clear"

private def testConcurrentCapture : IO Unit := do
  let capture ← Capture.create
  let count := 64
  let tasks ← (List.range count).mapM fun index =>
    IO.asTask do
      capture.sink (event s!"event-{index}")
  for task in tasks do
    discard <| waitTask task
  let events ← capture.snapshot
  expectEq events.size count "concurrent capture cardinality"
  for index in List.range count do
    expect (events.any fun captured => captured.message == s!"event-{index}")
      s!"concurrent capture lost event-{index}"

private def testGate : IO Unit := do
  let gate ← Gate.new
  let completed ← IO.mkRef false
  let worker ← IO.asTask do
    gate.enter
    completed.set true

  gate.waitEntered
  expect (!(← completed.get)) "worker crossed a closed gate"
  gate.release
  gate.release
  discard <| waitTask worker
  expect (← completed.get) "worker did not cross an open gate"

private def testReleaseBeforeEntry : IO Unit := do
  let gate ← Gate.create
  gate.release
  let worker ← IO.asTask gate.enter
  gate.waitEntered
  discard <| waitTask worker

def runAll : IO Unit := do
  testManualClock
  testConcurrentClockAdvance
  testCapture
  testConcurrentCapture
  testGate
  testReleaseBeforeEntry

end Test.Testkit

def main : IO Unit :=
  Test.Testkit.runAll
