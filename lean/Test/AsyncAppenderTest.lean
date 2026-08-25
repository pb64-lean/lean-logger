import Std.Sync.Mutex
import Loggers.Runtime.AsyncAppender
import Loggers.Runtime.Lifecycle
import Loggers.Testkit

open Loggers
open Loggers.Runtime
open Loggers.Testkit

namespace Test.AsyncAppender

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

private def event (message : String) : LogEvent :=
  { timestamp := 0
    level := .info
    logger := "async-test"
    provenance := {
      declaration := `Test.AsyncAppender.event
      module := `Test.AsyncAppender
    }
    message }

private def messages (capture : Capture) : IO (Array String) := do
  return (← capture.events).map fun captured => captured.message

private def testCapacityValidation : IO Unit := do
  match ({ capacity := 0 } : AsyncOptions).validate with
  | .error .zeroCapacity => pure ()
  | .ok () => fail "zero capacity validation: expected rejection"
  let child : StartedAppender := {
    name := "invalid"
    append := fun _ => pure ()
  }
  expectError
    (discard <| AsyncAppender.start child (options := { capacity := 0 }))
    "capacity must be positive"
    "zero-capacity start"

private def startGated
    (policy : OverflowPolicy) : IO (AsyncAppender × Gate × Capture) := do
  let gate ← Gate.new
  let capture ← Capture.new
  let child : StartedAppender := {
    name := "overflow"
    append := fun logged => do
      if logged.message == "first" then gate.enter
      capture.append logged
  }
  let appender ← AsyncAppender.start child
    (options := { capacity := 1, overflowPolicy := policy })
  pure (appender, gate, capture)

private def testDropNewest : IO Unit := do
  let (appender, gate, capture) ← startGated .dropNewest
  expectEq (← appender.offer (event "first")) .admitted "first admission"
  gate.waitEntered
  expectEq (← appender.offer (event "second")) .admitted "second admission"
  expectEq (← appender.offer (event "third")) .droppedNewest "drop-newest admission"
  gate.release
  appender.flush
  expectEq (← messages capture) #["first", "second"] "drop-newest delivery"
  let stats ← appender.stats
  expectEq stats.offered 3 "drop-newest offered"
  expectEq stats.admitted 2 "drop-newest admitted"
  expectEq stats.delivered 2 "drop-newest delivered"
  expectEq stats.droppedNewest 1 "drop-newest counter"
  appender.close

private def testDropOldest : IO Unit := do
  let (appender, gate, capture) ← startGated .dropOldest
  expectEq (← appender.offer (event "first")) .admitted "first admission"
  gate.waitEntered
  expectEq (← appender.offer (event "second")) .admitted "second admission"
  expectEq (← appender.offer (event "third")) .admittedAfterDropOldest
    "drop-oldest admission"
  gate.release
  appender.flush
  expectEq (← messages capture) #["first", "third"] "drop-oldest delivery"
  let stats ← appender.stats
  expectEq stats.offered 3 "drop-oldest offered"
  expectEq stats.admitted 3 "drop-oldest admitted"
  expectEq stats.delivered 2 "drop-oldest delivered"
  expectEq stats.droppedOldest 1 "drop-oldest counter"
  appender.close

private def testDropOldestRespectsFlushFence : IO Unit := do
  let gate ← Gate.new
  let operations ← Std.Mutex.new (#[] : Array String)
  let record (operation : String) : IO Unit :=
    operations.atomically do modify (·.push operation)
  let child : StartedAppender := {
    name := "flush-fenced-overflow"
    append := fun logged => do
      if logged.message == "first" then gate.enter
      record s!"append:{logged.message}"
    flush := record "flush"
  }
  let appender ← AsyncAppender.start child
    (options := { capacity := 1, overflowPolicy := .dropOldest })
  expectEq (← appender.offer (event "first")) .admitted "fence first admission"
  gate.waitEntered
  expectEq (← appender.offer (event "A")) .admitted "fence protected admission"
  let flushing ← IO.asTask appender.flush
  waitUntil do
    let stats ← appender.stats
    pure (stats.pendingFlushes == 1)
  expectEq (← appender.offer (event "C")) .droppedNewest
    "flush-fenced drop-oldest admission"
  let beforeRelease ← appender.stats
  expectEq beforeRelease.droppedNewest 1 "flush-fenced newest counter"
  expectEq beforeRelease.droppedOldest 0 "flush-fenced oldest counter"
  gate.release
  discard <| waitTask flushing
  expectEq (← operations.atomically get) #["append:first", "append:A", "flush"]
    "flush fence preserves earlier event"
  appender.close

private def testBlockingAdmission : IO Unit := do
  let (appender, gate, capture) ← startGated .block
  expectEq (← appender.offer (event "first")) .admitted "first admission"
  gate.waitEntered
  expectEq (← appender.offer (event "second")) .admitted "second admission"
  let producer ← IO.asTask <| appender.offer (event "third")
  waitUntil do
    let stats ← appender.stats
    pure (stats.offered == 3)
  expect (!(← IO.hasFinished producer)) "full blocking admission completed before capacity opened"
  gate.release
  expectEq (← waitTask producer) .admitted "unblocked admission"
  appender.flush
  expectEq (← messages capture) #["first", "second", "third"] "blocking FIFO delivery"
  appender.close

private def testCloseFencesAndWakes : IO Unit := do
  let (appender, gate, _) ← startGated .block
  expectEq (← appender.offer (event "first")) .admitted "first admission"
  gate.waitEntered
  expectEq (← appender.offer (event "second")) .admitted "second admission"
  let producer ← IO.asTask <| appender.offer (event "third")
  waitUntil do
    let stats ← appender.stats
    pure (stats.offered == 3)
  expect (!(← IO.hasFinished producer)) "full producer was not blocked before close"
  let closer ← IO.asTask appender.close
  expectEq (← waitTask producer) (.rejected .closing) "close admission fence"
  gate.release
  discard <| waitTask closer
  let stats ← appender.stats
  expectEq stats.phase .closed "closed phase"
  expectEq stats.rejected 1 "close rejection counter"
  expectEq (← appender.offer (event "late")) (.rejected .closed) "closed rejection"

private def testFlushBarrier : IO Unit := do
  let gate ← Gate.new
  let operations ← Std.Mutex.new (#[] : Array String)
  let record (operation : String) : IO Unit :=
    operations.atomically do modify (·.push operation)
  let child : StartedAppender := {
    name := "barrier"
    append := fun logged => do
      if logged.message == "first" then gate.enter
      record s!"append:{logged.message}"
    flush := record "flush"
    close := record "close"
  }
  let appender ← AsyncAppender.start child (options := { capacity := 2 })
  discard <| appender.offer (event "first")
  gate.waitEntered
  discard <| appender.offer (event "second")
  let flushing ← IO.asTask appender.flush
  expect (!(← IO.hasFinished flushing)) "flush crossed an earlier blocked append"
  gate.release
  discard <| waitTask flushing
  let beforeClose ← operations.atomically get
  expectEq beforeClose #["append:first", "append:second", "flush"]
    "worker-ordered flush"
  appender.close

private def testFlushFailureIsolation : IO Unit := do
  let flushCalls ← IO.mkRef 0
  let diagnosticCalls ← IO.mkRef 0
  let services : RuntimeServices := {
    diagnostic := fun _ => diagnosticCalls.modify (· + 1)
  }
  let child : StartedAppender := {
    name := "flush-failure"
    append := fun _ => pure ()
    flush := do
      let count ← flushCalls.get
      flushCalls.set (count + 1)
      if count == 0 then throw (IO.userError "first flush failed")
  }
  let appender ← AsyncAppender.start child services
  discard <| appender.offer (event "before")
  expectError appender.flush "first flush failed" "flush barrier failure"
  discard <| appender.offer (event "after")
  appender.flush
  let stats ← appender.stats
  expectEq stats.delivered 2 "delivery after flush failure"
  expectEq stats.flushFailures 1 "flush failure counter"
  expectEq (← diagnosticCalls.get) 0 "explicit flush failure diagnostics"
  appender.close

private def testChildFailureIsolation : IO Unit := do
  let capture ← Capture.new
  let diagnosticCalls ← IO.mkRef 0
  let services : RuntimeServices := {
    diagnostic := fun diagnostic => do
      diagnosticCalls.modify (· + 1)
      throw <| IO.userError s!"diagnostic rejected: {diagnostic.message}"
  }
  let child : StartedAppender := {
    name := "child-failure"
    append := fun logged =>
      if logged.message == "bad" then
        throw (IO.userError "child rejected event")
      else
        capture.append logged
  }
  let appender ← AsyncAppender.start child services
  discard <| appender.offer (event "bad")
  discard <| appender.offer (event "good")
  appender.flush
  expectEq (← messages capture) #["good"] "delivery after child failure"
  let stats ← appender.stats
  expectEq stats.appendFailures 1 "child failure counter"
  expectEq stats.delivered 1 "successful delivery counter"
  expectEq (← diagnosticCalls.get) 1 "nonrecursive diagnostic count"
  appender.close

private def testConcurrentCloseAndExactJoin : IO Unit := do
  let capture ← Capture.new
  let closeGate ← Gate.new
  let flushCalls ← IO.mkRef 0
  let closeCalls ← IO.mkRef 0
  let child : StartedAppender := {
    name := "close"
    append := capture.append
    close := do
      flushCalls.modify (· + 1)
      closeCalls.modify (· + 1)
      closeGate.enter
  }
  let appender ← AsyncAppender.start child (options := { capacity := 2 })
  discard <| appender.offer (event "first")
  discard <| appender.offer (event "second")
  let closeOne ← IO.asTask appender.close
  let closeTwo ← IO.asTask appender.close
  closeGate.waitEntered
  expect (!(← IO.hasFinished closeOne)) "first close returned before child retirement"
  expect (!(← IO.hasFinished closeTwo)) "concurrent close did not share worker retirement"
  expectEq (← messages capture) #["first", "second"] "close drain"
  closeGate.release
  discard <| waitTask closeOne
  discard <| waitTask closeTwo
  appender.close
  expectEq (← flushCalls.get) 1 "exact shutdown flush"
  expectEq (← closeCalls.get) 1 "exact child close"
  expectEq (← appender.stats).phase .closed "joined closed phase"

private def testFailedCloseResult : IO Unit := do
  let closeCalls ← IO.mkRef 0
  let diagnosticCalls ← IO.mkRef 0
  let services : RuntimeServices := {
    diagnostic := fun _ => diagnosticCalls.modify (· + 1)
  }
  let child : StartedAppender := {
    name := "failed-close"
    append := fun _ => pure ()
    close := do
      closeCalls.modify (· + 1)
      throw (IO.userError "close failed")
  }
  let appender ← AsyncAppender.start child services
  expectError appender.close "close failed" "first failed close"
  expectEq (← appender.stats).phase .failed "failed phase"
  expectEq (← appender.offer (event "late")) (.rejected .failed) "failed rejection"
  expectError appender.close "close failed" "repeated failed close"
  expectEq (← closeCalls.get) 1 "shared failed close result"
  expectEq (← appender.stats).closeFailures 1 "close failure counter"
  expectEq (← diagnosticCalls.get) 0 "explicit close failure diagnostics"

private def testRuntimeReportsLifecycleFailuresOnce : IO Unit := do
  let flushDiagnostics ← IO.mkRef ([] : List Diagnostic)
  let flushCalls ← IO.mkRef 0
  let flushSpec := (AppenderSpec.custom "runtime-flush-failure" (fun _ => pure {
    append := fun _ => pure ()
    flush := do
      let count ← flushCalls.get
      flushCalls.set (count + 1)
      if count == 0 then throw (IO.userError "runtime flush failed")
  })).async
  let flushRuntime ← ({
    appenders := #[flushSpec]
    services := {
      diagnostic := fun diagnostic => flushDiagnostics.modify (· ++ [diagnostic])
    }
  } : Loggers.LogConfig).start
  expectError flushRuntime.flush "runtime flush failed" "runtime async flush failure"
  match ← flushDiagnostics.get with
  | [diagnostic] => expectEq diagnostic.operation .flush "runtime flush diagnostic"
  | diagnostics => fail s!"runtime flush diagnostics: expected one, got {diagnostics.length}"
  flushRuntime.close
  expectEq (← flushDiagnostics.get).length 1 "runtime flush diagnostic count after close"

  let closeDiagnostics ← IO.mkRef ([] : List Diagnostic)
  let closeSpec := (AppenderSpec.custom "runtime-close-failure" (fun _ => pure {
    append := fun _ => pure ()
    close := throw (IO.userError "runtime close failed")
  })).async
  let closeRuntime ← ({
    appenders := #[closeSpec]
    services := {
      diagnostic := fun diagnostic => closeDiagnostics.modify (· ++ [diagnostic])
    }
  } : Loggers.LogConfig).start
  expectError closeRuntime.close "runtime close failed" "runtime async close failure"
  expectError closeRuntime.close "runtime close failed" "repeated runtime async close failure"
  match ← closeDiagnostics.get with
  | [diagnostic] => expectEq diagnostic.operation .close "runtime close diagnostic"
  | diagnostics => fail s!"runtime close diagnostics: expected one, got {diagnostics.length}"

private def testAppenderDecoration : IO Unit := do
  let capture ← Capture.new
  let spec := (AppenderSpec.custom "decorated" fun _ => pure {
    append := capture.append
  }).async { capacity := 2 }
  let appender ← spec.start {}
  appender.append (event "decorated")
  appender.flush
  appender.close
  expectEq (← messages capture) #["decorated"] "appender-spec decoration"

def runAll : IO Unit := do
  testCapacityValidation
  testDropNewest
  testDropOldest
  testDropOldestRespectsFlushFence
  testBlockingAdmission
  testCloseFencesAndWakes
  testFlushBarrier
  testFlushFailureIsolation
  testChildFailureIsolation
  testConcurrentCloseAndExactJoin
  testFailedCloseResult
  testRuntimeReportsLifecycleFailuresOnce
  testAppenderDecoration

end Test.AsyncAppender

def main : IO Unit :=
  Test.AsyncAppender.runAll
