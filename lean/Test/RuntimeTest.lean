import Init.System.Promise
import Loggers.Runtime.Lifecycle

open Loggers
open Loggers.Runtime

namespace Test.Runtime

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

private def awaitUnit (label : String) (promise : IO.Promise Unit) : IO Unit := do
  match ← IO.wait promise.result? with
  | some () => pure ()
  | none => fail s!"{label} promise was dropped"

private def event
    (message : String)
    (logger : String := "Test.Runtime")
    (level : Level := .info) : LogEvent :=
  { timestamp := 0
    level
    logger
    provenance := {
      declaration := `Test.Runtime.event
      module := `Test.Runtime
    }
    message }

private def compiledLevels
    (root : Level)
    (overrides : List (String × Level)) : IO CompiledLevels :=
  match compileLevels root overrides with
  | .ok levels => pure levels
  | .error error => fail s!"unexpected level configuration error: {error}"

private def testHierarchicalLevels : IO Unit := do
  let levels ← compiledLevels .info [
    ("App", .debug),
    ("App.Http", .warn),
    ("App.Http.Client", .error)
  ]
  expectEq (levels.effectiveLevel "Other") .info "root level"
  expectEq (levels.effectiveLevel "App.Worker") .debug "parent level"
  expectEq (levels.effectiveLevel "App.Http.Server") .warn "longest prefix"
  expectEq (levels.effectiveLevel "App.Http.Client.Call") .error "deepest prefix"
  expectEq (levels.effectiveLevel "App.Httpish") .debug "segment boundary"
  expect (levels.enabled "App.Http" .error) "higher level must be enabled"
  expect (!levels.enabled "App.Http" .info) "lower level must be disabled"

private def testConfigurationValidation : IO Unit := do
  match compileLevels .info [("App..Http", .debug)] with
  | .error (.invalidLoggerPrefix "App..Http") => pure ()
  | _ => fail "invalid logger prefix was accepted"
  match compileLevels .info [("App", .debug), ("App", .warn)] with
  | .error (.duplicateLoggerPrefix "App") => pure ()
  | _ => fail "duplicate logger prefix was accepted"

  let unnamed := AppenderSpec.custom "" fun _ =>
    pure { append := fun _ => pure () }
  match ({ appenders := #[unnamed] : Loggers.LogConfig }).compile with
  | .error (.invalidAppenderName "") => pure ()
  | _ => fail "an empty appender name was accepted"

  let duplicate := AppenderSpec.custom "duplicate" fun _ =>
    pure { append := fun _ => pure () }
  match ({ appenders := #[duplicate, duplicate] : Loggers.LogConfig }).compile with
  | .error (.duplicateAppenderName "duplicate") => pure ()
  | _ => fail "a duplicate appender name was accepted"

private def recordingFilter
    (calls : IO.Ref (List String))
    (label : String)
    (reply : FilterReply) : Filter :=
  ⟨fun _ => do
    calls.modify (· ++ [label])
    pure reply⟩

private def testFilterOrderingAndShortCircuit : IO Unit := do
  let calls ← IO.mkRef ([] : List String)
  let appended ← IO.mkRef 0
  let spec := AppenderSpec.custom "filtered" (fun _ => pure {
      append := fun _ => appended.modify (· + 1)
    })
    |>.withFilter (recordingFilter calls "first" .accept)
    |>.withFilter (recordingFilter calls "second" .deny)
  let appender ← spec.start {}
  appender.append (event "accepted")
  expectEq (← calls.get) ["first"] "chained filter order"
  expectEq (← appended.get) 1 "accepted event delivery"

  calls.set []
  let accepted ← filtersAccept #[
    recordingFilter calls "neutral" .neutral,
    recordingFilter calls "deny" .deny,
    recordingFilter calls "unreached" .accept
  ] (event "denied")
  expect (!accepted) "deny must reject an event"
  expectEq (← calls.get) ["neutral", "deny"] "deny short circuit"

  expect (← filtersAccept #[Filter.constant .neutral] (event "neutral"))
    "an all-neutral chain must accept"
  appender.close

private def testAppenderFailureIsolation : IO Unit := do
  let diagnostics ← IO.mkRef ([] : List Diagnostic)
  let delivered ← IO.mkRef ([] : List String)
  let services : RuntimeServices := {
    diagnostic := fun diagnostic => diagnostics.modify (· ++ [diagnostic])
  }
  let failing : StartedAppender := {
    name := "failing"
    append := fun _ => throw (IO.userError "sink failed")
  }
  let healthy : StartedAppender := {
    name := "healthy"
    append := fun value => delivered.modify (· ++ [value.message])
  }
  routeEvent services #[failing, healthy] (event "delivered")
  expectEq (← delivered.get) ["delivered"] "isolated routing"
  match ← diagnostics.get with
  | [diagnostic] =>
      expectEq diagnostic.component "failing" "diagnostic component"
      expectEq diagnostic.operation .append "diagnostic operation"
  | other => fail s!"expected one diagnostic, got {other.length}"

private def testSerializedAppender : IO Unit := do
  let firstEntered ← IO.Promise.new
  let releaseFirst ← IO.Promise.new
  let secondAttempted ← IO.Promise.new
  let secondDone ← IO.Promise.new
  let order ← IO.mkRef ([] : List String)
  let spec := AppenderSpec.custom "serialized" fun _ => pure {
    append := fun value => do
      order.modify (· ++ [value.message])
      if value.message == "first" then
        firstEntered.resolve ()
        awaitUnit "first release" releaseFirst
  }
  let appender ← spec.start {}
  let firstTask ← IO.asTask <| appender.append (event "first")
  awaitUnit "first entry" firstEntered
  let secondTask ← IO.asTask do
    secondAttempted.resolve ()
    appender.append (event "second")
    secondDone.resolve ()
  awaitUnit "second attempt" secondAttempted
  expect (!(← secondDone.isResolved)) "a concurrent append bypassed serialization"
  releaseFirst.resolve ()
  discard <| waitTask firstTask
  discard <| waitTask secondTask
  expectEq (← order.get) ["first", "second"] "serialized append order"
  appender.close

private def lifecycleTarget
    (events : IO.Ref (List String))
    (name : String) : AppenderTarget := {
  append := fun _ => pure ()
  flush := events.modify (· ++ [s!"flush-{name}"])
  close := events.modify (· ++ [s!"close-{name}"])
}

private def testStartupUnwind : IO Unit := do
  let events ← IO.mkRef ([] : List String)
  let diagnostics ← IO.mkRef ([] : List Diagnostic)
  let started (name : String) := AppenderSpec.custom name fun _ => do
    events.modify (· ++ [s!"start-{name}"])
    pure (lifecycleTarget events name)
  let failing := AppenderSpec.custom "three" fun _ => do
    events.modify (· ++ ["start-three"])
    throw (IO.userError "startup failed")
  let config : Loggers.LogConfig := {
    appenders := #[started "one", started "two", failing]
    services := {
      diagnostic := fun diagnostic => diagnostics.modify (· ++ [diagnostic])
    }
  }
  try
    discard <| config.start
    fail "runtime startup unexpectedly succeeded"
  catch error =>
    expect ((toString error).contains "startup failed") "startup error was not preserved"
  expectEq (← events.get) [
    "start-one", "start-two", "start-three",
    "flush-two", "close-two", "flush-one", "close-one"
  ] "reverse startup unwind"
  match ← diagnostics.get with
  | [diagnostic] =>
      expectEq diagnostic.component "three" "startup diagnostic component"
      expectEq diagnostic.operation .startup "startup diagnostic operation"
  | other => fail s!"expected one startup diagnostic, got {other.length}"

private def testIdempotentClose : IO Unit := do
  let flushes ← IO.mkRef 0
  let closes ← IO.mkRef 0
  let spec := AppenderSpec.custom "counted" fun _ => pure {
    append := fun _ => pure ()
    flush := flushes.modify (· + 1)
    close := closes.modify (· + 1)
  }
  let runtime ← ({ appenders := #[spec] : Loggers.LogConfig }).start
  runtime.close
  runtime.close
  runtime.flush
  expectEq (← flushes.get) 1 "exactly-once final flush"
  expectEq (← closes.get) 1 "exactly-once close"

private def testConcurrentClose : IO Unit := do
  let flushes ← IO.mkRef 0
  let closes ← IO.mkRef 0
  let closeEntered ← IO.Promise.new
  let closeRelease ← IO.Promise.new
  let secondStarted ← IO.Promise.new
  let secondDone ← IO.Promise.new
  let spec := AppenderSpec.custom "concurrent-close" fun _ => pure {
    append := fun _ => pure ()
    flush := flushes.modify (· + 1)
    close := do
      closes.modify (· + 1)
      closeEntered.resolve ()
      awaitUnit "close release" closeRelease
  }
  let runtime ← ({ appenders := #[spec] : Loggers.LogConfig }).start
  let firstTask ← IO.asTask runtime.close
  awaitUnit "close entry" closeEntered
  let secondTask ← IO.asTask do
    secondStarted.resolve ()
    runtime.close
    secondDone.resolve ()
  awaitUnit "second close start" secondStarted
  expect (!(← secondDone.isResolved)) "a concurrent close returned before child retirement"
  closeRelease.resolve ()
  discard <| waitTask firstTask
  discard <| waitTask secondTask
  expect (← secondDone.isResolved) "the concurrent close waiter did not finish"
  expectEq (← flushes.get) 1 "concurrent exactly-once final flush"
  expectEq (← closes.get) 1 "concurrent exactly-once close"

private def testFileAppenderModes : IO Unit :=
  IO.FS.withTempDir fun directory => do
    let path := directory / "events.log"
    let encoder : Loggers.Format.Encoder := fun value =>
      (value.message ++ "\n").toUTF8

    let first ← ({ appenders := #[
      AppenderSpec.file "file" path encoder .truncate
    ] } : Loggers.LogConfig).start
    first.core.sink (event "one")
    first.core.sink (event "two")
    first.flush
    expectEq (← IO.FS.readFile path) "one\ntwo\n" "truncated file output"
    first.close

    let second ← ({ appenders := #[
      AppenderSpec.file "file" path encoder .append
    ] } : Loggers.LogConfig).start
    second.core.sink (event "three")
    second.close
    expectEq (← IO.FS.readFile path) "one\ntwo\nthree\n" "appended file output"

private def testRuntimeAdmissionFence : IO Unit := do
  let appendEntered ← IO.Promise.new
  let appendRelease ← IO.Promise.new
  let closeEntered ← IO.Promise.new
  let closeDone ← IO.Promise.new
  let diagnostics ← IO.mkRef ([] : List Diagnostic)
  let base := AppenderSpec.custom "gated" fun _ => pure {
    append := fun _ => pure ()
  }
  let decorated := base.mapStarted fun _ child => pure {
    name := child.name
    append := fun _ => do
      appendEntered.resolve ()
      awaitUnit "append release" appendRelease
    flush := child.flush
    close := do
      closeEntered.resolve ()
      child.close
  }
  let config : Loggers.LogConfig := {
    appenders := #[decorated]
    services := {
      diagnostic := fun diagnostic => diagnostics.modify (· ++ [diagnostic])
    }
  }
  let runtime ← config.start
  let appendTask ← IO.asTask <| runtime.core.sink (event "accepted")
  awaitUnit "append entry" appendEntered
  let closeTask ← IO.asTask do
    runtime.close
    closeDone.resolve ()
  awaitUnit "close entry" closeEntered
  expect (!(← closeDone.isResolved)) "runtime close did not wait for an admitted event"
  runtime.core.sink (event "rejected")
  expect ((← diagnostics.get).any fun diagnostic =>
    diagnostic.component == "runtime" && diagnostic.operation == .append)
    "post-fence event was not rejected diagnostically"
  appendRelease.resolve ()
  discard <| waitTask appendTask
  discard <| waitTask closeTask
  expect (← closeDone.isResolved) "runtime close did not finish after drain"

private def testBracketPreservesPrimaryFailure : IO Unit := do
  let diagnostics ← IO.mkRef ([] : List Diagnostic)
  let spec := AppenderSpec.custom "bad-close" fun _ => pure {
    append := fun _ => pure ()
    close := throw (IO.userError "close failure")
  }
  let config : Loggers.LogConfig := {
    appenders := #[spec]
    services := {
      diagnostic := fun diagnostic => diagnostics.modify (· ++ [diagnostic])
    }
  }
  let action : Logger [] Unit := fun _ => throw (IO.userError "application failure")
  try
    Loggers.Runtime.run config action
    fail "failing application unexpectedly succeeded"
  catch error =>
    expect ((toString error).contains "application failure")
      "shutdown failure masked the application failure"
  expect ((← diagnostics.get).any fun diagnostic =>
    diagnostic.operation == .close && diagnostic.message.contains "close failure")
    "secondary shutdown failure was not diagnosed"

private def testBracketReportsCloseFailure : IO Unit := do
  let spec := AppenderSpec.custom "bad-close" fun _ => pure {
    append := fun _ => pure ()
    close := throw (IO.userError "close failure")
  }
  try
    Loggers.Runtime.run ({ appenders := #[spec] } : Loggers.LogConfig) (pure ())
    fail "close failure was not returned"
  catch error =>
    expect ((toString error).contains "close failure") "wrong close error"

def runAll : IO Unit := do
  testHierarchicalLevels
  testConfigurationValidation
  testFilterOrderingAndShortCircuit
  testAppenderFailureIsolation
  testSerializedAppender
  testStartupUnwind
  testIdempotentClose
  testConcurrentClose
  testFileAppenderModes
  testRuntimeAdmissionFence
  testBracketPreservesPrimaryFailure
  testBracketReportsCloseFailure

end Test.Runtime

def main : IO Unit :=
  Test.Runtime.runAll
