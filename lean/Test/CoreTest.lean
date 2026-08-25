import Loggers.Core

open Loggers

namespace Test.Core

/--
error: failed to synthesize
-/
#guard_msgs (error, substring := true) in
#synth HasKey [("identity", Nat), ("identity", String)] "identity" String

/--
error: Unknown constant `Loggers.HasKey.mk`
-/
#guard_msgs (error, substring := true) in
#check Loggers.HasKey.mk

/--
error:
-/
#guard_msgs (error, substring := true) in
def duplicateFields := fields! ["duplicate" := (1 : Nat), "duplicate" := (2 : Nat)]

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def expect (condition : Bool) (message : String) : IO Unit :=
  unless condition do fail message

private def expectEq [BEq α] [Repr α] (actual expected : α) (label : String) : IO Unit :=
  unless actual == expected do
    fail s!"{label}: expected {repr expected}, got {repr actual}"

private def onlyEvent (events : List LogEvent) : IO LogEvent :=
  match events with
  | [event] => pure event
  | _ => fail s!"expected one event, got {events.length}"

private def capturingCore
    (events : IO.Ref (List LogEvent))
    (enabled : Bool := true)
    (nowCalls? : Option (IO.Ref Nat) := none)
    (sinkCalls? : Option (IO.Ref Nat) := none) : CoreCtx IO :=
  { enabled := fun _ _ => pure enabled
    now := do
      if let some calls := nowCalls? then calls.modify (· + 1)
      pure 0
    sink := fun event => do
      if let some calls := sinkCalls? then calls.modify (· + 1)
      events.modify (· ++ [event])
    close := pure () }

private def testLevels : IO Unit := do
  expect (Level.enabledBy .info .error) "error must pass an info threshold"
  expect (!Level.enabledBy .warn .info) "info must not pass a warn threshold"
  expectEq (Level.parse? "WARNING") (some .warn) "level parsing"

private def structuredProgram : Logger [] Unit :=
  pushNew "requestId" "r-42" do
    pushNew "userId" (7 : Nat) do
      let requestId : String ← mdc "requestId"
      log! .info "accepted {requestId}"
        (fields := fields! ["outcome" := "ok", "durationMs" := (12 : Nat)])

private def testTypedContextAndFields : IO Unit := do
  let events ← IO.mkRef ([] : List LogEvent)
  runWith (capturingCore events) structuredProgram
  let event ← onlyEvent (← events.get)
  expectEq event.level .info "event level"
  expectEq event.message "accepted r-42" "lazy interpolation"
  expectEq event.context
    [("requestId", .str "r-42"), ("userId", .nat 7)]
    "canonical context"
  expectEq event.fields
    [("outcome", .str "ok"), ("durationMs", .nat 12)]
    "typed fields"
  expect (event.provenance.declaration.toString.endsWith "structuredProgram")
    "provenance must name the lexical declaration"

private def rebindingProgram : Logger [] Unit :=
  pushNew "identity" "outer" do
    rebindMDC "identity" (17 : Nat) do
      let identity : Nat ← mdc "identity"
      log! .info "inner {identity}"
    let identity : String ← mdc "identity"
    log! .info "outer {identity}"

private def testRebindingAndRestoration : IO Unit := do
  let events ← IO.mkRef ([] : List LogEvent)
  runWith (capturingCore events) rebindingProgram
  match ← events.get with
  | [inner, outer] =>
      expectEq inner.context [("identity", .nat 17)] "rebound canonical context"
      expectEq outer.context [("identity", .str "outer")] "restored context"
  | other => fail s!"expected two rebinding events, got {other.length}"

private def exceptionProgram : Logger [] Unit :=
  pushNew "identity" "outer" do
    try
      rebindMDC "identity" (17 : Nat) do
        throw (IO.userError "stop")
    catch _ =>
      log! .info "recovered"

private def testExceptionRestoration : IO Unit := do
  let events ← IO.mkRef ([] : List LogEvent)
  runWith (capturingCore events) exceptionProgram
  let event ← onlyEvent (← events.get)
  expectEq event.context [("identity", .str "outer")] "exception restoration"

private def dynamicOrderProgram : Logger [] (Except DynamicError Unit) :=
  withDynMDC "identity" (.str "dynamic") do
    pushNew "identity" "typed" do
      hideMDC "identity" do
        log! .info "hidden"
      log! .info "typed"
    log! .info "dynamic"

private def testDynamicPrecedenceAndHiding : IO Unit := do
  let events ← IO.mkRef ([] : List LogEvent)
  let result ← runWith (capturingCore events) dynamicOrderProgram
  match result with
  | .error error => fail s!"unexpected dynamic error: {error}"
  | .ok () => pure ()
  match ← events.get with
  | [hidden, typed, dynamic] =>
      expectEq hidden.context [] "scoped hiding"
      expectEq typed.context [("identity", .str "typed")] "typed precedence"
      expectEq dynamic.context [("identity", .str "dynamic")] "dynamic restoration"
  | other => fail s!"expected three dynamic-order events, got {other.length}"

private def typedCollisionProgram : Logger [] (Except DynamicError Unit) :=
  pushNew "identity" "typed" do
    mergeDynMDC .overwrite [("identity", .str "dynamic")] do
      log! .info "must not run"

private def testTypedCollision : IO Unit := do
  let events ← IO.mkRef ([] : List LogEvent)
  let result ← runWith (capturingCore events) typedCollisionProgram
  match result with
  | .error (.typedCollision "identity") => pure ()
  | _ => fail s!"typed collision: got {repr result}"
  expectEq (← events.get) [] "colliding action suppression"

private def policyProgram : Logger [] (Except DynamicError Unit) :=
  withDynMDC "color" (.str "red") do
    let preserved ← mergeDynMDC .preserve [("color", .str "blue")] do
      log! .info "preserved"
    match preserved with
    | .error error => fail s!"preserve failed: {error}"
    | .ok () => pure ()
    let overwritten ← mergeDynMDC .overwrite [("color", .str "blue")] do
      log! .info "overwritten"
    match overwritten with
    | .error error => fail s!"overwrite failed: {error}"
    | .ok () => pure ()
    let rejected ← mergeDynMDC .reject [("color", .str "blue")] do
      log! .info "must not run"
    match rejected with
    | .error (.dynamicCollision "color") => pure ()
    | _ => fail "reject policy produced the wrong result"

private def testDynamicPolicies : IO Unit := do
  let events ← IO.mkRef ([] : List LogEvent)
  let result ← runWith (capturingCore events) policyProgram
  match result with
  | .error error => fail s!"outer dynamic binding failed: {error}"
  | .ok () => pure ()
  match ← events.get with
  | [preserved, overwritten] =>
      expectEq preserved.context [("color", .str "red")] "preserve policy"
      expectEq overwritten.context [("color", .str "blue")] "overwrite policy"
  | other => fail s!"expected two policy events, got {other.length}"

private structure Explosive where

private instance : ToLogValue Explosive where
  toLogValue _ := panic! "disabled context conversion was forced"

private def disabledProgram : Logger [] Unit :=
  pushNew "explosive" ({} : Explosive) do
    log! .debug "disabled {(panic! "message forced" : String)}"
      (fields := fields! ["field" := (panic! "field forced" : String)])
    logErr! .debug (panic! "cause forced" : IO.Error) "disabled error"

private def testDisabledLaziness : IO Unit := do
  let events ← IO.mkRef ([] : List LogEvent)
  let nowCalls ← IO.mkRef 0
  let sinkCalls ← IO.mkRef 0
  runWith (capturingCore events false (some nowCalls) (some sinkCalls)) disabledProgram
  expectEq (← events.get) [] "disabled events"
  expectEq (← nowCalls.get) 0 "disabled clock"
  expectEq (← sinkCalls.get) 0 "disabled sink"

private def failureProgram : Logger [] (Except String Nat × Except String Nat) := do
  let failed ← logFailure! .warn (.error "bad" : Except String Nat) "operation failed"
    (fields := fields! ["attempt" := (3 : Nat)])
  let succeeded ← logFailure! .warn (.ok 7 : Except String Nat) "must not log"
  pure (failed, succeeded)

private def testFailureHelpers : IO Unit := do
  let events ← IO.mkRef ([] : List LogEvent)
  let (failed, succeeded) ← runWith (capturingCore events) failureProgram
  match failed, succeeded with
  | .error "bad", .ok 7 => pure ()
  | _, _ => fail "logFailure! changed its input results"
  let event ← onlyEvent (← events.get)
  expectEq event.level .warn "failure level"
  expectEq (event.cause.map fun cause => cause.summary) (some "bad") "failure cause"
  expectEq event.fields [("attempt", .nat 3)] "failure fields"

private def testTapErrorPreservesPrimary : IO Unit := do
  let core : CoreCtx IO :=
    { enabled := fun _ _ => pure true
      now := pure 0
      sink := fun _ => throw (IO.userError "sink failure")
      close := pure () }
  try
    runWith core <| tapError! .error (throw (IO.userError "primary failure")) "action failed"
    fail "tapError! unexpectedly succeeded"
  catch error =>
    expect ((toString error).contains "primary failure")
      "tapError! must preserve the primary application error"

private def testSnapshots : IO Unit := do
  let events ← IO.mkRef ([] : List LogEvent)
  let core := capturingCore events
  let snapshot : Snapshot IO [("requestId", String)] ←
    runWith core <| pushNew "requestId" "captured" capture
  let value : String ← snapshot.run (mdc "requestId")
  expectEq value "captured" "snapshot read"
  let task ← snapshot.concurrently (mdc "requestId")
  match ← IO.wait task with
  | .ok taskValue => expectEq taskValue "captured" "snapshot task"
  | .error error => fail s!"snapshot task failed: {error}"

def runAll : IO Unit := do
  testLevels
  testTypedContextAndFields
  testRebindingAndRestoration
  testExceptionRestoration
  testDynamicPrecedenceAndHiding
  testTypedCollision
  testDynamicPolicies
  testDisabledLaziness
  testFailureHelpers
  testTapErrorPreservesPrimary
  testSnapshots

end Test.Core

def main : IO Unit :=
  Test.Core.runAll
