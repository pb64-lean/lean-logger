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
error: Unknown constant `Loggers.HasKey.findImpl`
-/
#guard_msgs (error, substring := true) in
#check Loggers.HasKey.findImpl

/--
error:
-/
#guard_msgs (error, substring := true) in
#check ({ findImpl := fun env => env.1 } : HasKey [("identity", Nat)] "identity" Nat)

/--
error: duplicate event field 'duplicate'
-/
#guard_msgs (error, substring := true) in
def duplicateFields := fields! ["duplicate" := (1 : Nat), "duplicate" := (2 : Nat)]

/--
error: Tactic `decide` proved
-/
#guard_msgs (error, substring := true) in
def invalidStaticContext : Logger [] Unit :=
  pushNew "bad key" "value" do pure ()

/--
error: Tactic `decide` proved
-/
#guard_msgs (error, substring := true) in
def duplicatePush : Logger [] Unit :=
  pushNew "identity" "outer" do
    pushNew "identity" "inner" do pure ()

/--
error: invalid event field name 'bad=key'
-/
#guard_msgs (error, substring := true) in
def invalidStaticFields := fields! ["bad=key" := (1 : Nat)]

/--
error: expected 'fields'
-/
#guard_msgs (error, substring := true) in
def invalidFieldArgumentLabel : Logger [] Unit :=
  log! .info "invalid label" (fieldValues := fields! [])

private def fields : Nat :=
  7

private def downstreamEventLiteral : LogEvent :=
  { timestamp := 0
    level := .info
    logger := "Downstream"
    provenance := { declaration := `Test.Core.downstreamEventLiteral, module := `Test.Core }
    message := "constructed"
    fields := [] }

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
  expect (decide (Level.debug ≤ Level.info)) "level LE ordering"
  expect (!decide (Level.error ≤ Level.warn)) "level LE reverse ordering"
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

private def stateCore : CoreCtx (StateM (List LogEvent)) :=
  { enabled := fun _ _ => pure true
    now := pure 0
    sink := fun event => modify (· ++ [event])
    close := pure () }

private def stateProgram : LoggerT [] (StateM (List LogEvent)) Unit :=
  pushNew "requestId" "state-r-1" do
    log! .info "pure carrier" (fields := fields! ["count" := (2 : Nat)])

private def testCarrierParametricity : IO Unit := do
  let (_, events) := runWith stateCore stateProgram []
  let event ← onlyEvent events
  expectEq event.context [("requestId", .str "state-r-1")] "StateM context"
  expectEq event.fields [("count", .nat 2)] "StateM fields"

private def exceptProgram : LoggerT [] (ExceptT String IO) Unit :=
  pushNew "requestId" "except-r-1" do
    log! .info "except carrier"

private def testExceptTCarrier : IO Unit := do
  let events ← IO.mkRef ([] : List LogEvent)
  let core : CoreCtx (ExceptT String IO) := {
    enabled := fun _ _ => pure true
    now := pure 0
    sink := fun event => ExceptT.lift (events.modify (· ++ [event]))
    close := pure ()
  }
  match ← ExceptT.run (runWith core exceptProgram) with
  | .error error => fail s!"ExceptT carrier failed: {error}"
  | .ok () => pure ()
  let event ← onlyEvent (← events.get)
  expectEq event.context [("requestId", .str "except-r-1")] "ExceptT context"

private def secretProgram : Logger [] String := do
  let secret := Secret.protect "application-secret"
  pushNew "credential" secret do
    log! .info "redacted"
      (fields := fields! ["secretField" := secret])
  pure secret.reveal

private def testRedactionAndFieldLookup : IO Unit := do
  let typedFields := EventFields.empty.insert "count" (7 : Nat)
  expectEq (typedFields.get "count") 7 "typed event-field lookup"
  let events ← IO.mkRef ([] : List LogEvent)
  let revealed ← runWith (capturingCore events) secretProgram
  expectEq revealed "application-secret" "secret reveal"
  let event ← onlyEvent (← events.get)
  expectEq event.context [("credential", .str "***")] "context redaction"
  expectEq event.fields [("secretField", .str "***")] "event-field redaction"

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

private def sameTypeRebindingProgram : Logger [] Unit :=
  pushNew "identity" "outer" do
    rebindMDC "identity" "inner" do
      let identity : String ← mdc "identity"
      log! .info "same-type inner {identity}"
    let identity : String ← mdc "identity"
    log! .info "same-type outer {identity}"

private def testSameTypeRebinding : IO Unit := do
  let events ← IO.mkRef ([] : List LogEvent)
  runWith (capturingCore events) sameTypeRebindingProgram
  match ← events.get with
  | [inner, outer] =>
      expectEq inner.message "same-type inner inner" "same-type rebound lookup"
      expectEq inner.context [("identity", .str "inner")] "same-type canonical erasure"
      expectEq outer.message "same-type outer outer" "same-type restored lookup"
      expectEq outer.context [("identity", .str "outer")] "same-type restoration"
  | other => fail s!"expected two same-type rebinding events, got {other.length}"

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

private def duplicateTypedCollisionProgram : Logger [] (Except DynamicError Unit) :=
  pushNew "identity" "typed" do
    mergeDynMDC .overwrite
      [("identity", .str "first"), ("identity", .str "second")] do
      log! .info "must not run"

private def testDuplicatePrecedesTypedCollision : IO Unit := do
  let events ← IO.mkRef ([] : List LogEvent)
  let result ← runWith (capturingCore events) duplicateTypedCollisionProgram
  match result with
  | .error (.duplicateInput "identity") => pure ()
  | _ => fail s!"duplicate/typed precedence: got {repr result}"
  expectEq (← events.get) [] "duplicate input action suppression"

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

private def eventFieldPolicyProgram : Logger [] Unit := do
  let base ←
    match EventFields.empty.mergeDynamic .reject [("color", .str "red")] with
    | .ok value => pure value
    | .error error => fail s!"base event fields failed: {error}"
  let preserved ←
    match base.mergeDynamic .preserve [("color", .str "blue")] with
    | .ok value => pure value
    | .error error => fail s!"preserved event fields failed: {error}"
  log! .info "preserved event fields" (fields := preserved)
  let overwritten ←
    match base.mergeDynamic .overwrite [("color", .str "blue")] with
    | .ok value => pure value
    | .error error => fail s!"overwritten event fields failed: {error}"
  log! .info "overwritten event fields" (fields := overwritten)
  match base.mergeDynamic .reject [("color", .str "blue")] with
  | .error (.dynamicCollision "color") => pure ()
  | _ => fail "rejected event fields produced the wrong result"
  let dynamicFirst ←
    match EventFields.empty.mergeDynamic .reject [("identity", .str "dynamic")] with
    | .ok value => pure value
    | .error error => fail s!"dynamic-first event fields failed: {error}"
  let typedAfter := dynamicFirst.insert "identity" "typed"
  log! .info "typed event-field precedence" (fields := typedAfter)
  let typedFirst := EventFields.empty.insert "identity" "typed"
  match typedFirst.mergeDynamic .overwrite [("identity", .str "dynamic")] with
  | .error (.typedCollision "identity") => pure ()
  | _ => fail "typed-first event-field collision produced the wrong result"
  match typedFirst.mergeDynamic .overwrite
      [("identity", .str "first"), ("identity", .str "second")] with
  | .error (.duplicateInput "identity") => pure ()
  | _ => fail "event-field duplicate/typed precedence produced the wrong result"

private def testEventFieldPolicies : IO Unit := do
  let events ← IO.mkRef ([] : List LogEvent)
  runWith (capturingCore events) eventFieldPolicyProgram
  match ← events.get with
  | [preserved, overwritten, typedAfter] =>
      expectEq preserved.fields [("color", .str "red")] "preserved event fields"
      expectEq overwritten.fields [("color", .str "blue")] "overwritten event fields"
      expectEq typedAfter.fields [("identity", .str "typed")] "typed event-field precedence"
  | other => fail s!"expected three event-field policy events, got {other.length}"

private def contextUtilityProgram : Logger [] (Except DynamicError Unit) :=
  withDynMDC "dynamic" (.str "runtime") do
    pushNew "typed" (7 : Nat) do
      expectEq (← mdc? "typed") (some (.nat 7)) "typed mdc?"
      expectEq (← mdc? "dynamic") (some (.str "runtime")) "dynamic mdc?"
      expectEq (← mdc? "missing") none "missing mdc?"
      clearMDC do
        expectEq (← mdc? "typed") none "cleared typed mdc"
        expectEq (← mdc? "dynamic") none "cleared dynamic mdc"
        log! .info "cleared"
      log! .info "restored"

private def concurrentContextProgram : Logger [] (Task (Except IO.Error Unit)) :=
  pushNew "requestId" "task-r-1" do
    Logger.concurrently do
      log! .info "concurrent"

private def testContextUtilities : IO Unit := do
  let events ← IO.mkRef ([] : List LogEvent)
  let core := capturingCore events
  match ← runWith core contextUtilityProgram with
  | .error error => fail s!"context utility boundary failed: {error}"
  | .ok () => pure ()
  match ← events.get with
  | [cleared, restored] =>
      expectEq cleared.context [] "clearMDC context"
      expectEq restored.context
        [("typed", .nat 7), ("dynamic", .str "runtime")]
        "clearMDC restoration"
  | other => fail s!"expected two context-utility events, got {other.length}"

  match ← runWith core <| withDynMDC "bad key" (.str "invalid") (pure ()) with
  | .error (.invalidName "bad key") => pure ()
  | result => fail s!"invalid dynamic context key: got {repr result}"
  match EventFields.empty.mergeDynamic .reject [("bad=key", .str "invalid")] with
  | .error (.invalidName "bad=key") => pure ()
  | _ => fail "invalid dynamic event-field key produced the wrong result"

  events.set []
  let task ← runWith core concurrentContextProgram
  match ← IO.wait task with
  | .error error => fail s!"Logger.concurrently failed: {error}"
  | .ok () => pure ()
  let concurrent ← onlyEvent (← events.get)
  expectEq concurrent.context [("requestId", .str "task-r-1")]
    "Logger.concurrently context"

private unsafe def observe (calls : IO.Ref Nat) (value : α) : α :=
  unsafeBaseIO do
    calls.modify (· + 1)
    pure value

private structure CountedContext where
  calls : IO.Ref Nat

private unsafe instance : ToLogValue CountedContext where
  toLogValue value := observe value.calls (.str "context")

private unsafe def disabledProgram
    (contextCalls messageCalls fieldCalls causeCalls : IO.Ref Nat) : Logger [] Unit :=
  pushNew "explosive" ({ calls := contextCalls } : CountedContext) do
    log! .debug "disabled {observe messageCalls "message"}"
      (fields := fields! ["field" := observe fieldCalls "value"])
    logErr! .debug (observe causeCalls (IO.userError "cause")) "disabled error"

private unsafe def acceptedForcingProgram
    (contextCalls messageCalls fieldCalls causeCalls : IO.Ref Nat) : Logger [] Unit :=
  pushNew "counted" ({ calls := contextCalls } : CountedContext) do
    logErr! .info (observe causeCalls (IO.userError "cause"))
      "accepted {observe messageCalls "message"}"
      (fields := fields! ["field" := observe fieldCalls "value"])

private unsafe def successfulFailureProgram
    (messageCalls fieldCalls : IO.Ref Nat) : Logger [] (Except String Nat) :=
  logFailure! .warn (.ok 7 : Except String Nat)
    "unused {observe messageCalls "message"}"
    (fields := fields! ["field" := observe fieldCalls "value"])

private unsafe def rebindForcingProgram
    (outerCalls innerCalls : IO.Ref Nat) : Logger [] Unit :=
  pushNew "identity" ({ calls := outerCalls } : CountedContext) do
    rebindMDC "identity" ({ calls := innerCalls } : CountedContext) do
      log! .info "visible binding only"

private unsafe def testDisabledLaziness : IO Unit := do
  let events ← IO.mkRef ([] : List LogEvent)
  let nowCalls ← IO.mkRef 0
  let sinkCalls ← IO.mkRef 0
  let contextCalls ← IO.mkRef 0
  let messageCalls ← IO.mkRef 0
  let fieldCalls ← IO.mkRef 0
  let causeCalls ← IO.mkRef 0
  runWith (capturingCore events false (some nowCalls) (some sinkCalls)) <|
    disabledProgram contextCalls messageCalls fieldCalls causeCalls
  expectEq (← events.get) [] "disabled events"
  expectEq (← nowCalls.get) 0 "disabled clock"
  expectEq (← sinkCalls.get) 0 "disabled sink"
  expectEq (← contextCalls.get) 0 "disabled context conversion"
  expectEq (← messageCalls.get) 0 "disabled message construction"
  expectEq (← fieldCalls.get) 0 "disabled field construction"
  expectEq (← causeCalls.get) 0 "disabled cause construction"

  runWith (capturingCore events) <|
    acceptedForcingProgram contextCalls messageCalls fieldCalls causeCalls
  expectEq (← contextCalls.get) 1 "accepted context conversion"
  expectEq (← messageCalls.get) 1 "accepted message construction"
  expectEq (← fieldCalls.get) 1 "accepted field construction"
  expectEq (← causeCalls.get) 1 "accepted cause construction"

  let successMessageCalls ← IO.mkRef 0
  let successFieldCalls ← IO.mkRef 0
  let result ← runWith (capturingCore events) <|
    successfulFailureProgram successMessageCalls successFieldCalls
  match result with
  | .ok 7 => pure ()
  | _ => fail "successful failure helper changed its result"
  expectEq (← successMessageCalls.get) 0 "successful failure helper message"
  expectEq (← successFieldCalls.get) 0 "successful failure helper fields"

  let outerCalls ← IO.mkRef 0
  let innerCalls ← IO.mkRef 0
  runWith (capturingCore events) <| rebindForcingProgram outerCalls innerCalls
  expectEq (← outerCalls.get) 0 "shadowed context conversion"
  expectEq (← innerCalls.get) 1 "visible context conversion"

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

private def testFailureLoggingIsObservational : IO Unit := do
  let core : CoreCtx IO :=
    { enabled := fun _ _ => pure true
      now := pure 0
      sink := fun _ => throw (IO.userError "observational sink failure")
      close := pure () }
  let result ← runWith core <|
    logFailure! .error (.error "original" : Except String Nat) "failed"
  match result with
  | .error "original" => pure ()
  | _ => fail "failure helper did not preserve the original result"

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

private def richSnapshotProgram :
    Logger [] (Except DynamicError (Snapshot IO [("requestId", String)])) :=
  withDynMDC "traceId" (.str "dynamic-trace") do
    pushNew "requestId" "captured-request" do
      withLogger "Captured.Logger" capture

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
  let richResult ← runWith core richSnapshotProgram
  let rich ←
    match richResult with
    | .ok snapshot => pure snapshot
    | .error error => fail s!"rich snapshot failed: {error}"
  rich.run (log! .info "after parent scope")
  let event ← onlyEvent (← events.get)
  expectEq event.logger "Captured.Logger" "snapshot logger override"
  expectEq event.context
    [("requestId", .str "captured-request"), ("traceId", .str "dynamic-trace")]
    "snapshot canonical context"

unsafe def runAll : IO Unit := do
  expectEq fields 7 "ordinary fields identifier"
  expectEq downstreamEventLiteral.fields [] "downstream record field syntax"
  testLevels
  testTypedContextAndFields
  testCarrierParametricity
  testExceptTCarrier
  testRedactionAndFieldLookup
  testRebindingAndRestoration
  testSameTypeRebinding
  testExceptionRestoration
  testDynamicPrecedenceAndHiding
  testTypedCollision
  testDuplicatePrecedesTypedCollision
  testDynamicPolicies
  testEventFieldPolicies
  testContextUtilities
  testDisabledLaziness
  testFailureHelpers
  testFailureLoggingIsObservational
  testTapErrorPreservesPrimary
  testSnapshots

end Test.Core

unsafe def main : IO Unit :=
  Test.Core.runAll
