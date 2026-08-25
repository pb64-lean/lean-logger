import Loggers.Runtime.Config
import Loggers.Runtime.Appender
import Init.System.Promise

namespace Loggers
namespace Runtime

private inductive RuntimePhase where
  | open
  | closing
      (drained : IO.Promise Unit)
      (done : IO.Promise (Except IO.Error Unit))
  | closed (result : Except IO.Error Unit)

private structure RuntimeState where
  phase : RuntimePhase := .open
  inFlight : Nat := 0

/-- A started logging runtime and its empty-row core context. -/
structure StartedRuntime where
  private mk ::
  core : CoreCtx IO
  private appenders : Array StartedAppender
  private services : RuntimeServices
  private state : Std.Mutex RuntimeState

private def reportFailure
    (services : RuntimeServices)
    (component : String)
    (operation : DiagnosticOperation)
    (error : IO.Error) : IO Unit :=
  services.report { component, operation, message := toString error }

private def closeAppenders
    (services : RuntimeServices)
    (appenders : Array StartedAppender) : IO (Option IO.Error) := do
  let mut firstFailure? : Option IO.Error := none
  for appender in appenders.toList.reverse do
    try
      appender.close
    catch error =>
      reportFailure services appender.name .close error
      if firstFailure?.isNone then
        firstFailure? := some error
  pure firstFailure?

private def flushAppenders
    (services : RuntimeServices)
    (appenders : Array StartedAppender) : IO (Option IO.Error) := do
  let mut firstFailure? : Option IO.Error := none
  for appender in appenders do
    try
      appender.flush
    catch error =>
      reportFailure services appender.name .flush error
      if firstFailure?.isNone then
        firstFailure? := some error
  pure firstFailure?

private def unwindStarted
    (services : RuntimeServices)
    (appenders : Array StartedAppender) : IO Unit := do
  discard <| closeAppenders services appenders

private def startAppenders
    (services : RuntimeServices)
    (specs : List AppenderSpec)
    (started : Array StartedAppender := #[]) : IO (Array StartedAppender) := do
  match specs with
  | [] => pure started
  | spec :: rest =>
      let result : Except IO.Error StartedAppender ← try
        pure (Except.ok (← spec.start services))
      catch error =>
        pure (Except.error error)
      match result with
      | .ok appender =>
          startAppenders services rest (started.push appender)
      | .error error =>
        reportFailure services spec.name .startup error
        unwindStarted services started
        throw error

private def admitEvent (state : Std.Mutex RuntimeState) : IO Bool :=
  state.atomically do
    let current ← get
    match current.phase with
    | .open =>
        set { current with inFlight := current.inFlight + 1 }
        pure true
    | .closing .. | .closed .. =>
        pure false

private def releaseEvent (state : Std.Mutex RuntimeState) : IO Unit :=
  state.atomically do
    let current ← get
    let remaining := current.inFlight - 1
    set { current with inFlight := remaining }
    match current.phase with
    | .closing drained _ =>
        if remaining == 0 then
          liftM (drained.resolve ())
    | .open | .closed .. =>
        pure ()

private def emitRuntime
    (state : Std.Mutex RuntimeState)
    (services : RuntimeServices)
    (appenders : Array StartedAppender)
    (event : LogEvent) : IO Unit := do
  if !(← admitEvent state) then
    services.report {
      component := "runtime"
      operation := .append
      message := "event rejected after logging runtime began closing"
    }
  else
    try
      routeEvent services appenders event
    catch error =>
      releaseEvent state
      throw error
    releaseEvent state

private def awaitUnitPromise (label : String) (promise : IO.Promise Unit) : IO Unit := do
  match ← IO.wait promise.result? with
  | some () => pure ()
  | none => throw <| IO.userError s!"{label} promise was dropped"

private def awaitClosePromise
    (promise : IO.Promise (Except IO.Error Unit)) : IO (Except IO.Error Unit) := do
  match ← IO.wait promise.result? with
  | some result => pure result
  | none => throw <| IO.userError "runtime close promise was dropped"

private def replayResult : Except IO.Error Unit → IO Unit
  | .ok () => pure ()
  | .error error => throw error

private inductive RuntimeSnapshot where
  | open
  | closing (done : IO.Promise (Except IO.Error Unit))
  | closed (result : Except IO.Error Unit)

private def snapshotRuntime (state : Std.Mutex RuntimeState) : IO RuntimeSnapshot :=
  state.atomically do
    match (← get).phase with
    | .open => pure .open
    | .closing _ done => pure (.closing done)
    | .closed result => pure (.closed result)

private def flushRuntime
    (state : Std.Mutex RuntimeState)
    (services : RuntimeServices)
    (appenders : Array StartedAppender) : IO Unit := do
  match ← snapshotRuntime state with
  | .open =>
      match ← flushAppenders services appenders with
      | some error => throw error
      | none => pure ()
  | .closing done =>
      replayResult (← awaitClosePromise done)
  | .closed result =>
      replayResult result

private inductive CloseDecision where
  | owner
      (drained : IO.Promise Unit)
      (done : IO.Promise (Except IO.Error Unit))
      (alreadyDrained : Bool)
  | wait (done : IO.Promise (Except IO.Error Unit))
  | finished (result : Except IO.Error Unit)

private def closeRuntime
    (state : Std.Mutex RuntimeState)
    (services : RuntimeServices)
    (appenders : Array StartedAppender) : IO Unit := do
  let candidateDrained ← IO.Promise.new
  let candidateDone ← IO.Promise.new
  let decision : CloseDecision ← state.atomically do
    let current ← get
    match current.phase with
    | .open =>
        set { current with phase := .closing candidateDrained candidateDone }
        pure <| CloseDecision.owner candidateDrained candidateDone (current.inFlight == 0)
    | .closing _ done =>
        pure (CloseDecision.wait done)
    | .closed result =>
        pure (CloseDecision.finished result)
  match decision with
  | .wait done =>
      replayResult (← awaitClosePromise done)
  | .finished result =>
      replayResult result
  | .owner drained done alreadyDrained =>
      if alreadyDrained then
        drained.resolve ()
      -- Closing appenders first lets a decorator wake producers blocked in admission.
      let failure? ← closeAppenders services appenders
      awaitUnitPromise "runtime drain" drained
      let result := failure?.map Except.error |>.getD (.ok ())
      state.atomically do
        modify fun current => { current with phase := .closed result }
      done.resolve result
      replayResult result

/-- Start a validated configuration and acquire its appenders in declaration order. -/
def CompiledConfig.start (config : CompiledConfig) : IO StartedRuntime := do
  let appenders ← startAppenders config.services config.appenders.toList
  let state ← Std.Mutex.new ({} : RuntimeState)
  let close := closeRuntime state config.services appenders
  let core : CoreCtx IO := {
    enabled := fun logger level => pure (config.levels.enabled logger level)
    now := config.now
    sink := emitRuntime state config.services appenders
    close
  }
  pure ⟨core, appenders, config.services, state⟩

/-- Validate and start a logging configuration. -/
def LogConfig.start (config : LogConfig) : IO StartedRuntime :=
  match config.compile with
  | .error error => throw <| IO.userError (toString error)
  | .ok compiled => compiled.start

/-- Flush every appender while keeping the runtime open. -/
def StartedRuntime.flush (runtime : StartedRuntime) : IO Unit :=
  flushRuntime runtime.state runtime.services runtime.appenders

/-- Close every appender in reverse acquisition order exactly once. -/
def StartedRuntime.close (runtime : StartedRuntime) : IO Unit :=
  closeRuntime runtime.state runtime.services runtime.appenders

/-- Run one empty-row logging computation under a bracketed runtime.

An application failure remains primary if shutdown also fails. -/
def run (config : LogConfig) (action : Logger [] α) : IO α := do
  let runtime ← config.start
  let applicationResult : Except IO.Error α ← try
    pure (Except.ok (← runWith runtime.core action))
  catch error =>
    pure (Except.error error)
  let closeResult : Except IO.Error Unit ← try
    runtime.close
    pure (Except.ok ())
  catch error =>
    pure (Except.error error)
  match applicationResult, closeResult with
  | .ok value, .ok () => pure value
  | .ok _, .error closeError => throw closeError
  | .error applicationError, .ok () => throw applicationError
  | .error applicationError, .error closeError =>
      runtime.services.report {
        component := "runtime"
        operation := .close
        message := s!"shutdown also failed while preserving the application error: {closeError}"
      }
      throw applicationError

end Runtime

/-- Public code-based runtime configuration. -/
abbrev LogConfig := Runtime.LogConfig

/-- Run an action with a code-based configuration and bracketed logging resources. -/
def run (config : LogConfig := {}) (action : Logger [] α) : IO α :=
  Runtime.run config action

end Loggers
