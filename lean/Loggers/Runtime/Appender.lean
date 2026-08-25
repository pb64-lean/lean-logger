import Std.Sync.Mutex
import Loggers.Format
import Loggers.Runtime.Filter

namespace Loggers
namespace Runtime

/-- Runtime operation associated with an observational diagnostic. -/
inductive DiagnosticOperation where
  | startup
  | append
  | flush
  | close
deriving Repr, BEq, DecidableEq, Inhabited

/-- A failure observed by logging infrastructure itself. -/
structure Diagnostic where
  component : String
  operation : DiagnosticOperation
  message : String
deriving Repr, BEq, Inhabited

/-- Services supplied while starting appenders.

Diagnostic hooks are best-effort, nonblocking health observations. They must
not be relied on as a durable event channel. -/
structure RuntimeServices where
  diagnostic : Diagnostic → IO Unit := fun _ => pure ()
  private diagnosticGuard? : Option (Std.Mutex Bool) := none

private initialize fallbackDiagnosticGuard : Std.Mutex Bool ←
  Std.Mutex.new false

/-- Install or reuse the single-active diagnostic guard for one runtime tree. -/
def RuntimeServices.activate (services : RuntimeServices) : BaseIO RuntimeServices := do
  if services.diagnosticGuard?.isSome then
    pure services
  else
    pure { services with diagnosticGuard? := some (← Std.Mutex.new false) }

private def claimDiagnostic (guard : Std.Mutex Bool) : IO Bool :=
  guard.atomically do
    if ← get then
      pure false
    else
      set true
      pure true

private def releaseDiagnostic (guard : Std.Mutex Bool) : IO Unit :=
  guard.atomically do set false

/-- Report an infrastructure failure without propagating hook failures.

While a hook is active, both recursive and concurrently overlapping reports
from the same runtime tree are dropped. Started components activate a
tree-local guard; callers using `report` directly should activate services as
well, because otherwise unactivated values share a process fallback guard. -/
def RuntimeServices.report (services : RuntimeServices) (diagnostic : Diagnostic) : IO Unit := do
  let guard := services.diagnosticGuard?.getD fallbackDiagnosticGuard
  if ← claimDiagnostic guard then
    try
      services.diagnostic diagnostic
    catch _ =>
      pure ()
    releaseDiagnostic guard

/-- Unserialized operations owned by one appender. -/
structure AppenderTarget where
  append : LogEvent → IO Unit
  flush : IO Unit := pure ()
  close : IO Unit := pure ()

/-- An encoded destination used by files and application-defined byte sinks. -/
structure ByteSink where
  write : ByteArray → IO Unit
  flush : IO Unit := pure ()
  close : IO Unit := pure ()

private structure SerializedState where
  closed : Bool := false
  closeFailure? : Option IO.Error := none

/-- The operations exposed by an acquired appender.

Each implementation owns its concurrency and lifecycle policy. This makes it
possible for decorators with blocking admission to wake producers during close.
`quiesce` must be idempotent and prompt. It fences or wakes blocking admission
without releasing resources, so routes already admitted by an owning runtime
can finish before final close. Blocking decorators must propagate it to their
children and must not fail it.
`close` must fence new admission, drain owned work, flush, release resources,
and be idempotent; callers therefore do not issue a separate final flush. -/
structure StartedAppender where
  name : String
  append : LogEvent → IO Unit
  flush : IO Unit := pure ()
  quiesce : IO Unit := pure ()
  close : IO Unit := pure ()
  private closeAfterImpl? : Option (Array LogEvent → IO Unit) := none

/-- Install an owner-only terminal-batch close implementation.

Decorators with blocking admission use this hook to accept strict final records
and fence ordinary producers in one lifecycle transition. -/
def StartedAppender.withTerminalBatch
    (appender : StartedAppender)
    (closeAfter : Array LogEvent → IO Unit) : StartedAppender :=
  { appender with closeAfterImpl? := some closeAfter }

private def attempt (action : IO Unit) : IO (Option IO.Error) := do
  try
    action
    pure none
  catch error =>
    pure (some error)

/-- Use an installed atomic terminal-batch close, returning `false` without
effects when the appender has only the sequential fallback. -/
def StartedAppender.tryCloseAfter
    (appender : StartedAppender)
    (finalEvents : Array LogEvent) : IO Bool := do
  match appender.closeAfterImpl? with
  | some closeAfter =>
      closeAfter finalEvents
      pure true
  | none => pure false

/-- Deliver owner-supplied final records and close through one lifecycle operation.

The default is a best-effort sequential fallback. Lifecycle-aware decorators
with blocking admission install an atomic implementation. This operation is
owner-only and is called in place of `close`, never in addition to it. -/
def StartedAppender.closeAfter
    (appender : StartedAppender)
    (finalEvents : Array LogEvent) : IO Unit := do
  match appender.closeAfterImpl? with
  | some closeAfter => closeAfter finalEvents
  | none =>
      let mut appendFailure? : Option IO.Error := none
      for event in finalEvents do
        try
          appender.append event
        catch error =>
          if appendFailure?.isNone then
            appendFailure? := some error
      let closeFailure? ← attempt appender.close
      match appendFailure?, closeFailure? with
      | none, none => pure ()
      | some error, none | none, some error => throw error
      | some appendError, some closeError =>
          throw <| IO.userError <|
            s!"appender {appender.name} failed to deliver a terminal record ({appendError}) " ++
            s!"and close ({closeError})"

private def combineFailures
    (name : String)
    (flushFailure? closeFailure? : Option IO.Error) : Option IO.Error :=
  match flushFailure?, closeFailure? with
  | none, none => none
  | some error, none => some error
  | none, some error => some error
  | some flushError, some closeError =>
      some <| IO.userError
        s!"appender {name} failed to flush ({flushError}) and close ({closeError})"

/-- Wrap raw operations in a serialized, exactly-once lifecycle boundary. -/
def StartedAppender.serialized
    (name : String)
    (target : AppenderTarget) : BaseIO StartedAppender := do
  let state ← Std.Mutex.new ({} : SerializedState)
  pure {
    name
    append := fun event => state.atomically do
      if (← get).closed then
        throw <| IO.userError s!"appender {name} is closed"
      liftM (target.append event)
    flush := state.atomically do
      let current ← get
      if current.closed then
        match current.closeFailure? with
        | some error => throw error
        | none => pure ()
      else
        liftM target.flush
    close := state.atomically do
      let current ← get
      if current.closed then
        match current.closeFailure? with
        | some error => throw error
        | none => pure ()
      else
        let flushFailure? ← liftM (attempt target.flush)
        let closeFailure? ← liftM (attempt target.close)
        let failure? := combineFailures name flushFailure? closeFailure?
        set ({ closed := true, closeFailure? := failure? } : SerializedState)
        match failure? with
        | some error => throw error
        | none => pure ()
  }

/-- Compatibility spelling for constructing a serialized synchronous appender. -/
abbrev StartedAppender.ofTarget := StartedAppender.serialized

/-- Guard a started appender without changing its lifecycle or serialization.

Filters run before ordinary child admission and outside the child's lifecycle
boundary. Owner-only terminal records and records synthesized inside a
decorator bypass this outer filter chain. Filters should be pure, prompt, and
concurrency-safe. An append racing with an unsynchronized direct close may
finish filtering after the child has fenced admission. -/
def StartedAppender.withFilters
    (appender : StartedAppender)
    (filters : Array Filter) : StartedAppender := {
  appender with
  append := fun event => do
    if ← filtersAccept filters event then
      appender.append event
}

/-- A declaration that acquires a complete started appender.

Filters remain declarative so repeated additions retain their source order and
are installed outside any started decorators. -/
structure AppenderSpec where
  private mk ::
  name : String
  private startImpl : RuntimeServices → IO StartedAppender
  private filters : Array Filter := #[]

/-- Construct a serialized appender from application-defined synchronous operations. -/
def AppenderSpec.custom
    (name : String)
    (acquire : RuntimeServices → IO AppenderTarget) : AppenderSpec :=
  ⟨name, fun services => do
    StartedAppender.serialized name (← acquire services), #[]⟩

/-- Guard an appender with an ordered filter chain. -/
def AppenderSpec.withFilters (spec : AppenderSpec) (filters : Array Filter) : AppenderSpec :=
  { spec with filters := spec.filters ++ filters }

/-- Guard an appender with one additional filter. -/
def AppenderSpec.withFilter (spec : AppenderSpec) (filter : Filter) : AppenderSpec :=
  spec.withFilters #[filter]

/-- Transform a started child while preserving the configured appender name.

If decorator construction fails, the acquired child is closed before the
construction error is rethrown. A secondary close failure is only diagnostic. -/
def AppenderSpec.mapStarted
    (spec : AppenderSpec)
    (transform : RuntimeServices → StartedAppender → IO StartedAppender) : AppenderSpec :=
  ⟨spec.name, (fun services => do
    let child ← spec.startImpl services
    try
      let decorated ← transform services child
      pure { decorated with name := spec.name }
    catch error =>
      try
        child.close
      catch closeError =>
        services.report {
          component := child.name
          operation := .close
          message := toString closeError
        }
      throw error
  ), spec.filters⟩

/-- Alias emphasizing that a started transformation installs a decorator. -/
abbrev AppenderSpec.decorate := AppenderSpec.mapStarted

/-- Acquire a declared appender and install its complete ordered filter chain. -/
def AppenderSpec.start
    (spec : AppenderSpec)
    (services : RuntimeServices) : IO StartedAppender := do
  let services ← services.activate
  let appender ← spec.startImpl services
  pure (appender.withFilters spec.filters)

/-- Construct an application-defined encoded appender. -/
def AppenderSpec.encoded
    (name : String)
    (encoder : Format.Encoder)
    (acquire : RuntimeServices → IO ByteSink) : AppenderSpec :=
  AppenderSpec.custom name fun services => do
    let sink ← acquire services
    pure {
      append := fun event => sink.write (encoder event)
      flush := sink.flush
      close := sink.close
    }

/-- Standard output or standard error. -/
inductive ConsoleTarget where
  | stdout
  | stderr
deriving Repr, BEq, DecidableEq, Inhabited

/-- Construct a console appender and capture its stream when the runtime starts. -/
def AppenderSpec.console
    (name : String)
    (target : ConsoleTarget)
    (layout : Format.Layout) : AppenderSpec :=
  AppenderSpec.custom name fun _ => do
    let stream ← match target with
      | .stdout => IO.getStdout
      | .stderr => IO.getStderr
    pure {
      append := fun event => stream.putStr (layout event)
      flush := stream.flush
    }

/-- Whether a file appender truncates or extends an existing file at startup. -/
inductive FileMode where
  | truncate
  | append
deriving Repr, BEq, DecidableEq, Inhabited

/-- Construct a serialized file appender. -/
def AppenderSpec.file
    (name : String)
    (path : System.FilePath)
    (encoder : Format.Encoder)
    (mode : FileMode := .append) : AppenderSpec :=
  AppenderSpec.encoded name encoder fun _ => do
    let handle ← IO.FS.Handle.mk path <| match mode with
      | .truncate => .write
      | .append => .append
    let handleRef ← IO.mkRef (some handle)
    let withHandle (action : IO.FS.Handle → IO Unit) : IO Unit := do
      match ← handleRef.get with
      | some current => action current
      | none => throw <| IO.userError s!"file appender {name} is closed"
    pure {
      write := fun bytes => withHandle fun current => current.write bytes
      flush := withHandle fun current => current.flush
      close := handleRef.set none
    }

/-- Route an event to every appender, isolating one appender's failure from the rest. -/
def routeEvent
    (services : RuntimeServices)
    (appenders : Array StartedAppender)
    (event : LogEvent) : IO Unit := do
  for appender in appenders do
    try
      appender.append event
    catch error =>
      services.report {
        component := appender.name
        operation := .append
        message := toString error
      }

end Runtime
end Loggers
