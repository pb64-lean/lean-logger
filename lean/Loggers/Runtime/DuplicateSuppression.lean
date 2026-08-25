import Loggers.Runtime.Appender

namespace Loggers
namespace Runtime

/-- Invalid bounded duplicate-suppression configuration. -/
inductive DuplicateSuppressionConfigError where
  | zeroAllowedPerWindow
  | nonPositiveWindow
  | zeroCapacity
  | invalidStableField (name : String)
  | duplicateStableField (name : String)
deriving Repr, BEq, Inhabited

instance : ToString DuplicateSuppressionConfigError where
  toString
    | .zeroAllowedPerWindow => "duplicate suppression must allow at least one event per window"
    | .nonPositiveWindow => "duplicate suppression window must be positive"
    | .zeroCapacity => "duplicate suppression capacity must be positive"
    | .invalidStableField name => s!"invalid duplicate-suppression stable field: {name}"
    | .duplicateStableField name => s!"duplicate stable-field allowlist entry: {name}"

/-- Bounded duplicate-suppression policy. -/
structure DuplicateSuppressionOptions where
  /-- Originals admitted for one key before denials begin. -/
  allowedPerWindow : Nat := 1
  /-- Fixed window measured only against strict `LogEvent.timestamp` values. -/
  window : Std.Time.Duration := Std.Time.Duration.ofSeconds 60
  /-- Maximum number of keys retained by the deterministic LRU table. -/
  capacity : Nat := 1024
  /-- Stable event-field names added to the otherwise top-level-only key.

  Messages, context, and every event field absent from this list are excluded. -/
  stableFields : List String := []
deriving Repr, Inhabited

/-- Validate duplicate-suppression configuration without acquiring resources. -/
def DuplicateSuppressionOptions.validate
    (options : DuplicateSuppressionOptions) : Except DuplicateSuppressionConfigError Unit := do
  if options.allowedPerWindow = 0 then
    throw .zeroAllowedPerWindow
  if !decide (0 < options.window) then
    throw .nonPositiveWindow
  if options.capacity = 0 then
    throw .zeroCapacity
  let rec validateFields (remaining seen : List String) :=
    match remaining with
    | [] => .ok ()
    | name :: rest =>
        if !isValidDynamicKey name then
          .error (.invalidStableField name)
        else if seen.contains name then
          .error (.duplicateStableField name)
        else
          validateFields rest (name :: seen)
  validateFields options.stableFields []

/-- Lifecycle phase of a started duplicate suppressor. -/
inductive DuplicateSuppressionPhase where
  | open
  | closing
  | closed
  | failed
deriving Repr, BEq, DecidableEq, Inhabited

/-- A coherent snapshot of bounded duplicate-suppression state. -/
structure DuplicateSuppressionStats where
  phase : DuplicateSuppressionPhase
  trackedKeys : Nat
  admitted : Nat
  suppressed : Nat
  suppressionStarts : Nat
  summaries : Nat
  evictions : Nat
  childFailures : Nat
  flushFailures : Nat
  closeFailures : Nat
deriving Repr, BEq, Inhabited

private inductive CauseDiscriminator where
  | absent
  | summary (value : String)
deriving BEq

private structure SuppressionKey where
  logger : String
  provenance : Provenance
  level : Level
  cause : CauseDiscriminator
  stableFields : List (String × Option LogValue)
deriving BEq

private structure SummaryTemplate where
  timestamp : Std.Time.Timestamp
  level : Level
  logger : String
  provenance : Provenance

private structure Entry where
  key : SuppressionKey
  windowStart : Std.Time.Timestamp
  admitted : Nat
  suppressed : Nat
  template : SummaryTemplate

private def summaryTemplate (event : LogEvent) : SummaryTemplate := {
  timestamp := event.timestamp
  level := event.level
  logger := event.logger
  provenance := event.provenance
}

private structure SuppressionCounters where
  admitted : Nat := 0
  suppressed : Nat := 0
  suppressionStarts : Nat := 0
  summaries : Nat := 0
  evictions : Nat := 0
  childFailures : Nat := 0
  flushFailures : Nat := 0
  closeFailures : Nat := 0

private abbrev CloseResult := Except IO.Error Unit

private structure SuppressionState where
  phase : DuplicateSuppressionPhase := .open
  entries : List Entry := []
  inFlight : Nat := 0
  counters : SuppressionCounters := {}
  closeFailure? : Option IO.Error := none

private structure SuppressionShared where
  options : DuplicateSuppressionOptions
  child : StartedAppender
  services : RuntimeServices
  state : Std.Mutex SuppressionState
  deliveriesDrained : IO.Promise Unit
  closeResult : IO.Promise CloseResult

/-- A bounded duplicate suppressor that owns one started child appender. -/
structure DuplicateSuppressor where
  name : String
  private shared : SuppressionShared

private def causeDiscriminator (cause : Option Cause) : CauseDiscriminator :=
  match cause with
  | none => .absent
  | some value => .summary value.summary

private def findField? (event : LogEvent) (name : String) : Option LogValue :=
  (event.fields.find? fun field => field.1 == name).map (·.2)

private def suppressionKey
    (options : DuplicateSuppressionOptions)
    (event : LogEvent) : SuppressionKey := {
  logger := event.logger
  provenance := event.provenance
  level := event.level
  cause := causeDiscriminator event.cause
  stableFields := options.stableFields.map fun name => (name, findField? event name)
}

private def takeEntry
    (key : SuppressionKey)
    (entries : List Entry) : Option (Entry × List Entry) :=
  let rec visit (remaining prefixRev : List Entry) :=
    match remaining with
    | [] => none
    | entry :: rest =>
        if entry.key == key then
          some (entry, prefixRev.reverse ++ rest)
        else
          visit rest (entry :: prefixRev)
  visit entries []

private def popLeastRecent (entries : List Entry) : Option (Entry × List Entry) :=
  match entries.reverse with
  | [] => none
  | entry :: rest => some (entry, rest.reverse)

private def windowExpired
    (entry : Entry)
    (timestamp : Std.Time.Timestamp)
    (window : Std.Time.Duration) : Bool :=
  decide (entry.windowStart.addDuration window ≤ timestamp)

private def suppressionStart (event : LogEvent) : LogEvent := {
  timestamp := event.timestamp
  level := event.level
  logger := event.logger
  provenance := event.provenance
  message := "duplicate event suppression started"
  cause := none
  context := ([] : List (String × LogValue))
  «fields» := [("suppressionPhase", .str "start")]
}

private def suppressionSummary
    (entry : Entry)
    (timestamp : Std.Time.Timestamp)
    (phase : String) : LogEvent := {
  timestamp := timestamp
  level := entry.template.level
  logger := entry.template.logger
  provenance := entry.template.provenance
  message := "duplicate event suppression summary"
  cause := none
  context := ([] : List (String × LogValue))
  «fields» := [
    ("suppressionPhase", .str phase),
    ("suppressedCount", .nat entry.suppressed),
  ]
}

private structure DeliveryPlan where
  synthetic : Array LogEvent := #[]
  original? : Option LogEvent := none

private def planNewKey
    (shared : SuppressionShared)
    (state : SuppressionState)
    (key : SuppressionKey)
    (event : LogEvent) : SuppressionState × DeliveryPlan :=
  let newEntry : Entry := {
    key
    windowStart := event.timestamp
    admitted := 1
    suppressed := 0
    template := summaryTemplate event
  }
  if state.entries.length < shared.options.capacity then
    ({
      state with
      entries := newEntry :: state.entries
      counters := { state.counters with admitted := state.counters.admitted + 1 }
    }, { original? := some event })
  else
    match popLeastRecent state.entries with
    | none =>
        ({
          state with
          entries := [newEntry]
          counters := { state.counters with admitted := state.counters.admitted + 1 }
        }, { original? := some event })
    | some (evicted, remaining) =>
        let hasSummary := evicted.suppressed > 0
        let synthetic :=
          if hasSummary then
            #[suppressionSummary evicted event.timestamp "evicted"]
          else
            #[]
        ({
          state with
          entries := newEntry :: remaining
          counters := {
            state.counters with
            admitted := state.counters.admitted + 1
            evictions := state.counters.evictions + 1
            summaries := state.counters.summaries + if hasSummary then 1 else 0
          }
        }, { synthetic, original? := some event })

private def planExistingKey
    (shared : SuppressionShared)
    (state : SuppressionState)
    (entry : Entry)
    (remaining : List Entry)
    (event : LogEvent) : SuppressionState × DeliveryPlan :=
  if windowExpired entry event.timestamp shared.options.window then
    let hasSummary := entry.suppressed > 0
    let reset : Entry := {
      entry with
      windowStart := event.timestamp
      admitted := 1
      suppressed := 0
      template := summaryTemplate event
    }
    let synthetic :=
      if hasSummary then #[suppressionSummary entry event.timestamp "resumed"] else #[]
    ({
      state with
      entries := reset :: remaining
      counters := {
        state.counters with
        admitted := state.counters.admitted + 1
        summaries := state.counters.summaries + if hasSummary then 1 else 0
      }
    }, { synthetic, original? := some event })
  else if entry.admitted < shared.options.allowedPerWindow then
    let updated := {
      entry with admitted := entry.admitted + 1, template := summaryTemplate event
    }
    ({
      state with
      entries := updated :: remaining
      counters := { state.counters with admitted := state.counters.admitted + 1 }
    }, { original? := some event })
  else
    let firstDenial := entry.suppressed = 0
    let updated := {
      entry with suppressed := entry.suppressed + 1, template := summaryTemplate event
    }
    let synthetic := if firstDenial then #[suppressionStart event] else #[]
    ({
      state with
      entries := updated :: remaining
      counters := {
        state.counters with
        suppressed := state.counters.suppressed + 1
        suppressionStarts := state.counters.suppressionStarts + if firstDenial then 1 else 0
      }
    }, { synthetic })

private def decideEvent (shared : SuppressionShared) (event : LogEvent) : IO DeliveryPlan :=
  shared.state.atomically do
    let state ← get
    if state.phase != .open then
      throw <| IO.userError s!"duplicate suppressor {shared.child.name} is not open"
    let key := suppressionKey shared.options event
    let (next, plan) := match takeEntry key state.entries with
      | none => planNewKey shared state key event
      | some (entry, remaining) => planExistingKey shared state entry remaining event
    set { next with inFlight := state.inFlight + 1 }
    pure plan

private def report
    (shared : SuppressionShared)
    (operation : DiagnosticOperation)
    (error : IO.Error) : IO Unit :=
  shared.services.report {
    component := shared.child.name
    operation
    message := toString error
  }

private def recordChildFailure
    (shared : SuppressionShared)
    (operation : DiagnosticOperation) : IO Unit :=
  shared.state.atomically do
    modify fun state => {
      state with counters := match operation with
        | .append => {
            state.counters with childFailures := state.counters.childFailures + 1
          }
        | .flush => {
            state.counters with flushFailures := state.counters.flushFailures + 1
          }
        | .close => {
            state.counters with closeFailures := state.counters.closeFailures + 1
          }
        | .startup => state.counters
    }

private def appendChild (shared : SuppressionShared) (event : LogEvent) : IO Unit := do
  try
    shared.child.append event
  catch error =>
    recordChildFailure shared .append
    report shared .append error

private def deliverPlan (shared : SuppressionShared) (plan : DeliveryPlan) : IO Unit := do
  for event in plan.synthetic do
    appendChild shared event
  if let some event := plan.original? then
    appendChild shared event

private def releaseDelivery (shared : SuppressionShared) : IO Unit :=
  shared.state.atomically do
    let state ← get
    let remaining := state.inFlight - 1
    set { state with inFlight := remaining }
    if state.phase != .open && remaining == 0 then
      liftM (shared.deliveriesDrained.resolve ())

/-- Apply one atomic suppression decision, then call the child without holding state locks.

Synthetic records precede the original from the same call. Deliveries from
concurrent calls may interleave according to the child's concurrency policy.
The `admitted` counter records suppression decisions; an unsuccessful child
delivery is recorded separately as a child failure. -/
def DuplicateSuppressor.append
    (suppressor : DuplicateSuppressor)
    (event : LogEvent) : IO Unit := do
  let plan ← decideEvent suppressor.shared event
  try
    deliverPlan suppressor.shared plan
  catch error =>
    releaseDelivery suppressor.shared
    throw error
  releaseDelivery suppressor.shared

private def awaitClose (shared : SuppressionShared) : IO CloseResult := do
  match ← IO.wait shared.closeResult.result? with
  | some result => pure result
  | none => pure (.error (IO.userError "duplicate suppressor close result was dropped"))

private inductive FlushDisposition where
  | completed (failure? : Option IO.Error)
  | awaitClose

private def currentPhase (shared : SuppressionShared) : IO DuplicateSuppressionPhase :=
  shared.state.atomically do
    pure (← get).phase

/-- Forward a flush while open, or await an in-progress close.

Callers that require append/flush ordering must not invoke them concurrently. -/
def DuplicateSuppressor.flush (suppressor : DuplicateSuppressor) : IO Unit := do
  let phase ← currentPhase suppressor.shared
  let disposition : FlushDisposition ←
    if phase != DuplicateSuppressionPhase.open then
      pure FlushDisposition.awaitClose
    else do
      let failure? ← do
        try
          suppressor.shared.child.flush
          pure none
        catch error =>
          recordChildFailure suppressor.shared .flush
          pure (some error)
      pure (FlushDisposition.completed failure?)
  match disposition with
  | .completed none => pure ()
  | .completed (some error) => throw error
  | .awaitClose =>
      match ← awaitClose suppressor.shared with
      | .ok () => pure ()
      | .error error => throw error

private def beginClose (shared : SuppressionShared) : IO Bool :=
  shared.state.atomically do
    let state ← get
    if state.phase == .open then
      set { state with phase := .closing }
      if state.inFlight == 0 then
        liftM (shared.deliveriesDrained.resolve ())
      pure true
    else
      pure false

private def closeSummaries (shared : SuppressionShared) : IO (Array LogEvent) :=
  shared.state.atomically do
    let state ← get
    let summaries := state.entries.reverse.foldl (init := #[]) fun summaries entry =>
      if entry.suppressed > 0 then
        summaries.push (suppressionSummary entry entry.template.timestamp "closed")
      else
        summaries
    set {
      state with
      entries := []
      counters := {
        state.counters with summaries := state.counters.summaries + summaries.size
      }
    }
    pure summaries

private def completeClose (shared : SuppressionShared) (result : CloseResult) : IO Unit := do
  shared.state.atomically do
    modify fun state => match result with
      | .ok () => { state with phase := .closed, closeFailure? := none }
      | .error error => { state with phase := .failed, closeFailure? := some error }
  shared.closeResult.resolve result

private def awaitDeliveries (shared : SuppressionShared) : IO Unit := do
  match ← IO.wait shared.deliveriesDrained.result? with
  | some () => pure ()
  | none => throw <| IO.userError "duplicate suppressor delivery-drain promise was dropped"

private def closeOwner
    (suppressor : DuplicateSuppressor)
    (upstreamFinalEvents : Array LogEvent) : IO Unit := do
  suppressor.shared.child.quiesce
  awaitDeliveries suppressor.shared
  let summaries ← closeSummaries suppressor.shared
  let finalEvents := summaries ++ upstreamFinalEvents
  let failure? ← do
    try
      if !(← suppressor.shared.child.tryCloseAfter finalEvents) then
        for event in finalEvents do
          appendChild suppressor.shared event
        suppressor.shared.child.close
      pure none
    catch error =>
      recordChildFailure suppressor.shared .close
      pure (some error)
  completeClose suppressor.shared <| match failure? with
    | none => .ok ()
    | some error => .error error

/-- Fence new decisions, quiesce blocking child admission, await every selected
delivery, then atomically hand final summaries to the child's close lifecycle.

The first close caller owns any supplied terminal records. Concurrent and later
callers share its exact result. -/
def DuplicateSuppressor.closeAfter
    (suppressor : DuplicateSuppressor)
    (upstreamFinalEvents : Array LogEvent) : IO Unit := do
  if ← beginClose suppressor.shared then
    try
      closeOwner suppressor upstreamFinalEvents
    catch error =>
      completeClose suppressor.shared (.error error)
  match ← awaitClose suppressor.shared with
  | .ok () => pure ()
  | .error error => throw error

/-- Close without additional owner-supplied terminal records. -/
def DuplicateSuppressor.close (suppressor : DuplicateSuppressor) : IO Unit :=
  suppressor.closeAfter #[]

/-- Propagate owner quiescence without fencing suppression decisions itself. -/
def DuplicateSuppressor.quiesce (suppressor : DuplicateSuppressor) : IO Unit :=
  suppressor.shared.child.quiesce

/-- Read a coherent statistics and lifecycle snapshot. -/
def DuplicateSuppressor.stats
    (suppressor : DuplicateSuppressor) : IO DuplicateSuppressionStats :=
  suppressor.shared.state.atomically do
    let state ← get
    pure {
      phase := state.phase
      trackedKeys := state.entries.length
      admitted := state.counters.admitted
      suppressed := state.counters.suppressed
      suppressionStarts := state.counters.suppressionStarts
      summaries := state.counters.summaries
      evictions := state.counters.evictions
      childFailures := state.counters.childFailures
      flushFailures := state.counters.flushFailures
      closeFailures := state.counters.closeFailures
    }

/-- Start a bounded suppressor that assumes lifecycle ownership of `child`. -/
def DuplicateSuppressor.start
    (child : StartedAppender)
    (services : RuntimeServices := {})
    (options : DuplicateSuppressionOptions := {}) : IO DuplicateSuppressor := do
  match options.validate with
  | .error error => throw <| IO.userError (toString error)
  | .ok () => pure ()
  let services ← services.activate
  let shared : SuppressionShared := {
    options
    child
    services
    state := ← Std.Mutex.new ({} : SuppressionState)
    deliveriesDrained := ← IO.Promise.new
    closeResult := ← IO.Promise.new
  }
  pure {
    name := child.name
    shared
  }

/-- View the suppressor as a standard started appender. -/
def DuplicateSuppressor.asStarted (suppressor : DuplicateSuppressor) : StartedAppender :=
  ({
    name := suppressor.name
    append := suppressor.append
    flush := suppressor.flush
    quiesce := suppressor.quiesce
    close := suppressor.close
  } : StartedAppender).withTerminalBatch suppressor.closeAfter

/-- Decorate an appender specification with bounded duplicate suppression. -/
def AppenderSpec.suppressDuplicates
    (spec : AppenderSpec)
    (options : DuplicateSuppressionOptions := {}) : AppenderSpec :=
  spec.decorate fun services child => do
    return (← DuplicateSuppressor.start child services options).asStarted

end Runtime
end Loggers
