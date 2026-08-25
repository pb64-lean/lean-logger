import Loggers.Runtime.Appender

namespace Loggers
namespace Runtime

/-- Behavior when an asynchronous appender's event capacity is exhausted.

`dropOldest` may evict an event whose earlier offer returned an admitted result
if that event has not yet been removed from the bounded queue. Pending flush
barriers fence eviction: only events after the latest barrier are candidates,
and an incoming event is dropped as `droppedNewest` when none is available. -/
inductive OverflowPolicy where
  | block
  | dropNewest
  | dropOldest
deriving Repr, BEq, DecidableEq, Inhabited

/-- Configuration rejected before an asynchronous worker is started. -/
inductive AsyncConfigError where
  | zeroCapacity
deriving Repr, BEq, DecidableEq, Inhabited

instance : ToString AsyncConfigError where
  toString
    | .zeroCapacity => "asynchronous appender capacity must be positive"

/-- Bounded asynchronous delivery configuration. -/
structure AsyncOptions where
  capacity : Nat := 1024
  overflowPolicy : OverflowPolicy := .block
deriving Repr, BEq, Inhabited

/-- Validate asynchronous delivery configuration without acquiring resources. -/
def AsyncOptions.validate (options : AsyncOptions) : Except AsyncConfigError Unit :=
  if options.capacity = 0 then .error .zeroCapacity else .ok ()

/-- Lifecycle state observed by admission and statistics snapshots. -/
inductive AsyncPhase where
  | open
  | closing
  | closed
  | failed
deriving Repr, BEq, DecidableEq, Inhabited

/-- The exact outcome of one event admission attempt.

`droppedNewest` describes which event was lost, so it can also be returned by
`dropOldest` when a pending flush barrier protects every queued event. -/
inductive Admission where
  | admitted
  | droppedNewest
  | admittedAfterDropOldest
  | rejected (phase : AsyncPhase)
deriving Repr, BEq, DecidableEq, Inhabited

/-- Whether the supplied event entered the queue at the end of its offer.

With `dropOldest`, a later offer may still evict an admitted queued event. -/
def Admission.isAdmitted : Admission → Bool
  | .admitted | .admittedAfterDropOldest => true
  | .droppedNewest | .rejected _ => false

/-- A coherent snapshot of asynchronous delivery counters and queue state. -/
structure AsyncStats where
  phase : AsyncPhase
  queued : Nat
  pendingFlushes : Nat
  offered : Nat
  admitted : Nat
  delivered : Nat
  droppedNewest : Nat
  droppedOldest : Nat
  rejected : Nat
  appendFailures : Nat
  flushFailures : Nat
  closeFailures : Nat
deriving Repr, BEq, Inhabited

private structure Counters where
  offered : Nat := 0
  admitted : Nat := 0
  delivered : Nat := 0
  droppedNewest : Nat := 0
  droppedOldest : Nat := 0
  rejected : Nat := 0
  appendFailures : Nat := 0
  flushFailures : Nat := 0
  closeFailures : Nat := 0

private abbrev BarrierResult := Except IO.Error Unit

private inductive WorkItem where
  | event (event : LogEvent)
  | flush (result : IO.Promise BarrierResult)

private structure AsyncState where
  phase : AsyncPhase := .open
  queue : Std.Queue WorkItem := Std.Queue.empty
  queuedEvents : Nat := 0
  counters : Counters := {}
  failure? : Option IO.Error := none

private structure AsyncShared where
  options : AsyncOptions
  child : StartedAppender
  services : RuntimeServices
  state : Std.Mutex AsyncState
  workAvailable : Std.Condvar
  spaceAvailable : Std.Condvar
  closeResult : IO.Promise BarrierResult

/-- A bounded asynchronous appender and the exact worker that owns its child. -/
structure AsyncAppender where
  name : String
  private shared : AsyncShared
  private worker : Task (Except IO.Error Unit)
  private flushLock : Std.Mutex Unit

private def report
    (shared : AsyncShared)
    (operation : DiagnosticOperation)
    (message : String) : IO Unit :=
  shared.services.report {
    component := shared.child.name
    operation
    message
  }

private def awaitBarrier (promise : IO.Promise BarrierResult) : IO BarrierResult := do
  match ← IO.wait promise.result? with
  | some result => pure result
  | none => pure (.error (IO.userError "asynchronous appender barrier was dropped"))

private def attemptIO (action : IO Unit) : IO (Option IO.Error) := do
  try
    action
    pure none
  catch error =>
    pure (some error)

private def queueFromList (items : List WorkItem) : Std.Queue WorkItem :=
  items.foldl (fun queue item => queue.enqueue item) Std.Queue.empty

private def dropOldestUnfencedEvent
    (queue : Std.Queue WorkItem) : Option (Std.Queue WorkItem) :=
  let rec remove (remaining : List WorkItem) : Bool × Option (List WorkItem) :=
    match remaining with
    | [] => (false, none)
    | item :: rest =>
        let (barrierAfter, removed?) := remove rest
        match item with
        | .flush _ =>
            (true, removed?.map (item :: ·))
        | .event _ =>
            if barrierAfter then
              (true, removed?.map (item :: ·))
            else
              (false, some rest)
  (remove queue.toArray.toList).2.map queueFromList

private def rejectAdmission (phase : AsyncPhase) : Std.AtomicT AsyncState IO Admission := do
  modify fun state => {
    state with counters := { state.counters with rejected := state.counters.rejected + 1 }
  }
  pure (.rejected phase)

private def enqueueEvent
    (shared : AsyncShared)
    (event : LogEvent)
    (admission : Admission := .admitted) : Std.AtomicT AsyncState IO Admission := do
  modify fun state => {
    state with
    queue := state.queue.enqueue (.event event)
    queuedEvents := state.queuedEvents + 1
    counters := { state.counters with admitted := state.counters.admitted + 1 }
  }
  liftM shared.workAvailable.notifyOne
  pure admission

/-- Offer one event and report whether ownership transferred to the worker. -/
def AsyncAppender.offer (appender : AsyncAppender) (event : LogEvent) : IO Admission :=
  appender.shared.state.atomically do
    modify fun state => {
      state with counters := { state.counters with offered := state.counters.offered + 1 }
    }
    let initial ← get
    if initial.phase != .open then
      rejectAdmission initial.phase
    else
      match appender.shared.options.overflowPolicy with
      | .block =>
          appender.shared.spaceAvailable.waitUntil appender.shared.state do
            let state ← get
            pure (state.phase != .open || state.queuedEvents < appender.shared.options.capacity)
          let state ← get
          if state.phase != .open then
            rejectAdmission state.phase
          else
            enqueueEvent appender.shared event
      | .dropNewest =>
          if initial.queuedEvents < appender.shared.options.capacity then
            enqueueEvent appender.shared event
          else
            modify fun state => {
              state with counters := {
                state.counters with droppedNewest := state.counters.droppedNewest + 1
              }
            }
            pure .droppedNewest
      | .dropOldest =>
          if initial.queuedEvents < appender.shared.options.capacity then
            enqueueEvent appender.shared event
          else
            match dropOldestUnfencedEvent initial.queue with
            | none =>
                modify fun state => {
                  state with counters := {
                    state.counters with droppedNewest := state.counters.droppedNewest + 1
                  }
                }
                pure .droppedNewest
            | some remaining =>
                set {
                  initial with
                  queue := remaining
                  queuedEvents := initial.queuedEvents - 1
                  counters := {
                    initial.counters with
                    droppedOldest := initial.counters.droppedOldest + 1
                  }
                }
                enqueueEvent appender.shared event .admittedAfterDropOldest

private def takeWork (shared : AsyncShared) : IO (Option WorkItem) :=
  shared.state.atomically do
    shared.workAvailable.waitUntil shared.state do
      let state ← get
      pure (!state.queue.isEmpty || state.phase != .open)
    let state ← get
    match state.queue.dequeue? with
    | some (item, remaining) =>
        let removesEvent := item matches .event _
        set {
          state with
          queue := remaining
          queuedEvents := if removesEvent then state.queuedEvents - 1 else state.queuedEvents
        }
        if removesEvent then
          liftM shared.spaceAvailable.notifyAll
        pure (some item)
    | none => pure none

private def recordDelivery (shared : AsyncShared) : IO Unit :=
  shared.state.atomically do
    modify fun state => {
      state with counters := { state.counters with delivered := state.counters.delivered + 1 }
    }

private def recordAppendFailure (shared : AsyncShared) : IO Unit :=
  shared.state.atomically do
    modify fun state => {
      state with counters := {
        state.counters with appendFailures := state.counters.appendFailures + 1
      }
    }

private def recordFlushFailure (shared : AsyncShared) : IO Unit :=
  shared.state.atomically do
    modify fun state => {
      state with counters := {
        state.counters with flushFailures := state.counters.flushFailures + 1
      }
    }

private def recordCloseFailure (shared : AsyncShared) : IO Unit :=
  shared.state.atomically do
    modify fun state => {
      state with counters := {
        state.counters with closeFailures := state.counters.closeFailures + 1
      }
    }

private def processWork (shared : AsyncShared) : WorkItem → IO Unit
  | .event event => do
      try
        shared.child.append event
        recordDelivery shared
      catch error =>
        recordAppendFailure shared
        report shared .append (toString error)
  | .flush result => do
      let failure? ← attemptIO shared.child.flush
      match failure? with
      | none => result.resolve (.ok ())
      | some error =>
          recordFlushFailure shared
          result.resolve (.error error)

private def finish
    (shared : AsyncShared)
    (result : BarrierResult) : IO Unit := do
  shared.state.atomically do
    modify fun state => match result with
      | .ok () => { state with phase := .closed, failure? := none }
      | .error error => { state with phase := .failed, failure? := some error }
    liftM shared.spaceAvailable.notifyAll
    liftM shared.workAvailable.notifyAll
  shared.closeResult.resolve result

private def shutdownChild (shared : AsyncShared) : IO Unit := do
  let closeFailure? ← attemptIO shared.child.close
  if closeFailure?.isSome then
    recordCloseFailure shared
  match closeFailure? with
  | none => finish shared (.ok ())
  | some error => finish shared (.error error)

private def workerLoop (shared : AsyncShared) : IO Unit := do
  let mut running := true
  while running do
    match ← takeWork shared with
    | some work => processWork shared work
    | none =>
        running := false
  shutdownChild shared

private def queuedBarriers (queue : Std.Queue WorkItem) : List (IO.Promise BarrierResult) :=
  queue.toArray.toList.filterMap fun
    | .event _ => none
    | .flush result => some result

private def failWorker (shared : AsyncShared) (error : IO.Error) : IO Unit := do
  let barriers ← shared.state.atomically do
    let state ← get
    let barriers := queuedBarriers state.queue
    set {
      state with
      phase := .failed
      queue := Std.Queue.empty
      queuedEvents := 0
      failure? := some error
    }
    liftM shared.spaceAvailable.notifyAll
    liftM shared.workAvailable.notifyAll
    pure barriers
  for barrier in barriers do
    barrier.resolve (.error error)
  report shared .append s!"asynchronous worker failed: {error}"
  let closeFailure? ← attemptIO shared.child.close
  if let some closeError := closeFailure? then
    recordCloseFailure shared
    report shared .close (toString closeError)
  shared.closeResult.resolve (.error error)

private def supervisedWorker (shared : AsyncShared) : IO Unit := do
  try
    workerLoop shared
  catch error =>
    failWorker shared error

/-- Start a bounded worker that takes exclusive lifecycle ownership of `child`. -/
def AsyncAppender.start
    (child : StartedAppender)
    (services : RuntimeServices := {})
    (options : AsyncOptions := {}) : IO AsyncAppender := do
  match options.validate with
  | .error error => throw <| IO.userError (toString error)
  | .ok () => pure ()
  let services ← services.activate
  let shared : AsyncShared := {
    options
    child
    services
    state := ← Std.Mutex.new ({} : AsyncState)
    workAvailable := ← Std.Condvar.new
    spaceAvailable := ← Std.Condvar.new
    closeResult := ← IO.Promise.new
  }
  let worker ← IO.asTask (supervisedWorker shared) .dedicated
  pure {
    name := child.name
    shared
    worker
    flushLock := ← Std.Mutex.new ()
  }

private def enqueueFlushBarrier (appender : AsyncAppender) : IO (IO.Promise BarrierResult) :=
  appender.shared.state.atomically do
    let state ← get
    if state.phase == .open then
      let result ← IO.Promise.new
      set { state with queue := state.queue.enqueue (.flush result) }
      liftM appender.shared.workAvailable.notifyOne
      pure result
    else
      pure appender.shared.closeResult

/-- Process retained queue entries ordered before this barrier, then flush the child.

Under `dropOldest`, an event admitted earlier but evicted before processing is
not covered by this guarantee. Concurrent producers require external
synchronization when a global admission barrier is needed. -/
def AsyncAppender.flush (appender : AsyncAppender) : IO Unit :=
  appender.flushLock.atomically do
    let result ← liftM (awaitBarrier (← enqueueFlushBarrier appender))
    match result with
    | .ok () => pure ()
    | .error error => throw error

private def requestClose (appender : AsyncAppender) : IO Unit :=
  appender.shared.state.atomically do
    let state ← get
    if state.phase == .open then
      set { state with phase := .closing }
      liftM appender.shared.spaceAvailable.notifyAll
      liftM appender.shared.workAvailable.notifyAll

/-- Fence admission, drain queued events, retire the child, and join the exact worker. -/
def AsyncAppender.close (appender : AsyncAppender) : IO Unit := do
  requestClose appender
  let closeResult ← awaitBarrier appender.shared.closeResult
  let workerResult ← IO.wait appender.worker
  match closeResult, workerResult with
  | .ok (), .ok () => pure ()
  | .error error, _ => throw error
  | .ok (), .error error => throw error

/-- Read one coherent statistics and lifecycle snapshot. -/
def AsyncAppender.stats (appender : AsyncAppender) : IO AsyncStats :=
  appender.shared.state.atomically do
    let state ← get
    pure {
      phase := state.phase
      queued := state.queuedEvents
      pendingFlushes := (queuedBarriers state.queue).length
      offered := state.counters.offered
      admitted := state.counters.admitted
      delivered := state.counters.delivered
      droppedNewest := state.counters.droppedNewest
      droppedOldest := state.counters.droppedOldest
      rejected := state.counters.rejected
      appendFailures := state.counters.appendFailures
      flushFailures := state.counters.flushFailures
      closeFailures := state.counters.closeFailures
    }

private def admissionFailure (name : String) : Admission → Option IO.Error
  | .rejected phase => some <| IO.userError s!"asynchronous appender {name} rejected event in {repr phase} phase"
  | .admitted | .droppedNewest | .admittedAfterDropOldest => none

/-- View the asynchronous handle as a standard started appender. -/
def AsyncAppender.asStarted (appender : AsyncAppender) : StartedAppender := {
  name := appender.name
  append := fun event => do
    if let some error := admissionFailure appender.name (← appender.offer event) then
      throw error
  flush := appender.flush
  close := appender.close
}

/-- Decorate an appender specification with bounded asynchronous delivery. -/
def AppenderSpec.async
    (spec : AppenderSpec)
    (options : AsyncOptions := {}) : AppenderSpec :=
  spec.decorate fun services child => do
    return (← AsyncAppender.start child services options).asStarted

end Runtime
end Loggers
