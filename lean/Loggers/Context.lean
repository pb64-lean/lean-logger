import Std.Data.HashSet
import Loggers.Event

namespace Loggers

/-- A type-level association list used to index heterogeneous values. -/
abbrev Row := List (String × Type)

/-- The row carried by a logging computation. -/
abbrev ContextRow := Row

/-- The row carried by one event's structured fields. -/
abbrev FieldRow := Row

/-- Names present in a row, without inspecting its type components. -/
abbrev Row.keys (row : Row) : List String := row.map (·.1)

/-- Remove every binding with `key` from a row. -/
def Row.eraseKey (row : Row) (key : String) : Row :=
  match row with
  | [] => []
  | (current, valueType) :: rest =>
      if current = key then
        Row.eraseKey rest key
      else
        (current, valueType) :: Row.eraseKey rest key

/-- Runtime storage corresponding exactly to a row. -/
def Env : Row → Type
  | [] => PUnit
  | (_, valueType) :: rest => valueType × Env rest

/-- Evidence that the first visible occurrence of `key` has type `valueType`. -/
class HasKey (row : Row) (key : String) (valueType : outParam Type) where
  private mk ::
  private findImpl : Env row → valueType

/-- Retrieve a typed value using canonical first-visible lookup evidence. -/
private def HasKey.find (key : String) [inst : HasKey row key valueType]
    (env : Env row) : valueType :=
  inst.findImpl env

private instance headHasKey : HasKey ((key, valueType) :: rest) key valueType where
  findImpl env := env.1

private instance (priority := low) tailHasKey [inst : HasKey rest key valueType] :
    HasKey ((other, otherType) :: rest) key valueType where
  findImpl env := inst.findImpl env.2

/-- Policy for a collision between two runtime-provided values. -/
inductive DynamicMergePolicy where
  | reject
  | preserve
  | overwrite
deriving Repr, BEq, DecidableEq, Inhabited

/-- A rejected runtime context or event-field boundary value. -/
inductive DynamicError where
  | invalidName (key : String)
  | duplicateInput (key : String)
  | typedCollision (key : String)
  | dynamicCollision (key : String)
deriving Repr, BEq, Inhabited

instance : ToString DynamicError where
  toString
    | .invalidName key => s!"invalid structured logging key: {key}"
    | .duplicateInput key => s!"duplicate incoming structured logging key: {key}"
    | .typedCollision key => s!"runtime key collides with typed key: {key}"
    | .dynamicCollision key => s!"runtime key collides with existing runtime key: {key}"

private abbrev PendingValue := String × Thunk LogValue

private def isValidKeyChar (char : Char) : Bool :=
  char.isAlphanum || char == '_' || char == '-' || char == '.' || char == ':'

/-- Structured context and event-field keys are deliberately conservative and bounded. -/
def isValidStructuredKey (key : String) : Bool :=
  !key.isEmpty && key.length ≤ 128 && key.toList.all isValidKeyChar

/-- Compatibility name for validation at runtime-computed boundaries. -/
def isValidDynamicKey (key : String) : Bool :=
  isValidStructuredKey key

private def keySetOfPending (pending : List PendingValue) : Std.HashSet String :=
  pending.foldl (fun keys item => keys.insert item.1) {}

private def selectVisiblePending (pending : List PendingValue) : List PendingValue :=
  let step (state : Std.HashSet String × List PendingValue) (item : PendingValue) :=
    if state.1.contains item.1 then
      state
    else
      (state.1.insert item.1, item :: state.2)
  (pending.foldl step ({}, [])).2

private def materializeCanonical
    (pending : List PendingValue)
    (dynamic : List (String × LogValue)) : List (String × LogValue) :=
  let visible := selectVisiblePending pending
  let typedKeys := visible.foldl (fun keys item => keys.insert item.1) ({} : Std.HashSet String)
  let typed := visible.map fun item => (item.1, item.2.get)
  let remaining := dynamic.filter fun item => !typedKeys.contains item.1
  typed ++ remaining

private def replaceDynamic
    (values : List (String × LogValue))
    (key : String)
    (value : LogValue) : List (String × LogValue) :=
  values.map fun item => if item.1 == key then (key, value) else item

private def validateIncoming
    (typedKeys : Std.HashSet String)
    (incoming : List (String × LogValue)) : Except DynamicError Unit := do
  let rec validateNames
      (remaining : List (String × LogValue))
      (seen : Std.HashSet String) : Except DynamicError Unit :=
    match remaining with
    | [] => .ok ()
    | (key, _) :: rest =>
        if !isValidStructuredKey key then
          .error (.invalidName key)
        else if seen.contains key then
          .error (.duplicateInput key)
        else
          validateNames rest (seen.insert key)
  let rec validateTypedCollisions
      (remaining : List (String × LogValue)) : Except DynamicError Unit :=
    match remaining with
    | [] => .ok ()
    | (key, _) :: rest =>
        if typedKeys.contains key then
          .error (.typedCollision key)
        else
          validateTypedCollisions rest
  validateNames incoming {}
  validateTypedCollisions incoming

private def mergeDynamicValues
    (typedKeys : Std.HashSet String)
    (policy : DynamicMergePolicy)
    (existing incoming : List (String × LogValue)) :
    Except DynamicError (List (String × LogValue)) := do
  validateIncoming typedKeys incoming
  let rec merge
      (current : List (String × LogValue))
      (remaining : List (String × LogValue)) :=
    match remaining with
    | [] => .ok current
    | (key, value) :: rest =>
        if current.any fun item => item.1 == key then
          match policy with
          | .reject => .error (.dynamicCollision key)
          | .preserve => merge current rest
          | .overwrite => merge (replaceDynamic current key value) rest
        else
          merge (current ++ [(key, value)]) rest
  merge existing incoming

/-- Typed, event-local structured fields. Construction is smart-constructor only. -/
structure EventFields (row : FieldRow) where
  private mk ::
  private env : Env row
  private pending : List PendingValue
  private dynamic : List (String × LogValue)

/-- An empty event-field set. -/
def EventFields.empty : EventFields [] :=
  { env := .unit, pending := [], dynamic := [] }

/-- Add a fresh typed event field. -/
def EventFields.insert
    (fields : EventFields row)
    (key : String)
    (value : valueType)
    [ToLogValue valueType]
    (_valid : isValidStructuredKey key := by decide)
    (_fresh : key ∉ Row.keys row := by decide) :
    EventFields ((key, valueType) :: row) :=
  { env := (value, fields.env)
    pending := (key, Thunk.mk fun _ => toLogValue value) :: fields.pending
    dynamic := fields.dynamic }

/-- Read a typed event field. -/
def EventFields.get
    (fields : EventFields row)
    (key : String)
    [HasKey row key valueType] : valueType :=
  HasKey.find key fields.env

/-- Validate and merge runtime-provided event fields. -/
def EventFields.mergeDynamic
    (fields : EventFields row)
    (policy : DynamicMergePolicy)
    (incoming : List (String × LogValue)) : Except DynamicError (EventFields row) := do
  let dynamic ← mergeDynamicValues (keySetOfPending fields.pending) policy fields.dynamic incoming
  pure { fields with dynamic }

private def EventFields.materialize (fields : EventFields row) : List (String × LogValue) :=
  materializeCanonical fields.pending fields.dynamic

/-- Effectful capabilities shared by every context in one logging run. -/
structure CoreCtx (m : Type → Type) where
  loggerOverride? : Option String := none
  enabled : String → Level → m Bool
  now : m Std.Time.Timestamp
  sink : LogEvent → m Unit
  close : m Unit

/-- Private context storage indexed by its exact typed row. -/
structure LogCtx (m : Type → Type) (row : ContextRow) where
  private mk ::
  private env : Env row
  private pending : List PendingValue
  private dynamic : List (String × LogValue)
  private core : CoreCtx m

private def LogCtx.root (core : CoreCtx m) : LogCtx m [] :=
  { env := .unit, pending := [], dynamic := [], core }

/-- A logging computation over a caller-selected carrier. -/
abbrev LoggerT (row : ContextRow) (m : Type → Type) (α : Type) :=
  ReaderT (LogCtx m row) m α

/-- The `IO` specialization used by application entry points. -/
abbrev Logger (row : ContextRow) := LoggerT row IO

/-- Run an empty-row computation with an already constructed core. -/
def runWith [Monad m] (core : CoreCtx m) (action : LoggerT [] m α) : m α :=
  action (LogCtx.root core)

private def extendCtx
    (key : String)
    (value : valueType)
    [ToLogValue valueType]
    (ctx : LogCtx m row) : LogCtx m ((key, valueType) :: row) :=
  { env := (value, ctx.env)
    pending := (key, Thunk.mk fun _ => toLogValue value) :: ctx.pending
    dynamic := ctx.dynamic
    core := ctx.core }

/-- Run an action under a fresh typed contextual binding. -/
def pushNew [Monad m]
    (key : String)
    (value : valueType)
    [ToLogValue valueType]
    (action : LoggerT ((key, valueType) :: row) m α)
    (_valid : isValidStructuredKey key := by decide)
    (_fresh : key ∉ Row.keys row := by decide) : LoggerT row m α :=
  ReaderT.adapt (extendCtx key value) action

/-- Deliberately shadow an existing typed contextual binding for one scope. -/
def rebindMDC [Monad m]
    (key : String)
    (value : valueType)
    [ToLogValue valueType]
    [HasKey row key oldType]
    (action : LoggerT ((key, valueType) :: row) m α) : LoggerT row m α :=
  ReaderT.adapt (extendCtx key value) action

/-- Read a statically known contextual binding. -/
def mdc [Monad m]
    (key : String)
    [HasKey row key valueType] : LoggerT row m valueType :=
  fun ctx => pure (HasKey.find key ctx.env)

/-- Read the canonical structured view of a contextual binding. -/
def mdc? [Monad m] (key : String) : LoggerT row m (Option LogValue) :=
  fun ctx =>
    let value := (materializeCanonical ctx.pending ctx.dynamic).find? fun item => item.1 == key
    pure (value.map (·.2))

private def eraseEnv (key : String) : (row : Row) → Env row → Env (Row.eraseKey row key)
  | [], .unit => .unit
  | (current, _) :: rest, (value, env) => by
      simp only [Row.eraseKey]
      split
      · exact eraseEnv key rest env
      · exact (value, eraseEnv key rest env)

private def hideCtx (key : String) (ctx : LogCtx m row) : LogCtx m (Row.eraseKey row key) :=
  { env := eraseEnv key row ctx.env
    pending := ctx.pending.filter fun item => item.1 != key
    dynamic := ctx.dynamic.filter fun item => item.1 != key
    core := ctx.core }

/-- Hide every typed and runtime binding with `key` for one scope. -/
def hideMDC [Monad m]
    (key : String)
    (action : LoggerT (Row.eraseKey row key) m α) : LoggerT row m α :=
  ReaderT.adapt (hideCtx key) action

private def clearCtx (ctx : LogCtx m row) : LogCtx m [] :=
  { env := .unit, pending := [], dynamic := [], core := ctx.core }

/-- Run an action with no contextual bindings. -/
def clearMDC [Monad m] (action : LoggerT [] m α) : LoggerT row m α :=
  ReaderT.adapt clearCtx action

private def mergeDynamicCtx
    (ctx : LogCtx m row)
    (policy : DynamicMergePolicy)
    (incoming : List (String × LogValue)) : Except DynamicError (LogCtx m row) := do
  let dynamic ← mergeDynamicValues (keySetOfPending ctx.pending) policy ctx.dynamic incoming
  pure { ctx with dynamic }

/-- Add one runtime-computed contextual value, rejecting every collision. -/
def withDynMDC [Monad m]
    (key : String)
    (value : LogValue)
    (action : LoggerT row m α) : LoggerT row m (Except DynamicError α) :=
  fun ctx =>
    match mergeDynamicCtx ctx .reject [(key, value)] with
    | .error error => pure (.error error)
    | .ok extended => .ok <$> action extended

/-- Validate and merge runtime-computed contextual values. -/
def mergeDynMDC [Monad m]
    (policy : DynamicMergePolicy)
    (incoming : List (String × LogValue))
    (action : LoggerT row m α) : LoggerT row m (Except DynamicError α) :=
  fun ctx =>
    match mergeDynamicCtx ctx policy incoming with
    | .error error => pure (.error error)
    | .ok extended => .ok <$> action extended

private def withLoggerCtx (name : String) (ctx : LogCtx m row) : LogCtx m row :=
  { ctx with core := { ctx.core with loggerOverride? := some name } }

/-- Override the logger name for one dynamic scope. -/
def withLogger [Monad m]
    (name : String)
    (action : LoggerT row m α) : LoggerT row m α :=
  ReaderT.adapt (withLoggerCtx name) action

/-- An immutable point-in-time context capture. -/
structure Snapshot (m : Type → Type) (row : ContextRow) where
  private mk ::
  private ctx : LogCtx m row

/-- Capture the current context for an explicitly owned callback or task. -/
def capture [Monad m] : LoggerT row m (Snapshot m row) :=
  fun ctx => pure ⟨ctx⟩

/-- Run an action using a captured context. -/
def Snapshot.run (snapshot : Snapshot m row) (action : LoggerT row m α) : m α :=
  action snapshot.ctx

/-- Spawn a task that captures exactly the current context value. -/
def Logger.concurrently
    (action : Logger row α)
    (priority := Task.Priority.default) : Logger row (Task (Except IO.Error α)) :=
  fun ctx => liftM (IO.asTask (action ctx) priority)

/-- Spawn a task from an explicit captured context. -/
def Snapshot.concurrently
    (snapshot : Snapshot IO row)
    (action : Logger row α)
    (priority := Task.Priority.default) : BaseIO (Task (Except IO.Error α)) :=
  IO.asTask (snapshot.run action) priority

/-- Build and emit one event after its level gate accepts it. -/
def logEventNamed [Monad m]
    (site : Provenance)
    (level : Level)
    (cause : Thunk (Option Cause))
    (fields : Thunk (EventFields fieldRow))
    (message : Thunk String) : LoggerT row m Unit :=
  fun ctx => do
    let name := ctx.core.loggerOverride?.getD site.declaration.toString
    if ← ctx.core.enabled name level then
      let eventFields := fields.get
      ctx.core.sink {
        timestamp := (← ctx.core.now)
        level
        logger := name
        provenance := site
        message := message.get
        cause := cause.get
        context := materializeCanonical ctx.pending ctx.dynamic
        fields := eventFields.materialize
      }

/-- Log the error branch of a result and pass the result through unchanged. -/
def logFailureNamed [Monad m] [MonadExceptOf IO.Error m] [ToCause errorType]
    (site : Provenance)
    (level : Level)
    (result : Except errorType α)
    (fields : Thunk (EventFields fieldRow))
    (message : Thunk String) : LoggerT row m (Except errorType α) := do
  match result with
  | .ok _ => pure result
  | .error error =>
      try
        logEventNamed site level
          (Thunk.mk fun _ => some (toCause error))
          fields
          message
      catch _ =>
        pure ()
      pure result

/-- Log an `IO.Error` from an action and rethrow the original error. Logging
failure during this path is observational and cannot replace the primary error. -/
def Logger.tapError
    (site : Provenance)
    (level : Level)
    (fields : Thunk (EventFields fieldRow))
    (message : Thunk String)
    (action : Logger row α) : Logger row α :=
  fun ctx =>
    try
      action ctx
    catch error =>
      try
        logEventNamed site level
          (Thunk.mk fun _ => some (toCause error))
          fields
          message
          ctx
      catch _ =>
        pure ()
      throw error

end Loggers
