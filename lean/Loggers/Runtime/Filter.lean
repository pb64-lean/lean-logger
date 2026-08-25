import Loggers.Core

namespace Loggers
namespace Runtime

/-- The decision made by one appender filter. -/
inductive FilterReply where
  | accept
  | deny
  | neutral
deriving Repr, BEq, DecidableEq, Inhabited

/-- An effectful predicate over a strict event. -/
structure Filter where
  apply : LogEvent → IO FilterReply

/-- Lift a pure filter into the runtime filter interface. -/
def Filter.pure (filter : LogEvent → FilterReply) : Filter :=
  ⟨fun event => Pure.pure (filter event)⟩

/-- A filter whose decision is constant. -/
def Filter.constant (reply : FilterReply) : Filter :=
  Filter.pure fun _ => reply

/-- Decide by inspecting only the event's top-level properties. -/
def Filter.onEvent (predicate : LogEvent → Bool) : Filter :=
  Filter.pure fun event => if predicate event then .accept else .neutral

/-- Deny events that fail a top-level predicate. -/
def Filter.requireEvent (predicate : LogEvent → Bool) : Filter :=
  Filter.pure fun event => if predicate event then .neutral else .deny

/-- Require an event to meet a severity threshold. -/
def Filter.minLevel (threshold : Level) : Filter :=
  Filter.requireEvent fun event => threshold.enabledBy event.level

/-- Decide by inspecting one canonical context value. -/
def Filter.onContext
    (key : String)
  (predicate : Option LogValue → FilterReply) : Filter :=
  Filter.pure fun event =>
    predicate <| (event.context.find? fun field => field.1 == key).map (fun item => item.2)

/-- Decide by inspecting one canonical event-local field. -/
def Filter.onField
    (key : String)
  (predicate : Option LogValue → FilterReply) : Filter :=
  Filter.pure fun event =>
    predicate <| (event.fields.find? fun field => field.1 == key).map (fun item => item.2)

/-- Evaluate filters in order, stopping at the first decisive reply.

An all-neutral chain accepts the event. -/
def filtersAccept (filters : Array Filter) (event : LogEvent) : IO Bool := do
  for filter in filters do
    match ← filter.apply event with
    | .accept => return true
    | .deny => return false
    | .neutral => pure ()
  return true

end Runtime
end Loggers
