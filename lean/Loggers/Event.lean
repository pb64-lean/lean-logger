import Std.Time
import Loggers.Level
import Loggers.Value

namespace Loggers

/-- Structured failure information associated with an event. -/
structure Cause where
  summary : String
  detail : Option LogValue := none
  inner : Option Cause := none
deriving Repr, BEq, Inhabited

/-- Converts an error value into structured failure information. -/
class ToCause (ε : Type u) where
  toCause : ε → Cause

export ToCause (toCause)

instance : ToCause IO.Error where
  toCause error := { summary := toString error }

instance : ToCause String where
  toCause summary := { summary }

/-- Compile-time identity and source position of an event site. -/
structure Provenance where
  declaration : Lean.Name
  module : Lean.Name
  file? : Option String := none
  line? : Option Nat := none
  column? : Option Nat := none
deriving Repr, BEq, Inhabited

/-- A fully strict event suitable for filters, queues, and appenders. -/
structure LogEvent where
  timestamp : Std.Time.Timestamp
  level : Level
  logger : String
  provenance : Provenance
  message : String
  cause : Option Cause := none
  context : List (String × LogValue) := []
  fields : List (String × LogValue) := []
deriving Repr, BEq, Inhabited

end Loggers
