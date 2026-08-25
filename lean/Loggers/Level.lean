namespace Loggers

/-- Severity of a logging event, ordered from least to most severe. -/
inductive Level where
  | trace
  | debug
  | info
  | warn
  | error
deriving Repr, BEq, DecidableEq, Inhabited

/-- Stable numeric ordering used by level gates. -/
def Level.rank : Level → Nat
  | .trace => 0
  | .debug => 1
  | .info => 2
  | .warn => 3
  | .error => 4

instance : Ord Level where
  compare left right := compare left.rank right.rank

/-- Whether an event at `eventLevel` passes `threshold`. -/
def Level.enabledBy (threshold eventLevel : Level) : Bool :=
  threshold.rank ≤ eventLevel.rank

/-- Canonical lowercase level name. -/
def Level.toString : Level → String
  | .trace => "trace"
  | .debug => "debug"
  | .info => "info"
  | .warn => "warn"
  | .error => "error"

/-- Canonical uppercase level name for human-oriented layouts. -/
def Level.toUpperString : Level → String
  | .trace => "TRACE"
  | .debug => "DEBUG"
  | .info => "INFO"
  | .warn => "WARN"
  | .error => "ERROR"

instance : ToString Level where
  toString := Level.toString

/-- Parse an ASCII level name without regard to case. -/
def Level.parse? (value : String) : Option Level :=
  match value.toLower with
  | "trace" => some .trace
  | "debug" => some .debug
  | "info" => some .info
  | "warn" => some .warn
  | "warning" => some .warn
  | "error" => some .error
  | _ => none

end Loggers
