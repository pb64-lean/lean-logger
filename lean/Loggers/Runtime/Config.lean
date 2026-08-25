import Std.Data.HashSet
import Loggers.Runtime.Appender

namespace Loggers
namespace Runtime

/-- A configuration error detected before acquiring runtime resources. -/
inductive ConfigError where
  | invalidLoggerPrefix (loggerPrefix : String)
  | duplicateLoggerPrefix (loggerPrefix : String)
  | invalidAppenderName (name : String)
  | duplicateAppenderName (name : String)
deriving Repr, BEq, Inhabited

instance : ToString ConfigError where
  toString
    | .invalidLoggerPrefix loggerPrefix => s!"invalid logger prefix: {loggerPrefix}"
    | .duplicateLoggerPrefix loggerPrefix => s!"duplicate logger prefix: {loggerPrefix}"
    | .invalidAppenderName name => s!"invalid appender name: {name}"
    | .duplicateAppenderName name => s!"duplicate appender name: {name}"

private def validLoggerPrefix (loggerPrefix : String) : Bool :=
  !loggerPrefix.isEmpty && (loggerPrefix.splitOn ".").all fun segment => !segment.isEmpty

/-- A prefix matches only a whole logger name or a dotted segment boundary. -/
def loggerPrefixMatches (loggerPrefix logger : String) : Bool :=
  logger == loggerPrefix || (loggerPrefix ++ ".").isPrefixOf logger

private structure LevelRule where
  loggerPrefix : String
  level : Level

/-- Validated level rules ready for repeated logger-name lookup. -/
structure CompiledLevels where
  private mk ::
  root : Level
  private rules : Array LevelRule

/-- Resolve a logger's threshold by the longest matching dotted prefix. -/
def CompiledLevels.effectiveLevel (levels : CompiledLevels) (logger : String) : Level :=
  let best := levels.rules.foldl (init := none) fun best rule =>
    if loggerPrefixMatches rule.loggerPrefix logger then
      match best with
      | none => some (rule.loggerPrefix.length, rule.level)
      | some (length, _) =>
          if length < rule.loggerPrefix.length then
            some (rule.loggerPrefix.length, rule.level)
          else
            best
    else
      best
  best.map (fun selected => selected.2) |>.getD levels.root

/-- Whether an event passes the effective threshold for its logger. -/
def CompiledLevels.enabled
    (levels : CompiledLevels)
    (logger : String)
    (eventLevel : Level) : Bool :=
  (levels.effectiveLevel logger).enabledBy eventLevel

/-- Validate and compile hierarchical logger thresholds. -/
def compileLevels
    (root : Level)
    (overrides : List (String × Level)) : Except ConfigError CompiledLevels := do
  let rec visit
      (remaining : List (String × Level))
      (seen : Std.HashSet String)
      (rules : Array LevelRule) :=
    match remaining with
    | [] => .ok rules
    | (loggerPrefix, level) :: rest =>
        if !validLoggerPrefix loggerPrefix then
          .error (.invalidLoggerPrefix loggerPrefix)
        else if seen.contains loggerPrefix then
          .error (.duplicateLoggerPrefix loggerPrefix)
        else
          visit rest (seen.insert loggerPrefix) (rules.push ⟨loggerPrefix, level⟩)
  pure ⟨root, ← visit overrides {} #[]⟩

/-- Code-based logging configuration. -/
structure LogConfig where
  root : Level := .info
  overrides : List (String × Level) := []
  appenders : Array AppenderSpec := #[]
  now : IO Std.Time.Timestamp := Std.Time.Timestamp.now
  services : RuntimeServices := {}

/-- A fully validated configuration; starting it may acquire resources. -/
structure CompiledConfig where
  levels : CompiledLevels
  appenders : Array AppenderSpec
  now : IO Std.Time.Timestamp
  services : RuntimeServices

private def validateAppenderNames
    (appenders : Array AppenderSpec) : Except ConfigError Unit := do
  let rec visit (remaining : List AppenderSpec) (seen : Std.HashSet String) :=
    match remaining with
    | [] => .ok ()
    | appender :: rest =>
        if appender.name.isEmpty then
          .error (.invalidAppenderName appender.name)
        else if seen.contains appender.name then
          .error (.duplicateAppenderName appender.name)
        else
          visit rest (seen.insert appender.name)
  visit appenders.toList {}

/-- Validate a logging configuration without performing any effects. -/
def LogConfig.compile (config : LogConfig) : Except ConfigError CompiledConfig := do
  let levels ← compileLevels config.root config.overrides
  validateAppenderNames config.appenders
  pure {
    levels
    appenders := config.appenders
    now := config.now
    services := config.services
  }

end Runtime
end Loggers
