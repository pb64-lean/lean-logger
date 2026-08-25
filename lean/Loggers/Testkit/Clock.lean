import Std.Sync.Mutex
import Std.Time

namespace Loggers
namespace Testkit

/-- A deterministic, concurrency-safe clock controlled by a test. -/
structure ManualClock where
  private state : Std.Mutex Std.Time.Timestamp

/-- Create a manual clock at an exact timestamp. -/
def ManualClock.new (initial : Std.Time.Timestamp := 0) : IO ManualClock := do
  pure { state := ← Std.Mutex.new initial }

/-- Alias for `ManualClock.new`. -/
def ManualClock.create (initial : Std.Time.Timestamp := 0) : IO ManualClock :=
  ManualClock.new initial

/-- Read the current timestamp without consulting host time. -/
def ManualClock.now (clock : ManualClock) : IO Std.Time.Timestamp :=
  clock.state.atomically get

/-- Replace the current timestamp. -/
def ManualClock.set (clock : ManualClock) (timestamp : Std.Time.Timestamp) : IO Unit :=
  clock.state.atomically do
    modify fun _ => timestamp

/-- Atomically advance the clock and return the resulting timestamp. -/
def ManualClock.advance
    (clock : ManualClock)
    (duration : Std.Time.Duration) : IO Std.Time.Timestamp :=
  clock.state.atomically do
    modifyGet fun current =>
      let next := current.addDuration duration
      (next, next)

end Testkit
end Loggers
