import Std.Sync.Mutex
import Loggers.Event

namespace Loggers
namespace Testkit

/-- A strict-event buffer safe for concurrent appender calls. -/
structure Capture where
  private buffer : Std.Mutex (Array LogEvent)

/-- Create an empty capture buffer. -/
def Capture.new : IO Capture := do
  pure { buffer := ← Std.Mutex.new #[] }

/-- Append one already-strict event. This function can be used directly as a sink. -/
def Capture.append (capture : Capture) (event : LogEvent) : IO Unit :=
  capture.buffer.atomically do
    modify fun events => events.push event

/-- Return an immutable point-in-time view of all captured events. -/
def Capture.events (capture : Capture) : IO (Array LogEvent) :=
  capture.buffer.atomically get

/-- Remove every captured event. Existing snapshots remain unchanged. -/
def Capture.clear (capture : Capture) : IO Unit :=
  capture.buffer.atomically do
    modify fun _ => #[]

/-- Alias for `Capture.new`. -/
def Capture.create : IO Capture :=
  Capture.new

/-- Alias for `Capture.append`. -/
def Capture.sink (capture : Capture) (event : LogEvent) : IO Unit :=
  capture.append event

/-- Alias for `Capture.events`. -/
def Capture.snapshot (capture : Capture) : IO (Array LogEvent) :=
  capture.events

end Testkit
end Loggers
