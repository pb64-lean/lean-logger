import Init.System.Promise

namespace Loggers
namespace Testkit

/-- A one-shot rendezvous that reports entry before waiting for explicit release. -/
structure Gate where
  private entered : IO.Promise Unit
  private released : IO.Promise Unit

/-- Create a closed gate. -/
def Gate.new : IO Gate := do
  pure { entered := ← IO.Promise.new, released := ← IO.Promise.new }

/-- Alias for `Gate.new`. -/
def Gate.create : IO Gate :=
  Gate.new

private def awaitPromise (label : String) (promise : IO.Promise Unit) : IO Unit := do
  match ← IO.wait promise.result? with
  | some () => pure ()
  | none => throw (IO.userError s!"{label} promise was dropped")

/-- Signal that the caller reached the gate, then block until `release`. -/
def Gate.enter (gate : Gate) : IO Unit := do
  gate.entered.resolve ()
  awaitPromise "gate release" gate.released

/-- Wait until a caller has signaled entry. -/
def Gate.waitEntered (gate : Gate) : IO Unit :=
  awaitPromise "gate entry" gate.entered

/-- Open the gate. Repeated releases are harmless. -/
def Gate.release (gate : Gate) : IO Unit :=
  gate.released.resolve ()

end Testkit
end Loggers
