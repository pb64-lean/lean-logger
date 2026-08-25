namespace Loggers

/-- Strict JSON-shaped data retained by an accepted logging event. -/
inductive LogValue where
  | null
  | str (value : String)
  | int (value : Int)
  | nat (value : Nat)
  | float (value : Float)
  | bool (value : Bool)
  | arr (values : Array LogValue)
  | obj (fields : Array (String × LogValue))
deriving Repr, BEq, Inhabited

/-- Converts an application value to its strict structured logging form. -/
class ToLogValue (α : Type u) where
  toLogValue : α → LogValue

export ToLogValue (toLogValue)

instance : ToLogValue LogValue where
  toLogValue := id

instance : ToLogValue String where
  toLogValue := .str

instance : ToLogValue Bool where
  toLogValue := .bool

instance : ToLogValue Int where
  toLogValue := .int

instance : ToLogValue Nat where
  toLogValue := .nat

instance : ToLogValue UInt8 where
  toLogValue value := .nat value.toNat

instance : ToLogValue UInt16 where
  toLogValue value := .nat value.toNat

instance : ToLogValue UInt32 where
  toLogValue value := .nat value.toNat

instance : ToLogValue UInt64 where
  toLogValue value := .nat value.toNat

instance : ToLogValue Float where
  toLogValue := .float

instance [ToLogValue α] : ToLogValue (Option α) where
  toLogValue
    | none => .null
    | some value => toLogValue value

instance [ToLogValue α] : ToLogValue (Array α) where
  toLogValue values := .arr (values.map toLogValue)

instance [ToLogValue α] : ToLogValue (List α) where
  toLogValue values := .arr (values.toArray.map toLogValue)

instance : ToLogValue Unit where
  toLogValue _ := .null

/-- A value whose default structured representation is always redacted. -/
structure Secret (α : Type u) where
  private mk ::
  private value : α

/-- Protect a value from accidental structured rendering. -/
def Secret.protect (value : α) : Secret α := ⟨value⟩

/-- Explicitly recover a protected value for its intended application use. -/
def Secret.reveal (secret : Secret α) : α := secret.value

instance : ToLogValue (Secret α) where
  toLogValue _ := .str "***"

end Loggers
