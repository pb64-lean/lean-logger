import Lean.Elab.Term
import Loggers.Context

open Lean Elab Term

namespace Loggers

private def ensureFieldsLabel (label : TSyntax `ident) : MacroM Unit :=
  unless label.getId == `fields do
    Macro.throwErrorAt label "expected 'fields'"

private def validateFieldKeys (keys : Array (TSyntax `str)) : MacroM Unit := do
  let mut seen : List String := []
  for keySyntax in keys do
    let key := keySyntax.getString
    unless isValidStructuredKey key do
      Macro.throwErrorAt keySyntax s!"invalid event field name '{key}'"
    if seen.contains key then
      Macro.throwErrorAt keySyntax <|
        s!"duplicate event field '{key}'; each name may appear once in fields!"
    seen := key :: seen

syntax (name := provenanceStx) "provenance%" : term

/-- Elaborate the lexical declaration, module, file, and source position. -/
@[term_elab provenanceStx] def elabProvenance : TermElab := fun stx expectedType? => do
  let position ← getRefPosition
  let environment ← getEnv
  let declaration := (← getDeclName?).getD environment.mainModule
  let fileName ← getFileName
  let expanded ← `(Loggers.Provenance.mk
    $(quote declaration)
    $(quote environment.mainModule)
    (some $(quote fileName))
    (some $(quote position.line))
    (some $(quote position.column)))
  withMacroExpansion stx expanded <| elabTerm expanded expectedType?

syntax logField := str " := " term
syntax "fields!" "[" logField,* "]" : term

/-- Build heterogeneous event fields while retaining their inferred row. -/
macro_rules
  | `(fields! [$[$keys:str := $values:term],*]) => do
      validateFieldKeys keys
      let mut result ← `(Loggers.EventFields.empty)
      for key in keys, value in values do
        result ← `(Loggers.EventFields.insert $result $key $value)
      pure result

/-- Emit a lazily constructed event with no cause or event-local fields. -/
macro "log!" level:term:max message:interpolatedStr(term) : term =>
  `(Loggers.logEventNamed provenance% $level
      (Thunk.mk fun _ => none)
      (Thunk.mk fun _ => Loggers.EventFields.empty)
      (Thunk.mk fun _ => s! $message))

/-- Emit a lazily constructed event with typed event-local fields. -/
macro "log!" level:term:max message:interpolatedStr(term)
    "(" label:ident ":=" fieldValues:term ")" : term => do
  ensureFieldsLabel label
  `(Loggers.logEventNamed provenance% $level
    (Thunk.mk fun _ => none)
    (Thunk.mk fun _ => $fieldValues)
    (Thunk.mk fun _ => s! $message))

/-- Emit a lazily converted cause with no event-local fields. -/
macro "logErr!" level:term:max error:term:max message:interpolatedStr(term) : term =>
  `(Loggers.logEventNamed provenance% $level
      (Thunk.mk fun _ => some (Loggers.toCause $error))
      (Thunk.mk fun _ => Loggers.EventFields.empty)
      (Thunk.mk fun _ => s! $message))

/-- Emit a lazily converted cause with typed event-local fields. -/
macro "logErr!" level:term:max error:term:max message:interpolatedStr(term)
    "(" label:ident ":=" fieldValues:term ")" : term => do
  ensureFieldsLabel label
  `(Loggers.logEventNamed provenance% $level
    (Thunk.mk fun _ => some (Loggers.toCause $error))
    (Thunk.mk fun _ => $fieldValues)
    (Thunk.mk fun _ => s! $message))

/-- Log only the error branch of an `Except` value and pass it through. -/
macro "logFailure!" level:term:max result:term:max message:interpolatedStr(term) : term =>
  `(Loggers.logFailureNamed provenance% $level $result
      (Thunk.mk fun _ => Loggers.EventFields.empty)
      (Thunk.mk fun _ => s! $message))

/-- Log only the error branch of an `Except` value with typed fields. -/
macro "logFailure!" level:term:max result:term:max message:interpolatedStr(term)
    "(" label:ident ":=" fieldValues:term ")" : term => do
  ensureFieldsLabel label
  `(Loggers.logFailureNamed provenance% $level $result
    (Thunk.mk fun _ => $fieldValues)
    (Thunk.mk fun _ => s! $message))

/-- Log and rethrow an `IO.Error` from an action. -/
macro "tapError!" level:term:max action:term:max message:interpolatedStr(term) : term =>
  `(Loggers.Logger.tapError provenance% $level
      (Thunk.mk fun _ => Loggers.EventFields.empty)
      (Thunk.mk fun _ => s! $message)
      $action)

/-- Log and rethrow an `IO.Error` from an action with typed fields. -/
macro "tapError!" level:term:max action:term:max message:interpolatedStr(term)
    "(" label:ident ":=" fieldValues:term ")" : term => do
  ensureFieldsLabel label
  `(Loggers.Logger.tapError provenance% $level
    (Thunk.mk fun _ => $fieldValues)
    (Thunk.mk fun _ => s! $message)
    $action)

end Loggers
