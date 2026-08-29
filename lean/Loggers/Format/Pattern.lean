import Lean.Elab.Term
import Loggers.Format.Text

namespace Loggers
namespace Format

/-- Optional vocabularies used to reject misspelled named conversions. -/
structure PatternSchemas where
  context? : Option (List String) := none
  field? : Option (List String) := none
deriving Repr, BEq, Inhabited

/-- A source-relative pattern compilation error. -/
structure PatternError where
  offset : Nat
  message : String
deriving Repr, BEq, Inhabited

instance : ToString PatternError where
  toString error := s!"pattern offset {error.offset}: {error.message}"

/-- Minimum/maximum width and padding alignment for one conversion. -/
structure PatternWidth where
  leftAlign : Bool := false
  minimum? : Option Nat := none
  maximum? : Option Nat := none
deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- Apply truncation first, then the requested minimum-width padding. -/
def PatternWidth.apply (width : PatternWidth) (value : String) : String :=
  let value :=
    match width.maximum? with
    | some maximum => if value.length > maximum then (value.takeEnd maximum).toString else value
    | none => value
  match width.minimum? with
  | none => value
  | some minimum =>
      if width.leftAlign then padRight value minimum else padLeft value minimum

/-- A validated date-time format retained in its parsed representation. -/
structure DatePattern where
  source : String
  format : Std.Time.GenericFormat .any
deriving Inhabited

instance : Repr DatePattern where
  reprPrec pattern _ := repr pattern.source

/-- Runtime-free conversion selected by a compiled pattern. -/
inductive PatternConversion where
  | date (pattern : DatePattern)
  | level
  | logger
  | message
  | cause
  | contextValue (key : String)
  | context
  | fieldValue (key : String)
  | fieldSet
deriving Repr, Inhabited

/-- One already parsed portion of a logging pattern. -/
inductive PatternPart where
  | literal (value : String)
  | newline
  | conversion (width : PatternWidth) (value : PatternConversion)
deriving Repr, Inhabited

/-- A pattern whose syntax and named keys have already been checked. -/
structure CompiledPattern where
  private mk ::
  private parts : Array PatternPart
deriving Repr, Inhabited

private def quotePatternWidth (width : PatternWidth) : Lean.Term :=
  Lean.Syntax.mkCApp ``PatternWidth.mk
    #[Lean.quote width.leftAlign, Lean.quote width.minimum?, Lean.quote width.maximum?]

namespace Pattern

private def maximumWidth : Nat :=
  4096

private def error (offset : Nat) (message : String) : Except PatternError α :=
  .error { offset, message }

private def parseNat (digits : List Char) : Nat :=
  (String.ofList digits).toNat?.getD 0

private def parseWidth
    (remaining : List Char)
    (offset conversionOffset : Nat) :
    Except PatternError (PatternWidth × List Char × Nat) := do
  let (leftAlign, remaining, offset) :=
    match remaining with
    | '-' :: rest => (true, rest, offset + 1)
    | _ => (false, remaining, offset)
  let (minimumDigits, remaining) := remaining.span Char.isDigit
  let minimum? := if minimumDigits.isEmpty then none else some (parseNat minimumDigits)
  let offset := offset + minimumDigits.length
  let (maximum?, remaining, offset) ←
    match remaining with
    | '.' :: rest =>
        let (maximumDigits, rest) := rest.span Char.isDigit
        if maximumDigits.isEmpty then
          error conversionOffset "a maximum width requires decimal digits"
        else
          pure (some (parseNat maximumDigits), rest, offset + maximumDigits.length + 1)
    | _ => pure (none, remaining, offset)
  if leftAlign && minimum?.isNone then
    error conversionOffset "left alignment requires a minimum width"
  else if minimum?.getD 0 > maximumWidth then
    error conversionOffset s!"minimum width exceeds the limit of {maximumWidth}"
  else if maximum?.getD 0 > maximumWidth then
    error conversionOffset s!"maximum width exceeds the limit of {maximumWidth}"
  else
    pure ({ leftAlign, minimum?, maximum? }, remaining, offset)

private def parseBraced
    (label : String)
    (remaining : List Char)
    (offset conversionOffset : Nat) :
    Except PatternError (String × List Char × Nat) :=
  match remaining with
  | '{' :: rest => collect rest [] (offset + 1)
  | _ => error conversionOffset s!"%{label} requires a braced argument"
where
  collect (remaining : List Char) (reversed : List Char) (offset : Nat) :=
    match remaining with
    | [] => error conversionOffset s!"unterminated argument to %{label}"
    | '}' :: rest =>
        if reversed.isEmpty then
          error conversionOffset s!"%{label} requires a nonempty argument"
        else
          pure (String.ofList reversed.reverse, rest, offset + 1)
    | char :: rest => collect rest (char :: reversed) (offset + 1)

private def parseDateBraced
    (remaining : List Char)
    (offset conversionOffset : Nat) :
    Except PatternError (String × List Char × Nat) :=
  match remaining with
  | '{' :: rest => collect rest [] (offset + 1) none false
  | _ => error conversionOffset "%d requires a braced argument"
where
  collect
      (remaining : List Char)
      (reversed : List Char)
      (offset : Nat)
      (quote? : Option Char)
      (escaped : Bool) :=
    match remaining with
    | [] => error conversionOffset "unterminated argument to %d"
    | char :: rest =>
        if escaped then
          collect rest (char :: reversed) (offset + 1) quote? false
        else
          match quote? with
          | some quote =>
              let nextQuote? := if char == quote then none else quote?
              collect rest (char :: reversed) (offset + 1) nextQuote? false
          | none =>
              if char == '\\' then
                collect rest (char :: reversed) (offset + 1) none true
              else if char == '\'' || char == '"' then
                collect rest (char :: reversed) (offset + 1) (some char) false
              else if char == '}' then
                if reversed.isEmpty then
                  error conversionOffset "%d requires a nonempty argument"
                else
                  pure (String.ofList reversed.reverse, rest, offset + 1)
              else
                collect rest (char :: reversed) (offset + 1) none false

private def validateNamedKey
    (label key : String)
    (offset : Nat) : Except PatternError Unit :=
  unless isValidStructuredKey key do
    error offset s!"%{label} contains an invalid structured key '{key}'"

private def checkContextSchema
    (schemas : PatternSchemas)
    (key : String)
    (offset : Nat) : Except PatternError Unit :=
  match schemas.context? with
  | none => pure ()
  | some allowed =>
      if allowed.contains key then pure ()
      else error offset s!"context key '{key}' is not present in the context schema"

private def checkFieldSchema
    (schemas : PatternSchemas)
    (key : String)
    (offset : Nat) : Except PatternError Unit :=
  match schemas.field? with
  | none => pure ()
  | some allowed =>
      if allowed.contains key then pure ()
      else error offset s!"event-field key '{key}' is not present in the field schema"

private def parseConversion
    (schemas : PatternSchemas)
    (remaining : List Char)
    (offset conversionOffset : Nat) :
    Except PatternError (PatternPart × List Char × Nat) := do
  match remaining with
  | [] => error conversionOffset "dangling '%'"
  | '%' :: rest => pure (.literal "%", rest, offset + 1)
  | 'n' :: rest => pure (.newline, rest, offset + 1)
  | _ =>
      let (width, remaining, offset) ← parseWidth remaining offset conversionOffset
      let (wordChars, remaining) := remaining.span Char.isAlpha
      if wordChars.isEmpty then
        error conversionOffset "expected a conversion word after '%'"
      let word := String.ofList wordChars
      let offset := offset + wordChars.length
      let make value := pure (.conversion width value, remaining, offset)
      match word with
      | "level" => make .level
      | "logger" => make .logger
      | "msg" => make .message
      | "cause" => make .cause
      | "mdc" => make .context
      | "fields" => make .fieldSet
      | "d" =>
          match remaining with
          | '{' :: _ =>
              let (format, rest, nextOffset) ←
                parseDateBraced remaining offset conversionOffset
              let parsed : Except String (Std.Time.GenericFormat .any) :=
                Std.Time.GenericFormat.spec format
              match parsed with
              | .error message => error conversionOffset s!"invalid date format: {message}"
              | .ok parsed =>
                  pure (.conversion width (.date { source := format, format := parsed }),
                    rest, nextOffset)
          | _ =>
              let source := "uuuu-MM-dd'T'HH:mm:ss.SSSSSSSSS"
              match Std.Time.GenericFormat.spec source with
              | .error message => error conversionOffset s!"invalid date format: {message}"
              | .ok parsed => make (.date { source, format := parsed })
      | "X" =>
          let (key, rest, nextOffset) ←
            parseBraced "X" remaining offset conversionOffset
          validateNamedKey "X" key conversionOffset
          checkContextSchema schemas key conversionOffset
          pure (.conversion width (.contextValue key), rest, nextOffset)
      | "field" =>
          let (key, rest, nextOffset) ←
            parseBraced "field" remaining offset conversionOffset
          validateNamedKey "field" key conversionOffset
          checkFieldSchema schemas key conversionOffset
          pure (.conversion width (.fieldValue key), rest, nextOffset)
      | _ => error conversionOffset s!"unknown conversion '%{word}'"

private def flushLiteral
    (reversedLiteral : List Char)
    (reversedParts : List PatternPart) : List PatternPart :=
  if reversedLiteral.isEmpty then
    reversedParts
  else
    .literal (String.ofList reversedLiteral.reverse) :: reversedParts

private partial def parseParts
    (schemas : PatternSchemas)
    (remaining : List Char)
    (offset : Nat)
    (reversedLiteral : List Char)
    (reversedParts : List PatternPart) : Except PatternError (List PatternPart) := do
  match remaining with
  | [] => pure (flushLiteral reversedLiteral reversedParts).reverse
  | '%' :: rest =>
      let reversedParts := flushLiteral reversedLiteral reversedParts
      let (part, rest, nextOffset) ← parseConversion schemas rest (offset + 1) offset
      parseParts schemas rest nextOffset [] (part :: reversedParts)
  | char :: rest =>
      parseParts schemas rest (offset + 1) (char :: reversedLiteral) reversedParts

/-- Parse and validate a pattern. No parsing occurs while rendering its result. -/
def compile
    (source : String)
    (schemas : PatternSchemas := {}) : Except PatternError CompiledPattern := do
  let parts ← parseParts schemas source.toList 0 [] []
  pure { parts := parts.toArray }

end Pattern

/-- Render the first binding with `key`, or `-` when it is absent. -/
def renderNamedBinding
    (key : String)
    (bindings : List (String × LogValue)) : String :=
  (bindings.find? fun binding => binding.1 == key)
    |>.map (renderLogValueText ·.2)
    |>.getD "-"

/-- Render an optional cause, using the pattern-language missing marker. -/
def renderOptionalCause (cause : Option Cause) : String :=
  cause.map renderCauseText |>.getD "-"

private def renderConversion (conversion : PatternConversion) (event : LogEvent) : String :=
  match conversion with
  | .date pattern => timestampWithFormat event.timestamp pattern.format
  | .level => event.level.toUpperString
  | .logger => event.logger
  | .message => event.message
  | .cause => renderOptionalCause event.cause
  | .contextValue key => renderNamedBinding key event.context
  | .context => renderBindings event.context
  | .fieldValue key => renderNamedBinding key event.fields
  | .fieldSet => renderBindings event.fields

/-- Render an event from an already compiled pattern. -/
def CompiledPattern.render (pattern : CompiledPattern) : Layout := fun event =>
  pattern.parts.foldl (init := "") fun output part =>
    match part with
    | .literal value => output ++ value
    | .newline => output ++ "\n"
    | .conversion width conversion => output ++ width.apply (renderConversion conversion event)

/-- Context keys named by a compiled pattern, in source order. -/
def CompiledPattern.contextKeys (pattern : CompiledPattern) : List String :=
  pattern.parts.toList.filterMap fun
    | .conversion _ (.contextValue key) => some key
    | _ => none

/-- Event-field keys named by a compiled pattern, in source order. -/
def CompiledPattern.fieldKeys (pattern : CompiledPattern) : List String :=
  pattern.parts.toList.filterMap fun
    | .conversion _ (.fieldValue key) => some key
    | _ => none

private meta def quoteDateFormat (pattern : DatePattern) : Lean.Elab.Term.TermElabM Lean.Term := do
  let source : Lean.TSyntax `str := ⟨Lean.Syntax.mkStrLit pattern.source⟩
  `(datespec($source))

private meta def quoteSpecializedConversion
    (conversion : PatternConversion)
    (event : Lean.Term) : Lean.Elab.Term.TermElabM Lean.Term := do
  let timestamp := Lean.Syntax.mkCApp ``LogEvent.timestamp #[event]
  let level := Lean.Syntax.mkCApp ``LogEvent.level #[event]
  let logger := Lean.Syntax.mkCApp ``LogEvent.logger #[event]
  let message := Lean.Syntax.mkCApp ``LogEvent.message #[event]
  let cause := Lean.Syntax.mkCApp ``LogEvent.cause #[event]
  let context := Lean.Syntax.mkCApp ``LogEvent.context #[event]
  let fields := Lean.Syntax.mkCApp ``LogEvent.fields #[event]
  match conversion with
  | .date pattern =>
      pure <| Lean.Syntax.mkCApp ``timestampWithFormat #[timestamp, ← quoteDateFormat pattern]
  | .level => pure <| Lean.Syntax.mkCApp ``Level.toUpperString #[level]
  | .logger => pure logger
  | .message => pure message
  | .cause => pure <| Lean.Syntax.mkCApp ``renderOptionalCause #[cause]
  | .contextValue key =>
      pure <| Lean.Syntax.mkCApp ``renderNamedBinding #[Lean.quote key, context]
  | .context => pure <| Lean.Syntax.mkCApp ``renderBindings #[context]
  | .fieldValue key =>
      pure <| Lean.Syntax.mkCApp ``renderNamedBinding #[Lean.quote key, fields]
  | .fieldSet => pure <| Lean.Syntax.mkCApp ``renderBindings #[fields]

private meta def quoteSpecializedPart
    (part : PatternPart)
    (event : Lean.Term) : Lean.Elab.Term.TermElabM Lean.Term := do
  match part with
  | .literal value => pure (Lean.quote value)
  | .newline => pure (Lean.quote "\n")
  | .conversion width conversion =>
      let value ← quoteSpecializedConversion conversion event
      if width == {} then
        pure value
      else
        pure <| Lean.Syntax.mkCApp ``PatternWidth.apply #[quotePatternWidth width, value]

private meta def quoteSpecializedLayout
    (pattern : CompiledPattern) : Lean.Elab.Term.TermElabM Lean.Term := do
  let eventName ← Lean.mkFreshUserName `event
  let event := Lean.mkIdent eventName
  let pieces ← pattern.parts.mapM (quoteSpecializedPart · event)
  let body := pieces.toList.foldr
    (fun piece output => Lean.Syntax.mkCApp ``String.append #[piece, output])
    (Lean.quote "")
  let eventIdentifier : Lean.TSyntax `ident := ⟨event⟩
  `(fun ($eventIdentifier : Loggers.LogEvent) => $body)

end Format
end Loggers

open Lean Elab Term

namespace Loggers.Format

syntax (name := patternBareStx) "pattern%" str : term
syntax (name := patternOneSchemaStx) "pattern%"
  "(" ident ":=" term ")" str : term
syntax (name := patternSchemasStx) "pattern%"
  "(" ident ":=" term ")"
  "(" ident ":=" term ")" str : term

private def schemaLabel (label : TSyntax `ident) : TermElabM Bool :=
  match label.getId.toString with
  | "contextSchema" => pure true
  | "fieldSchema" => pure false
  | _ => throwErrorAt label "expected 'contextSchema' or 'fieldSchema'"

private def addSchemaChecks
    (schema : TSyntax `term)
    (keys : List String)
    (body : Lean.Term) : TermElabM Lean.Term := do
  if keys.isEmpty then
    return ← `(let _ : Nonempty (List String) := ⟨$schema⟩; $body)
  let mut checked := body
  for key in keys.reverse do
    checked ← `(let _ : ($(quote key) ∈ ($schema : List String)) := (by decide); $checked)
  pure checked

private def expandPattern
    (stx : Syntax)
    (patternSyntax : Syntax)
    (contextSchema? : Option (TSyntax `term))
    (fieldSchema? : Option (TSyntax `term))
    (expectedType? : Option Expr) : TermElabM Expr := do
  let some source := patternSyntax.isStrLit?
    | throwErrorAt patternSyntax "pattern% requires a string literal"
  let compiled ←
    match Pattern.compile source with
    | .ok compiled => pure compiled
    | .error error => throwErrorAt patternSyntax s!"invalid logging pattern: {error}"
  let mut expanded ← quoteSpecializedLayout compiled
  if let some schema := contextSchema? then
    expanded ← addSchemaChecks schema compiled.contextKeys expanded
  if let some schema := fieldSchema? then
    expanded ← addSchemaChecks schema compiled.fieldKeys expanded
  withMacroExpansion stx expanded <| elabTerm expanded expectedType?

@[term_elab patternBareStx] def elabBarePattern : TermElab := fun stx expectedType? =>
  match stx with
  | `(pattern% $pattern:str) => expandPattern stx pattern.raw none none expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab patternOneSchemaStx] def elabOneSchemaPattern : TermElab := fun stx expectedType? => do
  match stx with
  | `(pattern% ($label:ident := $schema:term) $pattern:str) =>
      if ← schemaLabel label then
        expandPattern stx pattern.raw (some schema) none expectedType?
      else
        expandPattern stx pattern.raw none (some schema) expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab patternSchemasStx] def elabSchemasPattern : TermElab := fun stx expectedType? => do
  match stx with
  | `(pattern% ($first:ident := $ctx:term) ($second:ident := $fld:term) $pattern:str) =>
      unless ← schemaLabel first do
        throwErrorAt first "the first schema must be 'contextSchema'"
      if ← schemaLabel second then
        throwErrorAt second "the second schema must be 'fieldSchema'"
      expandPattern stx pattern.raw (some ctx) (some fld) expectedType?
  | _ => throwUnsupportedSyntax

end Loggers.Format
