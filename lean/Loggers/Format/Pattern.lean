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

/-- A validated date-time format retained in its parsed representation. -/
structure DatePattern where
  source : String
  format : Std.Time.GenericFormat .any
deriving Repr, Inhabited

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
  parts : Array PatternPart
deriving Repr, Inhabited

private def quotePatternWidth (width : PatternWidth) : Lean.Term :=
  Lean.Syntax.mkCApp ``PatternWidth.mk
    #[Lean.quote width.leftAlign, Lean.quote width.minimum?, Lean.quote width.maximum?]

private meta def quotePatternConversion : PatternConversion → Lean.Elab.Term.TermElabM Lean.Term
  | .date pattern => do
      let source : Lean.TSyntax `str := ⟨Lean.Syntax.mkStrLit pattern.source⟩
      `(Loggers.Format.PatternConversion.date
          { source := $(Lean.quote pattern.source), format := datespec($source) })
  | .level => pure <| Lean.Syntax.mkCApp ``PatternConversion.level #[]
  | .logger => pure <| Lean.Syntax.mkCApp ``PatternConversion.logger #[]
  | .message => pure <| Lean.Syntax.mkCApp ``PatternConversion.message #[]
  | .cause => pure <| Lean.Syntax.mkCApp ``PatternConversion.cause #[]
  | .contextValue key =>
      pure <| Lean.Syntax.mkCApp ``PatternConversion.contextValue #[Lean.quote key]
  | .context => pure <| Lean.Syntax.mkCApp ``PatternConversion.context #[]
  | .fieldValue key =>
      pure <| Lean.Syntax.mkCApp ``PatternConversion.fieldValue #[Lean.quote key]
  | .fieldSet => pure <| Lean.Syntax.mkCApp ``PatternConversion.fieldSet #[]

private meta def quotePatternPart : PatternPart → Lean.Elab.Term.TermElabM Lean.Term
  | .literal value => pure <| Lean.Syntax.mkCApp ``PatternPart.literal #[Lean.quote value]
  | .newline => pure <| Lean.Syntax.mkCApp ``PatternPart.newline #[]
  | .conversion width conversion => do
      let quoted ← quotePatternConversion conversion
      pure <| Lean.Syntax.mkCApp ``PatternPart.conversion #[quotePatternWidth width, quoted]

private meta def quoteCompiledPattern
    (pattern : CompiledPattern) : Lean.Elab.Term.TermElabM Lean.Term := do
  let parts ← pattern.parts.mapM quotePatternPart
  pure <| Lean.Syntax.mkCApp ``CompiledPattern.mk #[Lean.quote parts]

namespace Pattern

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
                parseBraced "d" remaining offset conversionOffset
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
          checkContextSchema schemas key conversionOffset
          pure (.conversion width (.contextValue key), rest, nextOffset)
      | "field" =>
          let (key, rest, nextOffset) ←
            parseBraced "field" remaining offset conversionOffset
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

private def findBinding?
    (key : String)
    (bindings : List (String × LogValue)) : Option LogValue :=
  (bindings.find? fun binding => binding.1 == key).map (·.2)

private def renderConversion (conversion : PatternConversion) (event : LogEvent) : String :=
  match conversion with
  | .date pattern => timestampWithFormat event.timestamp pattern.format
  | .level => event.level.toUpperString
  | .logger => event.logger
  | .message => event.message
  | .cause => event.cause.map renderCauseText |>.getD "-"
  | .contextValue key => findBinding? key event.context |>.map renderLogValueText |>.getD "-"
  | .context => renderBindings event.context
  | .fieldValue key => findBinding? key event.fields |>.map renderLogValueText |>.getD "-"
  | .fieldSet => renderBindings event.fields

private def applyWidth (width : PatternWidth) (value : String) : String :=
  let value :=
    match width.maximum? with
    | some maximum => if value.length > maximum then (value.takeEnd maximum).toString else value
    | none => value
  match width.minimum? with
  | none => value
  | some minimum =>
      if width.leftAlign then padRight value minimum else padLeft value minimum

/-- Render an event from an already compiled pattern. -/
def CompiledPattern.render (pattern : CompiledPattern) : Layout := fun event =>
  pattern.parts.foldl (init := "") fun output part =>
    match part with
    | .literal value => output ++ value
    | .newline => output ++ "\n"
    | .conversion width conversion => output ++ applyWidth width (renderConversion conversion event)

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

end Format
end Loggers

open Lean Elab Term

namespace Loggers.Format

syntax (name := patternBareStx) "pattern%" str : term
syntax (name := patternContextStx) "pattern%"
  "(" "contextSchema" ":=" term ")" str : term
syntax (name := patternFieldStx) "pattern%"
  "(" "fieldSchema" ":=" term ")" str : term
syntax (name := patternSchemasStx) "pattern%"
  "(" "contextSchema" ":=" term ")"
  "(" "fieldSchema" ":=" term ")" str : term

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
  let quotedCompiled ← quoteCompiledPattern compiled
  let mut expanded ← `(Loggers.Format.CompiledPattern.render $quotedCompiled)
  if let some schema := contextSchema? then
    for key in compiled.contextKeys.reverse do
      expanded ← `(let _ : ($(quote key) ∈ $schema) := (by decide); $expanded)
  if let some schema := fieldSchema? then
    for key in compiled.fieldKeys.reverse do
      expanded ← `(let _ : ($(quote key) ∈ $schema) := (by decide); $expanded)
  withMacroExpansion stx expanded <| elabTerm expanded expectedType?

@[term_elab patternBareStx] def elabBarePattern : TermElab := fun stx expectedType? =>
  match stx with
  | `(pattern% $pattern:str) => expandPattern stx pattern.raw none none expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab patternContextStx] def elabContextPattern : TermElab := fun stx expectedType? =>
  match stx with
  | `(pattern% (contextSchema := $schema:term) $pattern:str) =>
      expandPattern stx pattern.raw (some schema) none expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab patternFieldStx] def elabFieldPattern : TermElab := fun stx expectedType? =>
  match stx with
  | `(pattern% (fieldSchema := $schema:term) $pattern:str) =>
      expandPattern stx pattern.raw none (some schema) expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab patternSchemasStx] def elabSchemasPattern : TermElab := fun stx expectedType? =>
  match stx with
  | `(pattern% (contextSchema := $ctx:term) (fieldSchema := $fld:term) $pattern:str) =>
      expandPattern stx pattern.raw (some ctx) (some fld) expectedType?
  | _ => throwUnsupportedSyntax

end Loggers.Format
