import Lean.Data.Json.Printer
import Loggers.Format.Text

namespace Loggers
namespace Format

/-- Policy switches for stable JSON event encoding. -/
structure JsonOptions where
  /-- Physical source paths are omitted by default to avoid environment-specific output. -/
  includeSourceFile : Bool := false
deriving Repr, BEq, Inhabited

private def jsonString (value : String) : String :=
  Lean.Json.renderString value

private def jsonOption (render : α → String) : Option α → String
  | none => "null"
  | some value => render value

private def jsonFloat (value : Float) : String :=
  match Lean.JsonNumber.fromFloat? value with
  | .inl _ => "null"
  | .inr number => number.toString

/-- Strict JSON rendering for a structured value. Non-finite floats become `null`. -/
partial def renderLogValueJson : LogValue → String
  | .null => "null"
  | .str value => jsonString value
  | .int value => toString value
  | .nat value => toString value
  | .float value => jsonFloat value
  | .bool true => "true"
  | .bool false => "false"
  | .arr values =>
      "[" ++ String.intercalate "," (values.toList.map renderLogValueJson) ++ "]"
  | .obj entries =>
      let renderField field := jsonString field.1 ++ ":" ++ renderLogValueJson field.2
      "{" ++ String.intercalate "," (entries.toList.map renderField) ++ "}"

private def renderJsonBindings (bindings : List (String × LogValue)) : String :=
  let renderBinding binding := jsonString binding.1 ++ ":" ++ renderLogValueJson binding.2
  "{" ++ String.intercalate "," (bindings.map renderBinding) ++ "}"

private partial def renderJsonCause (cause : Cause) : String :=
  "{" ++
    "\"summary\":" ++ jsonString cause.summary ++ "," ++
    "\"detail\":" ++ jsonOption renderLogValueJson cause.detail ++ "," ++
    "\"inner\":" ++ jsonOption renderJsonCause cause.inner ++
  "}"

private def renderJsonProvenance (options : JsonOptions) (site : Provenance) : String :=
  let declaration := "\"declaration\":" ++ jsonString site.declaration.toString
  let moduleName := "\"module\":" ++ jsonString site.module.toString
  let file :=
    if options.includeSourceFile then
      ",\"file\":" ++ jsonOption jsonString site.file?
    else
      ""
  let line := ",\"line\":" ++ jsonOption toString site.line?
  let column := ",\"column\":" ++ jsonOption toString site.column?
  "{" ++ declaration ++ "," ++ moduleName ++ file ++ line ++ column ++ "}"

/-- Render an event as one compact JSON object with a fixed top-level field order. -/
def renderJson (options : JsonOptions := {}) : Layout := fun event =>
  "{" ++
    "\"timestamp\":" ++ jsonString (timestampUtc event.timestamp) ++ "," ++
    "\"level\":" ++ jsonString event.level.toUpperString ++ "," ++
    "\"logger\":" ++ jsonString event.logger ++ "," ++
    "\"provenance\":" ++ renderJsonProvenance options event.provenance ++ "," ++
    "\"message\":" ++ jsonString event.message ++ "," ++
    "\"cause\":" ++ jsonOption renderJsonCause event.cause ++ "," ++
    "\"context\":" ++ renderJsonBindings event.context ++ "," ++
    "\"fields\":" ++ renderJsonBindings event.fields ++
  "}"

/-- Compact JSON without a trailing line feed. -/
def json : Layout :=
  renderJson

/-- JSON Lines output terminated by exactly one line feed. -/
def jsonLine : Layout :=
  json.withNewline

/-- Alias emphasizing the JSON Lines framing. -/
def jsonl : Layout :=
  jsonLine

/-- UTF-8 JSON Lines encoder. -/
def jsonBytes : Encoder :=
  jsonLine.toEncoder

end Format
end Loggers
