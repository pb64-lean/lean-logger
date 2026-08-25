import Lean.Data.Json.Parser
import Loggers.Format

open Loggers Loggers.Format

namespace Test.Format

/--
error:
-/
#guard_msgs (error, substring := true) in
#check fun (compiled : CompiledPattern) => { compiled with parts := #[] }

private def AppContext : List String := ["requestId", "quoted"]
private def AppFields : List String := ["outcome", "count"]

private def contextSchema : Nat :=
  11

private def fieldSchema : Nat :=
  13

private structure UniversalSchema

private instance : Membership String UniversalSchema where
  mem _ _ := True

private def universalSchema : UniversalSchema := {}

private def schemaLayout : Layout :=
  pattern% (contextSchema := AppContext) (fieldSchema := AppFields)
    "%X{requestId} %field{outcome}"

private def literalLayout :=
  pattern% "literal %%"

/--
error: invalid logging pattern: pattern offset 0: unknown conversion '%unknown'
-/
#guard_msgs (error, substring := true) in
def invalidConversionPattern : Layout := pattern% "%unknown"

/--
error: Tactic `decide` proved
-/
#guard_msgs (error, substring := true) in
def invalidSchemaPattern : Layout :=
  pattern% (contextSchema := AppContext) "%X{absent}"

/--
error: Type mismatch
-/
#guard_msgs (error, substring := true) in
def invalidSchemaType : Layout :=
  pattern% (contextSchema := universalSchema) "%X{anything}"

/--
error: Application type mismatch
-/
#guard_msgs (error, substring := true) in
def invalidUnusedSchemaType : Layout :=
  pattern% (contextSchema := universalSchema) "%mdc"

/--
error: expected 'contextSchema' or 'fieldSchema'
-/
#guard_msgs (error, substring := true) in
def invalidSchemaLabel : Layout :=
  pattern% (schema := AppContext) "%mdc"

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def expect (condition : Bool) (message : String) : IO Unit :=
  unless condition do fail message

private def expectEq [BEq α] [Repr α] (actual expected : α) (label : String) : IO Unit :=
  unless actual == expected do
    fail s!"{label}: expected {repr expected}, got {repr actual}"

private def expectValidJson (value label : String) : IO Unit :=
  match Lean.Json.parse value with
  | .ok _ => pure ()
  | .error error => fail s!"{label}: invalid JSON: {error}"

private def expectPatternError
    (result : Except PatternError CompiledPattern)
    (offset : Nat)
    (message : String)
    (label : String) : IO Unit :=
  match result with
  | .error error => do
      expectEq error.offset offset s!"{label} offset"
      expectEq error.message message s!"{label} message"
  | .ok _ => fail s!"{label}: pattern unexpectedly compiled"

private def event : LogEvent :=
  LogEvent.mk
    0
    .info
    "App.Service"
    { declaration := `App.Service.run
      module := `App.Service
      file? := some "App/Service.lean"
      line? := some 12
      column? := some 3 }
    "hello \"world\"\n"
    (some
      { summary := "boom"
        detail := some (.obj #[("code", .nat 7)])
        inner := some { summary := "root" } })
    [("requestId", .str "r-1"), ("quoted", .str "a\"b")]
    [("outcome", .str "ok"), ("count", .nat 2)]

private def expectedJson : String :=
  "{\"timestamp\":\"1970-01-01T00:00:00.000000000Z\"," ++
  "\"level\":\"INFO\",\"logger\":\"App.Service\"," ++
  "\"provenance\":{\"declaration\":\"App.Service.run\"," ++
  "\"module\":\"App.Service\",\"line\":12,\"column\":3}," ++
  "\"message\":\"hello \\\"world\\\"\\n\"," ++
  "\"cause\":{\"summary\":\"boom\",\"detail\":{\"code\":7}," ++
  "\"inner\":{\"summary\":\"root\",\"detail\":null,\"inner\":null}}," ++
  "\"context\":{\"requestId\":\"r-1\",\"quoted\":\"a\\\"b\"}," ++
  "\"fields\":{\"outcome\":\"ok\",\"count\":2}}"

private def testText : IO Unit := do
  expectEq (compactText event)
    ("1970-01-01T00:00:00.000000000Z INFO  App.Service " ++
      "[requestId=r-1 quoted=\"a\\\"b\"] hello \"world\"\n " ++
      "{outcome=ok count=2} -- boom {\"code\":7} <- root")
    "compact text"
  expectEq (compactTextLine event) (compactText event ++ "\n") "compact text line"
  expectEq (renderLogValueText (.str "two words")) "\"two words\"" "quoted text value"
  expectEq (renderLogValueText (.arr #[.nat 1, .bool true])) "[1,true]" "text array"

private def testJson : IO Unit := do
  expectEq (json event) expectedJson "stable JSON"
  expectValidJson (json event) "stable JSON parse"
  expectEq (jsonLine event) (expectedJson ++ "\n") "JSON Lines framing"
  expect ((jsonBytes event) == ((expectedJson ++ "\n").toUTF8)) "JSON byte encoding"
  expectEq (renderJson { includeSourceFile := true } event)
    (expectedJson.replace
      "\"module\":\"App.Service\",\"line\""
      "\"module\":\"App.Service\",\"file\":\"App/Service.lean\",\"line\"")
    "optional source path"
  let controls := String.ofList ['\u0000', '\t', '\r', '\n', '\"', '\\']
  expectEq (renderLogValueJson (.str controls))
    "\"\\u0000\\u0009\\r\\n\\\"\\\\\""
    "strict JSON string escaping"
  let notANumber := Float.ofBits 0x7ff8000000000000
  expectEq (renderLogValueJson (.float notANumber)) "null" "non-finite JSON number"
  let positiveInfinity := Float.ofBits 0x7ff0000000000000
  let negativeInfinity := Float.ofBits 0xfff0000000000000
  expectEq (renderLogValueJson (.float positiveInfinity)) "null" "positive infinity"
  expectEq (renderLogValueJson (.float negativeInfinity)) "null" "negative infinity"
  let finite := renderLogValueJson (.float (-12.5))
  expect (finite != "null") "finite JSON number"
  expectValidJson finite "finite JSON number parse"
  let escapedObject :=
    renderLogValueJson (.obj #[("key\"\n\\", .str "value\t")])
  expectEq escapedObject "{\"key\\\"\\n\\\\\":\"value\\u0009\"}" "escaped JSON key"
  expectValidJson escapedObject "escaped JSON object parse"
  let absentSite : Provenance := { declaration := `Absent.site, module := `Absent }
  let absentJson := json { event with provenance := absentSite }
  expect (absentJson.contains "\"line\":null,\"column\":null")
    "null provenance positions"
  expect (!absentJson.contains "\"file\":") "default file omission"

private def testCompiledPatterns : IO Unit := do
  let layout : Layout :=
    pattern% "%%|%n|%d{HH:mm:ss.SSS}|%-5level|%15logger|%.3logger|%msg|%cause|%X{missing}|%mdc|%field{missing}|%fields"
  expectEq (layout event)
    ("%|\n|00:00:00.000|INFO |    App.Service|ice|hello \"world\"\n|" ++
      "boom {\"code\":7} <- root|-|requestId=r-1 quoted=\"a\\\"b\"|-|" ++
      "outcome=ok count=2")
    "compile-time pattern"
  expectEq (schemaLayout event) "r-1 ok" "schema-checked pattern"
  expectEq (literalLayout event) "literal %" "inferred literal pattern"
  let utcLayout : Layout := pattern% "%d{uuuu-MM-dd'T'HH:mm:ssX}"
  expectEq (utcLayout event) "1970-01-01T00:00:00Z" "UTC date pattern"
  let quotedBrace : Layout := pattern% "%d{HH'}'mm}"
  expectEq (quotedBrace event) "00}00" "quoted date brace"
  let escapedBrace : Layout := pattern% "%d{HH\\}mm}"
  expectEq (escapedBrace event) "00}00" "escaped date brace"
  let compiled ←
    match Pattern.compile "%d{uuuu-MM-dd} %level %logger %msg%n" with
    | .ok compiled => pure compiled
    | .error error => fail s!"valid dynamic pattern failed: {error}"
  expectEq (compiled.render event)
    "1970-01-01 INFO App.Service hello \"world\"\n\n"
    "dynamically compiled pattern"
  expectEq compiled.contextKeys [] "dynamic context keys"
  expectEq compiled.fieldKeys [] "dynamic field keys"

private def testPatternDiagnostics : IO Unit := do
  expectPatternError (Pattern.compile "abc %wat") 4
    "unknown conversion '%wat'" "unknown conversion"
  expectPatternError (Pattern.compile "%X{}") 0
    "%X requires a nonempty argument" "empty context key"
  expectPatternError (Pattern.compile "%field{outcome") 0
    "unterminated argument to %field" "unterminated field key"
  expectPatternError (Pattern.compile "%-.3level") 0
    "left alignment requires a minimum width" "invalid alignment"
  expectPatternError (Pattern.compile "%4097msg") 0
    "minimum width exceeds the limit of 4096" "bounded minimum width"
  expectPatternError (Pattern.compile "%.4097msg") 0
    "maximum width exceeds the limit of 4096" "bounded maximum width"
  expectPatternError (Pattern.compile "%X{bad key}") 0
    "%X contains an invalid structured key 'bad key'" "invalid context key"
  expectPatternError (Pattern.compile "%field{bad=key}") 0
    "%field contains an invalid structured key 'bad=key'" "invalid field key"
  expectPatternError (Pattern.compile "%d{HH\\}") 0
    "unterminated argument to %d" "escaped date delimiter"
  expectPatternError (Pattern.compile "%d{HH'}mm}") 0
    "unterminated argument to %d" "unterminated date quote"
  match Pattern.compile "%d{P}" with
  | .error error =>
      expectEq error.offset 0 "invalid date offset"
      expect (error.message.startsWith "invalid date format:") "invalid date diagnostic"
  | .ok _ => fail "invalid date pattern unexpectedly compiled"
  expectPatternError
    (Pattern.compile "%X{outcome}"
      { context? := some AppContext, field? := some AppFields })
    0
    "context key 'outcome' is not present in the context schema"
    "wrong pattern namespace"
  expectPatternError
    (Pattern.compile "%field{requestId}"
      { context? := some AppContext, field? := some AppFields })
    0
    "event-field key 'requestId' is not present in the field schema"
    "wrong field namespace"

def runAll : IO Unit := do
  expectEq contextSchema 11 "ordinary contextSchema identifier"
  expectEq fieldSchema 13 "ordinary fieldSchema identifier"
  testText
  testJson
  testCompiledPatterns
  testPatternDiagnostics

end Test.Format

def main : IO Unit :=
  Test.Format.runAll
