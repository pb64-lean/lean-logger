import Lean.Data.Json.Printer
import Loggers.Core

namespace Loggers
namespace Format

open Std.Time

/-- A formatter that turns one strict event into text. -/
abbrev Layout := LogEvent → String

/-- A formatter that turns one strict event into bytes. -/
abbrev Encoder := LogEvent → ByteArray

/-- Encode the exact UTF-8 output of a text layout. -/
def Layout.toEncoder (layout : Layout) : Encoder :=
  fun event => (layout event).toUTF8

/-- Append one platform-independent line feed to a layout. -/
def Layout.withNewline (layout : Layout) : Layout :=
  fun event => layout event ++ "\n"

private def formatPlainDateTime
    (date : PlainDateTime)
    (format : GenericFormat .any) : String :=
  let rendered := format.formatGeneric fun
    | .G _ => some date.era
    | .y _ => some date.year
    | .u _ => some date.year
    | .Y _ => some date.weekYear
    | .D _ => some (Sigma.mk date.year.isLeap date.dayOfYear)
    | .Qorq _ => some date.quarter
    | .w _ => some date.weekOfYear
    | .W _ => some date.alignedWeekOfMonth
    | .MorL _ => some date.month
    | .d _ => some date.day
    | .E _ => some date.weekday
    | .eorc _ => some date.weekday
    | .F _ => some date.weekOfMonth
    | .H _ => some date.hour
    | .k _ => some date.hour.shiftTo1BasedHour
    | .m _ => some date.minute
    | .n _ => some date.nanosecond
    | .s _ => some date.time.second
    | .a _ => some (HourMarker.ofOrdinal date.hour)
    | .h _ => some date.hour.toRelative
    | .K _ => some (date.hour.emod 12 (by decide))
    | .S _ => some date.nanosecond
    | .A _ => some date.time.toMilliseconds
    | .N _ => some date.time.toNanoseconds
    | .V => some "UTC"
    | .z _ => some "UTC"
    | .O _ => some Std.Time.TimeZone.Offset.zero
    | .X _ => some Std.Time.TimeZone.Offset.zero
    | .x _ => some Std.Time.TimeZone.Offset.zero
    | .Z _ => some Std.Time.TimeZone.Offset.zero
  rendered.getD "invalid time"

/-- Render a timestamp with an already parsed date-time specification. -/
def timestampWithFormat
    (timestamp : Timestamp)
    (format : GenericFormat .any) : String :=
  formatPlainDateTime (PlainDateTime.ofWallTime (timestamp.toWallTime TimeZone.Offset.zero)) format

private def utcTimestampFormat : GenericFormat .any :=
  datespec("uuuu-MM-dd'T'HH:mm:ss.SSSSSSSSS")

/-- UTC timestamp spelling used by the built-in deterministic layouts. -/
def timestampUtc (timestamp : Timestamp) : String :=
  timestampWithFormat timestamp utcTimestampFormat ++ "Z"

private def spaces (count : Nat) : String :=
  String.ofList (List.replicate count ' ')

/-- Right-pad a string to at least `width` Unicode scalar values. -/
def padRight (value : String) (width : Nat) : String :=
  value ++ spaces (width - value.length)

/-- Left-pad a string to at least `width` Unicode scalar values. -/
def padLeft (value : String) (width : Nat) : String :=
  spaces (width - value.length) ++ value

private def isBareTextChar (char : Char) : Bool :=
  !char.isWhitespace && char != '=' && char != ',' && char != '[' && char != ']' &&
    char != '{' && char != '}' && char != '"' && char != '\\'

private def renderTextString (value : String) : String :=
  if !value.isEmpty && value.toList.all isBareTextChar then
    value
  else
    Lean.Json.renderString value

/-- Compact, deterministic human-readable rendering of structured data. -/
partial def renderLogValueText : LogValue → String
  | .null => "null"
  | .str value => renderTextString value
  | .int value => toString value
  | .nat value => toString value
  | .float value => toString value
  | .bool true => "true"
  | .bool false => "false"
  | .arr values =>
      "[" ++ String.intercalate "," (values.toList.map renderLogValueText) ++ "]"
  | .obj entries =>
      let renderField field := Lean.Json.renderString field.1 ++ ":" ++ renderLogValueText field.2
      "{" ++ String.intercalate "," (entries.toList.map renderField) ++ "}"

/-- Render ordered context or event fields as `key=value` pairs. -/
def renderBindings (bindings : List (String × LogValue)) : String :=
  String.intercalate " " <| bindings.map fun (key, value) =>
    key ++ "=" ++ renderLogValueText value

/-- Render a cause chain without discarding structured details. -/
partial def renderCauseText (cause : Cause) : String :=
  let detail := cause.detail.map (fun value => " " ++ renderLogValueText value) |>.getD ""
  let inner := cause.inner.map (fun value => " <- " ++ renderCauseText value) |>.getD ""
  cause.summary ++ detail ++ inner

/-- A stable compact layout suitable for console output and golden tests. -/
def compactText : Layout := fun event =>
  let base := timestampUtc event.timestamp ++ " " ++
    padRight event.level.toUpperString 5 ++ " " ++ event.logger ++ " [" ++
    renderBindings event.context ++ "] " ++ event.message
  let withFields :=
    if event.fields.isEmpty then base
    else base ++ " {" ++ renderBindings event.fields ++ "}"
  match event.cause with
  | none => withFields
  | some cause => withFields ++ " -- " ++ renderCauseText cause

/-- The compact layout terminated by exactly one line feed. -/
def compactTextLine : Layout :=
  compactText.withNewline

end Format
end Loggers
