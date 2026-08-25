# lean-logger

`lean-logger` is a private, pre-release application-logging library for Lean 4.
It provides typed, scoped diagnostic context and event-local structured fields,
then erases accepted events into a strict representation suitable for filtering,
formatting, synchronous sinks, and bounded asynchronous delivery.

The `0.1.0` module version is a development coordinate, not a compatibility
promise. Public APIs may change before the first stable release.

## Scope

The library is organized into four layers:

- `core` defines levels, structured values, causes, provenance, strict events,
  row-indexed context and fields, scoped operations, and lazy logging syntax;
- `format` provides compact text, JSON, schemas, and compiled pattern layouts;
- `runtime` provides level configuration, filters, appenders, lifecycle,
  bounded asynchronous delivery, and duplicate suppression; and
- `testkit` provides deterministic clocks, capturing sinks, and explicit
  concurrency gates for application tests.

Typed context and event fields are separate namespaces. Fresh static bindings
reject accidental duplicate names, deliberate rebinding is explicit, and typed
values take precedence over values admitted through dynamic boundaries. Every
accepted event contains canonical duplicate-free context and field collections.

## Quick start

```lean
import Loggers

open Loggers Loggers.Format Loggers.Runtime

def config : Loggers.LogConfig := {
  root := .info
  overrides := [("App.Storage", .debug)]
  appenders := #[
    (AppenderSpec.console "stderr" .stderr <|
      pattern% "%d{HH:mm:ss.SSS} %-5level %logger [%mdc] %msg %fields%n")
      |>.async { capacity := 1024, overflowPolicy := .block }
  ]
}

def application : Logger [] Unit :=
  pushNew "requestId" "r-42" do
    log! .info "request complete"
      (fields := fields! ["outcome" := "accepted", "durationMs" := (12 : Nat)])

def main : IO Unit :=
  Loggers.run config application
```

The `log!`, `logErr!`, `logFailure!`, and `tapError!` forms defer messages,
causes, context conversion, field construction, clock access, and sink work
until the effective level accepts the event. Their default logger name and
provenance come from the lexical call site; `withLogger` provides an explicit
scoped override.

## Typed context and fields

`Logger ρ α` carries a row-indexed context through a reader. `pushNew` adds a
fresh binding for one lexical scope and restores the previous context on every
return path. A repeated name is rejected during elaboration. `rebindMDC` is the
deliberate shadowing operation, and `mdc` performs total typed lookup:

```lean
def audit [HasKey ρ "requestId" String] : Logger ρ Unit := do
  let requestId : String ← mdc "requestId"
  log! .info "auditing {requestId}"
```

`fields!` constructs a separate fresh typed row consumed by one event. Fields
are not ambient, are not visible through `mdc`, and are never propagated to a
child task or snapshot. A `Secret α` masks its value as `"***"` through the
normal `ToLogValue` conversion path.

Runtime-computed context enters through `withDynMDC` or `mergeDynMDC`;
runtime-computed event facts enter through `EventFields.mergeDynamic`. Static
and dynamic names must be nonempty, at most 128 characters, and contain only
letters, digits, `_`, `-`, `.`, or `:`. Duplicate input and typed-name
collisions are errors, and typed values always retain precedence.
The `reject`, `preserve`, and `overwrite` policies apply only to collisions
between dynamic sets.

`capture`, `Snapshot.run`, `Snapshot.concurrently`, and `Logger.concurrently`
make task propagation explicit. A raw task or deferred callback has no ambient
inheritance guarantee.

## Formatting

`compactText`, `compactTextLine`, `json`, `jsonLine`, and `jsonBytes` are stable
built-in layouts and encoders. JSON uses a fixed top-level property order,
strict escaping, UTC timestamps, and distinct `context` and `fields` objects.
Non-finite floating-point values encode as `null`.

`pattern%` validates and compiles a literal during elaboration. Its supported
conversions are `%%`, `%n`, `%d{...}`, `%level`, `%logger`, `%msg`, `%cause`,
`%X{key}`, `%mdc`, `%field{key}`, and `%fields`, with minimum/maximum widths and
left alignment. Pattern widths are bounded at 4096 characters. Date
specifications are retained in parsed form, so event rendering performs no
pattern parsing. Optional schemas catch a misspelled key or use of the wrong
namespace without requiring every event to populate it:

```lean
def contextSchema := ["requestId", "tenant"]
def fieldSchema := ["outcome", "durationMs"]

def layout : Layout :=
  pattern% (contextSchema := contextSchema) (fieldSchema := fieldSchema)
    "%level %X{requestId} %msg %field{outcome}%n"
```

`Pattern.compile` provides the corresponding validated boundary for patterns
that genuinely arrive at runtime.

## Runtime and lifecycle

Logger thresholds use the longest matching dotted segment prefix. Filters are
effectful and run in declaration order, stopping on `accept` or `deny`; an
all-`neutral` chain accepts. Per-event append failures are observational: they
are sent to a best-effort diagnostic hook while other appenders continue.
Recursive or overlapping diagnostics are dropped while that hook is active,
and failures raised by the hook itself are contained. Startup and explicit
flush or close failures remain visible to their caller.

Appender filters govern ordinary events entering the configured decorator
tree. Owner-only terminal records and records synthesized inside a decorator
bypass that outer chain so lifecycle and health summaries cannot be filtered
by the component that generated them.

`AppenderSpec.custom`, `.encoded`, `.console`, and `.file` create synchronous
appenders. Acquired appenders serialize their own writes. Startup proceeds in
declaration order and unwinds an acquired prefix in reverse on failure. Each
started appender owns an idempotent close result; lifecycle-aware decorators
fence admission, drain their owned work, flush, and release resources. If both
the application and shutdown fail, the application error remains primary and
the shutdown error is reported diagnostically.

Runtime close first fences new sink calls, invokes each appender's prompt
`quiesce` hook, waits for every route admitted before the fence to traverse all
configured appenders, and only then closes appenders in reverse acquisition
order. A custom decorator that can block admission must propagate `quiesce`
without releasing its child. If it can also produce strict lifecycle-final
records, it must install an atomic terminal close with
`StartedAppender.withTerminalBatch`.

The standard file-handle API has no explicit close operation, so a file
appender stores its handle behind its serialized lifecycle boundary and clears
the final retained reference during close. The descriptor then becomes
eligible for runtime release.

Explicit flush is not a global producer barrier. Runtime close does drain sink
calls that entered before its fence, including calls still evaluating filters,
but it cannot account for application tasks that have not called the sink yet.
Quiesce and join application-owned logging producers first when all of their
intended events must be included. Filters should be pure, prompt, and
concurrency-safe. The bracketed `Loggers.run` entry point likewise assumes its
action joins any logging tasks it owns before returning.

`.async` installs a bounded worker with `block`, `dropNewest`, or `dropOldest`
overflow behavior. It retains and joins the exact worker, preserves FIFO order
among events retained in the queue, drains before close, wakes blocked
producers when admission closes, and exposes coherent admission/failure
statistics through the direct `AsyncAppender` handle. A later `dropOldest`
offer may evict an event whose offer was admitted. Flush barriers protect
earlier queued events from later eviction; if every queued event is protected,
the incoming event is reported as `droppedNewest`. Concurrent producers must
still be synchronized when a flush needs to define a global admission cut.
During owner quiescence, ordinary direct offers return `quiesced`, while the
started-appender path continues admitting records whose ownership already
transferred through an enclosing lifecycle fence. Final owner records are
retained outside the normal capacity budget and handed to the child through
its terminal close operation after normal queued work, so nested blocking
asynchronous appenders make shutdown progress without dropping or reordering
retained records. Normal and terminal admissions and completions have separate
counters. `AsyncAppender.requestFailure` supplies an explicit supervised
failure transition: it fences admission, fails queued flush barriers, clears
queued work, retires the child, and makes later flush and close calls replay
the same error.

## Duplicate suppression

`.suppressDuplicates` installs a bounded decorator keyed by logger, full
provenance, level, cause summary, and an optional allowlist of stable event
fields. Message text, context, and non-allowlisted event fields do not fragment
the key. Configuration sets the number of originals allowed in a timestamp
window and the capacity of a deterministic least-recently-used table.

The first denied event emits a suppression-start record. Resumption, eviction,
and close emit summaries with `suppressedCount`; these synthetic records bypass
the suppressor itself. Decisions and counters are atomic, but concurrent child
deliveries can interleave according to the child appender. Flush ordering
therefore requires caller synchronization. Close fences new decisions,
quiesces child admission, waits for all selected delivery attempts, and then
hands close summaries to the child's terminal close operation. This atomic
handoff lets a full lifecycle-aware child retain summaries outside its normal
admission capacity before draining and closing.

## Build and test

Bazel 8.5.0 or Bazelisk and Nix are required for authoritative builds:

```sh
bazel build //...
bazel test //...
```

The checked-in module lockfile and toolchain declaration make standalone Bazel
builds reproducible. Dependency metadata changes must refresh the lockfile
explicitly with `bazel mod graph --lockfile_mode=update` before ordinary locked
builds resume.

The supported development matrix is Lean 4.27.0 from `lean-toolchain` and the
Bazel-selected Lean 4.31.0-pre toolchain at commit
`24bef91f9a20a45f074729e869461d374687de1c`. Other Lean versions are not part of
the current compatibility claim. Lake supplies the editor project model and a
compatibility build using the toolchain selected by `lean-toolchain`:

```sh
lake build
```

Bazel remains the source of truth for target boundaries, tests, and release
correctness.

## Bazel consumption

The complete application-facing library is available at `//:lean_logger` in a
root checkout. Dependency-mode consumers use `@lean-logger//:lean_logger`.
Layer targets are available at:

- `//lean/Loggers:core`
- `//lean/Loggers:format`
- `//lean/Loggers:runtime`
- `//lean/Loggers:testkit`

The `testkit` target is test-only and is intentionally excluded from the
umbrella library.

A dependency-mode root can use the module coordinate `lean-logger` and target
`@lean-logger//:lean_logger`. Until a registry release exists, pin the module to
an immutable authenticated source revision in the consuming root.
