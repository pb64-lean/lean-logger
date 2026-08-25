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

## Build and test

Bazel 8.5 or Bazelisk and Nix are required for authoritative builds:

```sh
bazel build //...
bazel test //...
```

The checked-in module lockfile and toolchain declaration make standalone Bazel
builds reproducible. Dependency metadata changes must refresh the lockfile
explicitly with `bazel mod graph --lockfile_mode=update` before ordinary locked
builds resume.

Lake supplies the editor project model and a compatibility build using the
toolchain selected by `lean-toolchain`:

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
