# Optional OpenTelemetry integration

This Bazel module provides `Loggers.OpenTelemetry` as an optional adapter for
structured logging. It builds against sibling source checkouts. From any
directory run:

```sh
bash path/to/lean-logger/integrations/otel/test.sh
```

`event` converts strict events and takes explicit immutable tracing context.
`appender` plugs into the existing runtime and accepts an event-to-context
function plus an optional flush callback. It borrows the OTel logger and never
closes the provider/channel. Nested structured values and causes are retained;
out-of-int64 integers become exact decimal strings, nonfinite floats become
empty values, duplicate object keys use the last value, and source paths are
omitted. Failure-isolated delivery cannot change application results.

The runner prints the dependency checkout paths and commits, selects the local
logger and OTel modules, and verifies the lockfile. Applications should pin
immutable dependency revisions.
