# Repository guidance

This repository is a private Lean 4 application-logging library built and
tested with Bazel. Keep source, diagnostics, examples, and configuration free
of credentials, machine-specific paths, and undocumented service assumptions.

## Layout and dependency direction

- `lean/Loggers.lean` is the public import facade.
- `lean/Loggers/Core.lean` collects the typed context, event-field, event, and
  logging syntax surface.
- `lean/Loggers/Format.lean` collects text, JSON, and compiled-pattern output.
- `lean/Loggers/Runtime.lean` collects configuration, filters, appenders,
  lifecycle management, asynchronous delivery, and duplicate suppression.
- `lean/Loggers/Testkit.lean` contains deterministic clocks, capturing sinks,
  and concurrency gates intended only for tests.
- Production dependency direction is `core` to `format` to `runtime`.
  `testkit` may depend on production targets, but production targets must not
  depend on `testkit` or test fixtures.

Keep `LogCtx` and `EventFields` representation details in the same module as
their smart constructors so module-private constructors and projections remain
enforced. Keep strict events as the boundary accepted by appenders and queues;
application thunks must be forced or discarded before crossing that boundary.

## Builds and dependency metadata

Bazel is authoritative. Lake exists for editors and compatibility feedback;
release correctness must not rely on Lake-only behavior.

Run these checks before handing off a change:

```bash
bazel build //...
bazel test //...
lake build
git diff --check
```

When `MODULE.bazel`, a module dependency, or a toolchain pin changes, refresh
and verify the lockfile explicitly:

```bash
bazel mod graph --lockfile_mode=update
bazel mod graph --lockfile_mode=error
```

Review `MODULE.bazel.lock` with the source change and commit it when it changes.
Do not commit Bazel output trees, `.lake/`, editor state, or generated artifacts
unless a target intentionally owns the generated source.

## Change discipline

- Inspect the worktree and preserve unrelated changes.
- Keep Bazel dependencies aligned with Lean imports.
- Add focused positive and adversarial tests with every API or invariant change.
- Use injected clocks and explicit promises or gates for concurrency tests;
  elapsed sleeps must not establish correctness.
- Update public documentation when observable behavior or API contracts change.
- Make cohesive checkpoint commits only after the relevant checks pass.
