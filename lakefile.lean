import Lake
open Lake DSL

/-!
# Editor project model

Bazel owns release builds and tests. This Lake package provides the source
model used by editors, `lake serve`, and a convenient compatibility build.
-/

package «lean-logger» where
  version := v!"0.1.0"
  description := "Typed structured application logging for Lean 4"
  keywords := #["logging", "structured-logging", "mdc"]

@[default_target]
lean_lib «Loggers» where
  srcDir := "lean"
  roots := #[`Loggers]

lean_lib «LoggersTestkit» where
  srcDir := "lean"
  roots := #[`Loggers.Testkit]
