#!/usr/bin/env bash
set -euo pipefail
integration_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
suite_dir="$(cd -- "$integration_dir/../../.." && pwd)"
cd -- "$integration_dir"
for dependency in lean-logger otel-lean rules_lean grpc-lean http2-lean tls13-lean; do
  git -C "$suite_dir/$dependency" rev-parse --show-toplevel HEAD
done
bazel mod graph --lockfile_mode=error >/dev/null
bazel test //... --jobs=4 --lockfile_mode=error \
  --override_module="lean-logger=$suite_dir/lean-logger" \
  --override_module="otel-lean=$suite_dir/otel-lean" --test_output=errors
