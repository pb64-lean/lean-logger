# Changelog

All notable changes to this project will be documented in this file. The
project has not made a stable release; `0.1.0` is a development coordinate.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

### Added

- Initial Bazel module, layered Lean library targets, Lake editor model, and
  continuous-integration configuration.
- Typed, row-indexed diagnostic context with fresh scoped bindings, explicit
  rebinding, canonical lookup and erasure, dynamic merge policies, redaction,
  and immutable task snapshots.
- Separate typed event-local fields, strict events, causes, provenance, and
  level-gated lazy logging forms.
- Stable compact-text and JSON encoders plus schema-aware compiled patterns
  with elaboration-time literal validation.
- Hierarchical logger levels, ordered filters, serialized console, byte, and
  file appenders, diagnostic isolation, startup unwind, and bracketed runtime
  lifecycle management.
- Bounded asynchronous appenders with three overflow policies, flush barriers,
  coherent statistics, exact worker ownership, supervised failure, compositional
  quiescence, and owner-only terminal batches.
- Bounded deterministic-LRU duplicate suppression with stable structured keys
  and suppression start, resumption, eviction, and close records.
- Deterministic clocks, captures, and promise-based concurrency gates for
  application tests.
- Dependency-mode integration coverage for the public Bazel module surface.
