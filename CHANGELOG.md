# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] — 2026-04-23

Initial pre-release of MoRDor, a reference implementation of Symbolic MRD from
["Symbolic MRD: Dynamic Memory, Undefined Behaviour, and Extrinsic Choice"](https://2025.splashcon.org/details/OOPSLA/104/Symbolic-MRD-Dynamic-Memory-Undefined-Behaviour-and-Extrinsic-Choice)
(Richards, Wright, Cooksey, Batty — OOPSLA 2025).

> **Caveat:** Pre-release — do not use until version 1.

### Added

#### Analysis Pipeline
- Full symbolic verification pipeline: parse → interpret → elaborate → execute → coherence → assert
- Symbolic event structure construction and manipulation
- Justification set generation and elaboration (with lifted caching)
- Value forwarding analysis
- MRD dependency computation across symbolic executions
- Coherence filtering of candidate executions
- `allow` / `forbid` assertion checking against final execution sets, including undefined-behaviour variants

#### Episodicity Analysis
- Loop periodicity analysis for unbounded programs using symbolic loop semantics
- `episodicity` CLI command and web UI integration

#### Memory Models
- Support for multiple weak memory models configurable via litmus test assertions and web UI settings
- `RelAcq` fence support; compare-and-swap branch events in execution graphs

#### CLI (`mordor`)
- `run` — full verification pipeline with `allow`/`forbid` result reporting
- `parse` — parse litmus tests to IR; output as ISA (Isabelle) or JSON
- `interpret` — generate symbolic event structures from IR
- `visual-es` — visualize event structures as DOT, JSON, or HTML
- `futures` — compute future sets (JSON or ISA output)
- `episodicity` — check loop episodicity
- `--single`, `--all-litmus-tests [-r]`, `--samples` input selection modes
- `--threads <n>` for parallel execution across litmus tests
- `--step-counter` / `--step-counter-per-loop` loop unrolling bounds
- `--symbolic-loop-semantics` for episodicity mode
- `--debug` / `--info` / `--warning` / `--error` log verbosity

#### Web UI (`mordor-web`)
- Dream-based HTTP server with Server-Sent Events (SSE) for real-time analysis progress
- SSE streaming REST API (`/api/visualize/stream`, `/api/parse/stream`, `/api/interpret/stream`, `/api/episodicity/stream`, `/api/assertions/stream`) and test management endpoints (`/api/tests/list`, `/api/tests/run`, `/api/tests/source`)
- Split-screen code editor with syntax highlighting
- Interactive event structure and execution graph visualization with relations filter
- Litmus test runner with file-tree navigation, persistent collapsed state, and per-test action selection
- Use-after-free analysis panel
- Memory model selector and thread count configuration
- Shareable URLs encoding program and selected action
- Persistent graph and analysis results across page refreshes

#### Infrastructure
- Menhir + ocamllex parser for the litmus test format
- Thread-safe Z3 SMT solver interface with mutex-protected caching (`solver.ml`)
- Parallel elaboration and parallel execution generation via Lwt + `lwt_domain`
- Landmarks-based performance profiling (`OCAML_LANDMARKS=on`)
- Docker image and `docker-compose.yml` for one-command deployment
- OVA appliance build tooling
- Alcotest unit test suite with property-based tests
- Integration test suite covering the full litmus test library
- GitHub Actions CI for build and integration tests
