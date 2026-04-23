# MoRDor - CLI

## Overview

The CLI (`main.ml`) is the entry point for the `mordor` executable. It is organized into the following internal modules:

- **`Config`** — Immutable configuration types: `command`, `run_mode`, and the complete `t` record passed through all pipelines
- **`Examples`** — Built-in Store Buffering (SB), Message Passing (MP), and Load Buffering (LB) litmus tests used as default samples
- **`FileIO`** — Loads programs from a single file, a directory of `.lit` files (optionally recursive), or the built-in examples
- **`Display`** — Formats and prints verification results (validity, UB, execution count, event count) to stdout
- **`Pipeline`** — Wires `mordor_lib` pipeline steps together for each command; each function runs `Lwt.return context |> step1 |> step2 |> ...`
- **`CLI`** — `Arg`-based argument parser; accumulates options into a mutable `parse_state`, then converts to an immutable `Config.t`
- **`Logging`** — Configures `Logs` with millisecond-precision timestamps

## Commands and Pipelines

| Command | Pipeline steps |
|---------|---------------|
| `run` | parse → interpret → generate justifications → calculate dependencies → check assertions |
| `parse` | parse |
| `interpret` | parse → interpret |
| `episodicity` | parse → interpret → test episodicity |
| `visual-es` | parse → interpret → generate justifications → calculate dependencies → visualize event structure |
| `futures` | parse → interpret → generate justifications → calculate dependencies → compute futures |
| `dependencies` | not yet implemented |

`episodicity`, `visual-es`, and `futures` require `--single`.

## Options

| Flag | Description |
|------|-------------|
| `--single <file>` | Process a single `.lit` file |
| `--all-litmus-tests <dir>` | Process all `.lit` files in a directory |
| `-r` | Scan recursively (use with `--all-litmus-tests`) |
| `--samples` | Run built-in sample programs (default) |
| `--output-mode <fmt>` | `json`/`dot`/`html` (visual-es) or `isa`/`json` (parse/futures) |
| `--output-file <path>` | Write output to file instead of stdout |
| `--threads <n>` | Number of parallel execution threads (default: 1) |
| `--step-counter <n>` | Global loop unrolling bound (default: 2) |
| `--step-counter-per-loop <n>` | Per-loop unrolling bound |
| `--symbolic-loop-semantics` | Symbolic loop representation (required for episodicity) |
| `--debug` / `--info` / `--warning` / `--error` | Log verbosity |
