[![CI](https://github.com/christiankissig/mordor/actions/workflows/ci.yml/badge.svg)](https://github.com/christiankissig/mordor/actions/workflows/ci.yml)

[![Litmus Tests](https://github.com/christiankissig/mordor/actions/workflows/integration.yml/badge.svg)](https://github.com/christiankissig/mordor/actions/workflows/integration.yml)


# MoRDor - Symbolic Modular Relaxed Dependencies (in OCaml)

MoRDor is a static code analysis tool implementing weak memory semantics of
C-like programs based on a symbolic variant of Modular Relaxed Dependencies
(MRD).

MoRDor is a reference implementation of Symbolic Modular Relaxed Dependencies
(SMRD)
["Symbolic MRD: Dynamic Memory, Undefined Behaviour, and Extrinsic Choice" by Jay Richards, Daniel Wright, Simon Cooksey, Mark Batty](https://2025.splashcon.org/details/OOPSLA/104/Symbolic-MRD-Dynamic-Memory-Undefined-Behaviour-and-Extrinsic-Choice).

**Caveat** Do not use until version 1.

## Overview

MoRDor analyzes weak memory models by calculating symbolic dependencies between
memory operations.

The tool provides a comprehensive command-line interface and web UI for:
- Parsing and validating programs and litmus tests
- Deciding episodicity of unbounded loops
- Computing and visualising event structures and executions
- Running symbolic verification

## Project Structure

```
mordor/
├── dune-project
├── README.md
├── Dockerfile
├── docker-compose.yml
├── Makefile
├── src/          # Core library (mordor_lib) — see src/README.md
├── cli/          # CLI entry point (mordor) — see cli/README.md
├── web/          # Web server (mordor-web) — see web/README.md
├── test/         # Unit and integration tests
├── litmus-tests/ # Litmus test suite
└── programs/     # Sample concurrent programs
```

- `src/`: Core analysis library shared by CLI and web server. See [src/README.md](src/README.md).
- `cli/`: `mordor` executable — argument parsing, pipeline orchestration. See [cli/README.md](cli/README.md).
- `web/`: `mordor-web` Dream server — SSE streaming, REST API, browser UI. See [web/README.md](web/README.md).
- `test/`: Alcotest unit tests (`dune test`) and integration tests (`dune exec test/test_integration.exe`).
- `litmus-tests/`: Litmus test suite run by CI.
- `programs/`: Hand-written sample programs including episodicity examples.

## Building the MoRDor Web UI

It is recommended to build and run MoRDor in Docker using the Makefiles. See the
[Docker Guide](DOCKER_GUIDE.md) for details.

```bash
make build # build the Docker container image
make run   # run the Docker container
make stop  # stop the Docker container
make clean # clean up
```

## Building the Executables

Build with Dune

```bash
dune build
```

Build and view documentation with

```bash
opam install odoc
dune build @doc
xdg-open _build/default/_doc/_html/index.html 
```

## Profiling

```bash
OCAML_LANDMARKS=on dune exec mordor
```

## Running

Run the CLI with

```bash
dune exec mordor
```

with stacktraces

```bash
OCAMLRUNPARAM=b dune exec mordor
```

It is recommended to run the Web interface in Docker as described in the
[Docker Guide](DOCKER_GUIDE.md).

```bash
make run
```

Run the Web UI locally with

```bash
dune exec mordor-web
```

## Testing

Run unit tests with

```bash
dune test
```

Run integration tests (core pipelines and litmus test suite) with

```bash
dune exec test/test_integration.exe
```

## Command Line Interface

MoRDor supports several commands for analyzing litmus tests and generating outputs.

### Commands

- **`run`**: Full verification pipeline — parse → interpret → dependencies → assertions
- **`parse`**: Parse a litmus test to IR only
- **`interpret`**: Parse and interpret to generate the event structure
- **`episodicity`**: Check loop episodicity (requires `--single`)
- **`visual-es`**: Visualize event structures (requires `--single`)
- **`dependencies`**: Compute dependency relations (not yet implemented)

### Options

#### Input Selection
- `--samples`: Use built-in sample programs (default)
- `--all-litmus-tests <dir>`: Process all `.lit` files in specified directory
- `-r`: Scan directories recursively (use with `--all-litmus-tests`)
- `--single <file>`: Process a single `.lit` file

#### Output Configuration
- `--output-mode <mode>`: Set output format
  - `json`: JSON format (visual-es, futures)
  - `dot`: Graphviz DOT format (visual-es)
  - `html`: HTML format (visual-es)
  - `isa`: Isabelle theory output (parse, futures)
- `--output-file <file>`: Output file path (default: stdout)

#### Loop Semantics
- `--step-counter <n>`: Global loop unrolling bound (default: 2)
- `--step-counter-per-loop <n>`: Per-loop unrolling bound
- `--symbolic-loop-semantics`: Symbolic loop representation (required for `episodicity`)

#### Execution
- `--threads <n>`: Number of parallel threads (default: 1)

#### Logging
- `--debug` / `--info` / `--warning` / `--error`: Log verbosity level

### Usage Examples

#### Parsing Litmus Tests

```bash
# Parse a single litmus test
dune exec mordor -- parse --single test.lit

# Parse with Isabelle output
dune exec mordor -- parse --single test.lit --output-mode isa

# Parse all tests in a directory
dune exec mordor -- parse --all-litmus-tests ./litmus-tests

# Parse recursively
dune exec mordor -- parse --all-litmus-tests ./litmus-tests -r
```

#### Running Verification

```bash
# Run verification on built-in samples
dune exec mordor -- run --samples

# Run verification on a single file
dune exec mordor -- run --single test.lit

# Run verification on all tests in directory
dune exec mordor -- run --all-litmus-tests ./litmus-tests

# Run verification recursively with parallel threads
dune exec mordor -- run --all-litmus-tests ./litmus-tests -r --threads 4
```

#### Visualizing Event Structures

```bash
# Generate DOT visualization
dune exec mordor -- visual-es --single test.lit --output-mode dot

# Generate JSON visualization
dune exec mordor -- visual-es --single test.lit --output-mode json
```

#### Checking Episodicity

```bash
# Check loop episodicity (uses symbolic semantics automatically)
dune exec mordor -- episodicity --single programs/episodicity/example.lit
```
