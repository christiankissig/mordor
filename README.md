[![CI](https://github.com/christiankissig/mordor/actions/workflows/ci.yml/badge.svg)](https://github.com/christiankissig/mordor/actions/workflows/ci.yml)

[![Litmus Tests](https://github.com/christiankissig/mordor/actions/workflows/integration.yml/badge.svg)](https://github.com/christiankissig/mordor/actions/workflows/integration.yml)


# MoRDor - Symbolic Modular Relaxed Dependencies (in OCaml)

MoRDor is a static code analysis tool implementing weak memory semantics of
C-like programs based on a symbolic variant of Modular Relaxed Dependencies
(MRD).

MoRDor is a reimplementation and extension of the Symbolic Mrder tool described
in the paper ["Symbolic MRD: Dynamic Memory, Undefined Behaviour, and Extrinsic Choice" by Jay Richards, Daniel Wright, Simon Cooksey, Mark Batty](https://2025.splashcon.org/details/OOPSLA/104/Symbolic-MRD-Dynamic-Memory-Undefined-Behaviour-and-Extrinsic-Choice).

MoRDor aims to be correct and efficient enough to calculate the semantics of
real-world concurrent algorithms, in addition to litmus tests.

**Caveat** Do not use until version 1.

## Overview

MoRDor analyzes weak memory models by calculating symbolic dependencies between
memory operations.

The tool provides a comprehensive command-line interface and web UI for:
- Parsing and validating programs and litmus tests
- Running symbolic verification
- Determine episodicity of unbounded loops
- Computing executions and future sets
- Visualizing event structures

## Project Structure

```
mordor/
├── dune-project
├── README.md
├── Dockerfile
├── docker-compose.yml
├── Makefile
├── src
│   ├── README.md # [See detailed module documentation](src/README.md)
│   ├── ...
├── cli
│   ├── ...
├── web
│   ├── ...
├── test
│   ├── ...
├── litmus-tests
│   ├── ...
├── programs
│   ├── ...
```

with

* `src/`: Core library modules
* `cli/`: Command-line interface
* `web/`: Web interface
* `test/`: Unit and integration tests
* `litmus-tests/`: Sample litmus tests
* `programs/`: Sample concurrent programs

For more details about the core library modules, see the
[src/README.md](src/README.md).

## Building

It is recommended to build and run MoRDor in Docker using the Makefiles. See the
[Docker Guide](DOCKER_GUIDE.md) for details.

```bash
make build
make run
make stop
make clean
```

Build executables with

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

Run the Web interface with

```bash
dune exec mordor-web
```

## Testing

Run unit tests with

```bash
dune test
```

Run integration tests with

```bash
dune exec test/test_integration.exe
```

Run the litmus tests with

```bash
dune exec test/test_integration.exe
```

or through the Web interface, pressing the "🧪 Litmus Tests" button.

## Command Line Interface

MoRDor supports several commands for analyzing litmus tests and generating outputs.

### Commands

- **`run`**: Execute verification on test programs
- **`parse`**: Parse litmus test files (supports Isabelle output)
- **`interpret`**: Interpret and verify programs
- **`visual-es`**: Visualize event structures (single file only)
- **`futures`**: Compute future sets for executions (single file only)

### Options

#### Input Selection
- `--samples`: Use built-in sample programs (default)
- `--all-litmus-tests <dir>`: Process all `.lit` files in specified directory
- `--single <file>`: Process a single `.lit` file
- `-r`: Scan directories recursively (use with `--all-litmus-tests`)

#### Output Configuration
- `--output-mode <mode>`: Set output format
  - `json`: JSON format (for visual-es, futures)
  - `html`: HTML format (for visual-es, not yet implemented)
  - `dot`: Graphviz DOT format (for visual-es)
  - `isa` or `isabelle`: Isabelle theory files (for parse, futures)
- `--output-file <file>`: Specify output file (default: stdout or auto-generated)

### Usage Examples

#### Parsing Litmus Tests

```bash
# Parse a single litmus test
dune exec mordor -- parse --single test.lit

# Parse with Isabelle output
dune exec mordor -- parse --single test.lit --output-mode isa

# Parse all tests in a directory
dune exec mordor -- parse --all-litmus-tests ./litmus_tests

# Parse recursively with Isabelle output
dune exec mordor -- parse --all-litmus-tests ./litmus_tests -r --output-mode isa
```

#### Computing Futures

```bash
# Compute futures with JSON output
dune exec mordor -- futures --single test.lit --output-mode json

# Compute futures with Isabelle output
dune exec mordor -- futures --single test.lit --output-mode isa --output-file MyFutures.thy

# Compute futures (stdout summary)
dune exec mordor -- futures --single test.lit
```

#### Visualizing Event Structures

```bash
# Generate DOT visualization
dune exec mordor -- visual-es --single test.lit --output-mode dot --output-file output.dot

# Generate JSON visualization
dune exec mordor -- visual-es --single test.lit --output-mode json
```

#### Running Verification

```bash
# Run verification on built-in samples
dune exec mordor -- run --samples

# Run verification on all tests in directory
dune exec mordor -- run --all-litmus-tests ./litmus_tests

# Run verification recursively
dune exec mordor -- run --all-litmus-tests ./litmus_tests -r

# Run verification on single file
dune exec mordor -- run --single test.lit
```
