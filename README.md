[![CI](https://github.com/christiankissig/mordor/actions/workflows/ci.yml/badge.svg)](https://github.com/christiankissig/mordor/actions/workflows/ci.yml)

# MoRDor - Symbolic Modular Relaxed Dependencies (in OCaml)

Library and command-line tool for symbolic analysis of weak memory models and
generation of weak memory semantics of C-like programs in symbolic modular
relaxed dependencies (MRD). 

MoRDor is a reimplementation and extension of the Symbolic Mrder tool described
in the paper ["Symbolic MRD: Dynamic Memory, Undefined Behaviour, and Extrinsic Choice" by Jay Richards, Daniel Wright, Simon Cooksey, Mark Batty](https://2025.splashcon.org/details/OOPSLA/104/Symbolic-MRD-Dynamic-Memory-Undefined-Behaviour-and-Extrinsic-Choice).

## Overview

MoRDor analyzes weak memory models by calculating symbolic dependencies between
memory operations.

The tool provides a comprehensive command-line interface for:
- Parsing and validating litmus tests
- Running symbolic verification
- Computing future sets for executions
- Visualizing event structures
- Generating Isabelle/HOL theory files for formal verification
- Batch processing with recursive directory scanning

## Project Structure

```
mordor/
├── dune-project
├── litmus-tests
│   ├── ...
├── README.md
├── smrd.opam
├── src
│   ├── ast.ml
│   ├── coherence.ml
│   ├── coherence.mli
│   ├── dune
│   ├── elaborations.ml
│   ├── events.ml
│   ├── eventstructureviz.ml
│   ├── executions.ml
│   ├── executions.mli
│   ├── expr.ml
│   ├── forwardingcontext.ml
│   ├── futures.ml
│   ├── interpret.ml
│   ├── ir.ml
│   ├── justifications.ml
│   ├── lexer.mll
│   ├── main.ml
│   ├── parse.ml
│   ├── parse.mli
│   ├── parser.mly
│   ├── rewrite.ml
│   ├── solver.ml
│   ├── solver.mli
│   ├── symmrd.ml
│   ├── trees.ml
│   ├── types.ml
│   ├── types.mli
│   ├── uset.ml
│   └── utils.ml
├── test
│   ├── ...
```

## Key Modules

### Parser (`parse.ml`, `parser.mly`, `lexer.mll`)
- Litmus test parsing
- Syntax tree generation

### Interpreter (`interpret.ml`)
- Interprets litmus tests into symbolic event structures

### Elaboration (`elaborations.ml`)
- Generate justification sets

### Executions (`executions.ml`)
- Generate symbolic executions

### Symmrd (`symmrd.ml`)
- Main dependency calculation algorithm

### Solver (`solver.ml`)
- Z3-based constraint solving

## Dependencies

```bash
opam install . --deps-only
opam install logs fmt
```

## Building

```bash
dune build
```

## Profiling

```bash
OCAML_LANDMARKS=on dune exec smrd
```

## Running

```bash
dune exec smrd
```

with stacktraces

```bash
OCAMLRUNPARAM=b dune exec smrd
```

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
dune exec smrd -- parse --single test.lit

# Parse with Isabelle output
dune exec smrd -- parse --single test.lit --output-mode isa

# Parse all tests in a directory
dune exec smrd -- parse --all-litmus-tests ./litmus_tests

# Parse recursively with Isabelle output
dune exec smrd -- parse --all-litmus-tests ./litmus_tests -r --output-mode isa
```

#### Computing Futures

```bash
# Compute futures with JSON output
dune exec smrd -- futures --single test.lit --output-mode json

# Compute futures with Isabelle output
dune exec smrd -- futures --single test.lit --output-mode isa --output-file MyFutures.thy

# Compute futures (stdout summary)
dune exec smrd -- futures --single test.lit
```

#### Visualizing Event Structures

```bash
# Generate DOT visualization
dune exec smrd -- visual-es --single test.lit --output-mode dot --output-file output.dot

# Generate JSON visualization
dune exec smrd -- visual-es --single test.lit --output-mode json
```

#### Running Verification

```bash
# Run verification on built-in samples
dune exec smrd -- run --samples

# Run verification on all tests in directory
dune exec smrd -- run --all-litmus-tests ./litmus_tests

# Run verification recursively
dune exec smrd -- run --all-litmus-tests ./litmus_tests -r

# Run verification on single file
dune exec smrd -- run --single test.lit
```

### Isabelle Output Format

When using `--output-mode isa`, MoRDor generates Isabelle/HOL theory files (`.thy`) suitable for formal verification.

#### Parse Command Output
```isabelle
theory ProgramName
  imports Main
begin

(* Parsed from test.lit *)

(* TODO: Add Isabelle formalization *)

end
```

#### Futures Command Output
```isabelle
theory ProgramName_futures
  imports Main
begin

(* Futures for program: test.lit *)

(* Number of executions: 4 *)
(* Number of events: 12 *)

(* TODO: Add Isabelle formalization of futures *)

end
```

Theory files are automatically named based on the input file, or you can specify a custom name with `--output-file`.

## Output Formats

MoRDor supports multiple output formats depending on the command:

### JSON Format
- Used by: `visual-es`, `futures`
- Structured data representation
- Easy to parse and process programmatically
- Example for futures:
  ```json
  {
    "program": "test.lit",
    "executions": [
      {
        "execution": 0,
        "futures": {}
      }
    ]
  }
  ```

### DOT Format (Graphviz)
- Used by: `visual-es`
- Graph visualization format
- Can be rendered with Graphviz tools
- Visualizes event structure and dependencies

### Isabelle/HOL Format
- Used by: `parse`, `futures`
- Generates `.thy` theory files
- Suitable for formal verification in Isabelle
- Includes metadata and placeholders for formalization

### Console Output
- Default for most commands
- Human-readable summaries
- Verification results and statistics

## Usage Examples

### Command Line Usage

See the [Command Line Interface](#command-line-interface) section above for comprehensive CLI examples.

### Programmatic API Usage

```ocaml
open Lwt.Syntax

let program = parse_program {|
  { x := 1; y := 1 } ||| { r1 := y; r2 := x }
|}

let options = {
  dependencies = true;
  just_structure = false;
  exhaustive = false;
  forcerc11 = false;
  forceimm = false;
  forcenocoh = false;
}

let* result = Symmrd.create_symbolic_event_structure program options in
Printf.printf "Valid: %b\n" result.valid;
Lwt.return_unit
```

## Key Algorithms

### Dependency Calculation
1. **Initialize** justifications for all write events
2. **Elaborate** through transformations:
   - **Filter**: Remove covered justifications
   - **Value Assignment**: Assign concrete values
   - **Forward**: Add forwarding edges
   - **Lift**: Merge justifications across branches
   - **Weaken**: Remove unnecessary constraints
   - **Strengthen**: Add required constraints
4. **Generate Executions**: Enumerate valid executions

## Performance Considerations

- **Z3 overhead**: SMT solving is expensive
- **Memory**: OCaml GC handles allocation
- **Parallelism**: Can use Lwt\_preemptive for CPU-bound tasks

## Future Work

1. ~~Complete parser implementation~~ (✓ Implemented)
2. ~~Command-line interface~~ (✓ Implemented)
3. Complete Isabelle formalization output
4. Performance optimizations (MSet bitset)
5. Comprehensive test suite
6. ~~Interactive mode~~ (✓ Multiple commands available)
7. ~~Visualization tools~~ (✓ DOT/JSON output)
8. HTML visualization output
9. Full futures computation (currently generates placeholders)

## References

- "Promising Semantics" pape
- IMM and RC11 memory models
- Z3 SMT solver documentation
