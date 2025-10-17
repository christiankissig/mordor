[![CI](https://github.com/christiankissig/mordor/actions/workflows/ci.yml/badge.svg)](https://github.com/christiankissig/mordor/actions/workflows/ci.yml)

# MoRDor - Symbolic Modular Relaxed Dependencies (in OCaml)

OCaml implementation of the sMRD memory model verifier, translated from JavaScript.

## Overview

This is a translation of the JavaScript Symbolic Mrder project to OCaml. Mordor
analyzes weak memory models by calculating symbolic dependencies between memory
operations.

## Project Structure

```
mordor/
├── dune-project
├── litmus-tests
│   ├── ...
├── src
│   ├── dune
│   ├── expr.ml
│   ├── interpret.ml
│   ├── main.ml
│   ├── parse.ml
│   ├── rewrite.ml
│   ├── solver.ml
│   ├── symmrd.ml
│   ├── types.ml
│   └── uset.ml
├── SUMMARY.md
├── test
│   ├── ...
├── README.md
└── TRANSLATION_PATTERNS.md
```

## Key Modules

### Types (`types.ml`)
- Core type definitions for events, modes, expressions
- Event types: Read, Write, Fence, Branch, etc.
- Memory ordering modes: Relaxed, Acquire, Release, SC
- Symbolic execution and justification types

### USet (`uset.ml`)
- Generic unordered set implementation
- Uses hash tables for efficient operations
- Supports transitive closure, relations, async operations
- Core data structure used throughout

### Expression (`expr.ml`)
- Expression and value representation
- Symbolic values (Greek letters for reads, Chinese for allocations)
- Expression operations: substitution, equality, simplification

### Rewrite (`rewrite.ml`)
- Expression simplification and rewriting
- Fixed-point rewriting rules
- Arithmetic simplification
- Canonicalization

### Solver (`solver.ml`)
- Z3-based constraint solver
- Converts expressions to Z3 format
- Satisfiability checking
- Model extraction

### Interpret (`interpret.ml`)
- Program interpreter
- Builds symbolic event structure
- Handles loads, stores, fences, threads
- Generates symbolic values

### Symmrd (`symmrd.ml`)
- Main dependency calculation algorithm
- Justification elaboration (filter, forward, lift, weaken)
- Fixed-point computation
- Execution generation

## Differences from JavaScript Version

### Type System
- **Static typing**: All types are explicitly defined
- **Algebraic data types**: Used for enums (event_type, mode, etc.)
- **No `undefined`/`null`**: Uses OCaml's `option` type

### Async/Promises
- **Lwt library**: Replaces JavaScript Promises
- **`let*` syntax**: Monadic bind for async operations
- **Lwt_main.run**: Entry point for async execution

### Data Structures
- **Hash tables**: Replace JavaScript objects for mutable maps
- **Sets**: Custom USet implementation instead of JavaScript's ad-hoc approach
- **No prototype extensions**: Pure functional style with explicit functions

### Object-Oriented vs Functional
- **Modules**: Replace JavaScript classes
- **Objects**: Used sparingly (e.g., `elaborate` object)
- **First-class functions**: Extensive use of higher-order functions

### Memory Management
- **Automatic GC**: No manual memory management needed
- **Immutability**: Encouraged but not enforced
- **Reference counting**: Handled by OCaml runtime

## Dependencies

```bash
opam install lwt z3 zarith containers
```

- **lwt**: Asynchronous programming
- **z3**: SMT solver bindings
- **zarith**: Arbitrary precision integers
- **containers**: Extended standard library

## Building

```bash
dune build
```

## Running

```bash
dune exec smrd
```

## Usage Example

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
3. **Fixed Point**: Repeat until convergence
4. **Generate Executions**: Enumerate valid executions

### Constraint Solving
1. Convert expressions to Z3 format
2. Check satisfiability
3. Extract model (concrete values)
4. Simplify disjunctions

## Limitations

This translation is a **faithful port** but **simplified** in some areas:

1. **Parser**: Not fully implemented (would need ocamllex/menhir)
2. **MSet**: BitSet optimization not implemented
3. **RFSet**: Enumeration strategy simplified
4. **Coherence**: Basic implementation
5. **Stats**: Simplified performance tracking

## Missing Components

To complete the translation, you would need:

1. **Parser** (`parse.ml`): Use ocamllex/menhir for litmus test syntax
2. **Coherence** (`coherence.ml`): Full IMM/RC11 coherence checking
3. **Assertion** (`assertion.ml`): Assertion checking logic
4. **ForwardingContext** (`forwarding.ml`): Full forwarding context
5. **Utilities**: Helper functions, pretty printing

## Testing

Example test suite structure:

```ocaml
let test_store_buffering () =
  let program = parse_program {|
    { x := 1 } ||| { y := 1 }
  |} in
  let* result = verify_program program default_options in
  assert (result.valid);
  Lwt.return_unit

let () =
  Lwt_main.run (test_store_buffering ())
```

## Performance Considerations

- **Z3 overhead**: SMT solving is expensive
- **Set operations**: Hash table based, O(1) average
- **Memory**: OCaml GC handles allocation
- **Parallelism**: Can use Lwt_preemptive for CPU-bound tasks

## Future Work

1. Complete parser implementation
2. Full coherence model support
3. Performance optimizations (MSet bitset)
4. Comprehensive test suite
5. Interactive mode
6. Visualization tools

## References

- Original JavaScript implementation
- "Promising Semantics" paper
- IMM and RC11 memory models
- Z3 SMT solver documentation

## License

Same as original JavaScript implementation.

## Authors

Translated from JavaScript to OCaml (2024)
