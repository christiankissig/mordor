# MoRDor - Core Library

## Overview

The following are the modules in the core library of Mordor

```
├── algorithms.ml
├── assertion.ml
├── ast.ml
├── coherence.ml
├── context.ml
├── dune
├── elaborations.ml
├── episodicity.ml
├── events.ml
├── eventstructures.ml
├── eventstructureviz.ml
├── executions.ml
├── expr.ml
├── forwarding.ml
├── futures.ml
├── interpret.ml
├── ir.ml
├── ir_context_utils.ml
├── justifications.ml
├── landmark_lwt.ml
├── lexer.mll
├── logs_safe.ml
├── lwt_utils.ml
├── monad.ml
├── parse.ml
├── parser.mly
├── parser_state.ml
├── pretty.ml
├── solver.ml
├── source_info.ml
├── types.ml
└── uset.ml
```

consisting of

- **Parser (`parse.ml`, `parser.mly`, `lexer.mll`, `parser_state.ml`)**
  - Parses litmus tests
  - Produces AST representation (`ast.ml`)
  - Converts AST to intermediate representation (IR) (`ir.ml`)
  - Performs basic post-parse validation

- **Interpreter (`interpret.ml`)**
  - Interprets litmus tests into symbolic event structures

- **Elaboration (`elaborations.ml`)**
  - Generates justification sets for event structures

- **Executions (`executions.ml`)**
  - Generates symbolic executions with MRD dependencies from event structures and justifications

- **Coherence (`coherence.ml`)**
  - Implements coherence constraints for memory models
  - Performs coherence filtering on executions

- **Assertion Checking (`assertion.ml`)**
  - Checks assertions against generated executions

- **Forwarding (`forwarding.ml`)**
  - Manages forwarding and write-exclusion contexts in symbolic event structures
  - Computes preserved program order (PPO) under memory model constraints

- **Supporting modules**
  - `types.ml` — Core type definitions shared across modules
  - `events.ml` — Event representation in concurrent executions
  - `eventstructures.ml` — Event structure construction and manipulation
  - `context.ml` — Analysis context, configuration, and pipeline state
  - `expr.ml` — Symbolic expression evaluation
  - `solver.ml` — Z3 SMT solver interface
  - `uset.ml` — Symbolic set operations used throughout analysis
  - `algorithms.ml` — Combination/permutation utilities for constraint solving
  - `justifications.ml` — Justification set generation
  - `futures.ml` — Future set computation
  - `episodicity.ml` — Loop periodicity analysis for unbounded programs
  - `eventstructureviz.ml` — Graph visualization (DOT/JSON/HTML output)
  - `pretty.ml` — Pretty-printing for AST/IR/events
  - `ir_context_utils.ml` — IR traversal utilities (loop IDs and source spans)
  - `source_info.ml` — Source location tracking
  - `monad.ml` — Identity and Lwt monads for sync/async execution switching
  - `logs_safe.ml` — Thread-safe logging wrapper (mutex-protected over `Logs`)
  - `lwt_utils.ml` — Lwt concurrency utilities
  - `landmark_lwt.ml` — Lwt profiling helpers for Landmarks (not compiled into the library)
