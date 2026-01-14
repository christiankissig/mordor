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
├── forwardingcontext.ml
├── futures.ml
├── interpret.ml
├── ir_context_utils.ml
├── ir.ml
├── justifications.ml
├── landmark_lwt.ml
├── lexer.mll
├── lwt_utils.ml
├── parse.ml
├── parser.mly
├── parser_state.ml
├── pretty.ml
├── rewrite.ml
├── solver.ml
├── solver.mli
├── solver_threadsafe_local.ml
├── solver_threadsafe.ml
├── source_info.ml
├── symmrd.ml
├── types.ml
└── uset.ml
```

consisting of

- **Parser (`parse.ml`, `parser.mly`, `lexer.mll`)**
  - Parses litmus tests
  - Produces AST representation
  - Converts AST to intermediate representation (IR)
  - Performs basic post-parse validation

- **Interpreter (`interpret.ml`)**
  - Interprets litmus tests into symbolic event structures

- **Elaboration (`elaborations.ml`)**
  - Generates justification sets for event structures

- **Executions (`symmrd.ml`, `executions.ml`)**
  - Generates symbolic executions from event structures and justifications

- **Coherence (`coherence.ml`)**
  - Implements coherence constraints for memory models
  - Performs coherence filtering on executions

- **Assertion Checking (`assertion.ml`)**
  - Checks assertions against generated executions  
