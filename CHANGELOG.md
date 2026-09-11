# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Breaking

- **Unknown memory model names are an error.** An annotation naming a model MoRDor does not implement, such as `[C11]`, `[RA]`, `[Promising]` or `[JMM]`, used to log a warning and fall back to the default model. It now fails, and `--allow-unknown-model` brings back the old warn-and-continue behaviour ([#86](https://github.com/christiankissig/mordor/issues/86)).
- **A test that names no model runs under sMRD.** The default used to be `undefined`, which checks RMW atomicity and nothing else, so a test with no annotation got no coherence or thin-air checking at all (`9fd5a15`).
- **`@x` in an assertion means the final value stored at `x`.** It used to be the location variable, which made every `@` assertion vacuous. It also sees writes that reach `x` through a pointer ([#84](https://github.com/christiankissig/mordor/issues/84), [#5](https://github.com/christiankissig/mordor/issues/5)).
- **A program's expressions are over registers.** A global, `@x` or `&` in an expression, and `free` of a global, are parse errors naming the statement's line and column. A global is read by a load and written by a store, each its own event, and its address is taken only by `r := &x`. Before, a global in an expression silently meant its address rather than its value: `r := x + 1` added one to where `x` lives, `if (x = 1)` compared that address, `*p := v` wrote to `p` itself, and `A := &x` stopped the run with "Unsupported unary operator &". `cas` and `fadd` on a global now take a reference, `rx := &x; r := cas(…, rx, …)`, and the 24 corpus programs that passed a global directly are rewritten that way.
- **Statements after a parallel block run.** They used to be silently dropped. They now execute once every thread in the block has finished ([#81](https://github.com/christiankissig/mordor/issues/81)).
- **Library API:** `USet.inplace_union` takes the set it mutates as `~into` ([#88](https://github.com/christiankissig/mordor/issues/88)). `symbolic_execution` has two new fields, `co` and `justifications`. `Eventstructures.dslwb` takes an optional `?state`.
- **The Java Causality Test Cases have left the scanned suite.** They are now annotated `[JMM]` and live in `litmus-tests-jmm/`.
- Removed the `promising` memory model, which was a misleading alias to IMM: promising semantics is operational and cannot be expressed by the axiomatic coherence checker. The promising-paper litmus tests are kept for reference under `litmus-tests-promising/`, with runnable `[IMM]` copies in `litmus-tests/popl_promising/` ([#9](https://github.com/christiankissig/mordor/pull/9)).

### Added

#### Command line
- `executions` command, and `POST /api/executions`, for exporting executions with their events and relations (`6db5120`).
- `justifications` command, which lists the program's justification set and the elaboration step behind each justification, as text or with `--output-mode json` ([#80](https://github.com/christiankissig/mordor/issues/80)).
- `dependencies` command. It used to print a TODO and exit 0 (`3d3a934`).
- `--output-mode isa`, an Isabelle interchange export ([#10](https://github.com/christiankissig/mordor/pull/10)).
- `--allow-unknown-model` ([#86](https://github.com/christiankissig/mordor/issues/86)).

#### Assertions and semantics
- Refinement chains (`~~>`) are now decided. The checker compares the programs' observable register states, and a register that holds a pointer is compared by which allocation it points to ([#85](https://github.com/christiankissig/mordor/issues/85), [#87](https://github.com/christiankissig/mordor/issues/87)).
- `.co`, the coherence order an execution was admitted under, can be used in assertions. It is also exported, as the canonically least order that admits the execution ([#66](https://github.com/christiankissig/mordor/issues/66)).
- `[_]` is accepted as a model annotation meaning "any model".
- A `volatile` load or store is never elided by forwarding. That is all `volatile` means ([#83](https://github.com/christiankissig/mordor/issues/83)).
- A UB assumption from folding `1 / !r` to `1` now reaches elaboration as a de facto constraint, so the narrowed write and the original write are both justified (partial fix for [#65](https://github.com/christiankissig/mordor/issues/65)).

#### Web UI
- A manual, opened from Manual in the top bar. It introduces MoRDor as a tool for exploring weak memory through justified executions, explains the concepts, describes every part of the web UI and common tasks, and includes the language reference that was the help page. `/help/` serves it too.
- The settings choose a primary memory model, or the test's own, and further models to compare. Each compared model checks every execution, the log gives each model's count, and an execution shows which other models also allow it. The same comes through `compare_models` on the stream API ([#82](https://github.com/christiankissig/mordor/issues/82)).
- `MORDOR_WEB_PORT` sets the web server's port, which is still 8080 by default.
- The final register state of each execution ([#8](https://github.com/christiankissig/mordor/issues/8)).
- The justifications each execution was frozen from, and the program's whole justification set with the elaboration step behind each justification ([#3](https://github.com/christiankissig/mordor/issues/3), [#80](https://github.com/christiankissig/mordor/issues/80)).
- TikZ export that keeps the on-screen layout ([#77](https://github.com/christiankissig/mordor/issues/77)), and DOT export with node positions (`2b70ef4`).
- The example dropdown is served from the test corpus and grouped by family ([#76](https://github.com/christiankissig/mordor/issues/76)).
- Forwarding and write-elision edges in the execution graph (`4e42074`).
- A light/dark theme switch ([#35](https://github.com/christiankissig/mordor/pull/35)).
- Episodicity verdicts appear loop by loop as each one finishes (`045b6f9`).

#### Testing
- A golden-diff suite, a canonicalizer and stage counters ([#34](https://github.com/christiankissig/mordor/pull/34)).
- An episodicity integration suite with a per-test deadline (`8a47197`).
- RMM Zoo property and model litmus tests ([#40](https://github.com/christiankissig/mordor/pull/40)).
- Reference directories for tests MoRDor cannot decide: `litmus-tests-cpp/`, `litmus-tests-ra/`, `litmus-tests-promising/` and `litmus-tests-jmm/` for models it does not implement, and `litmus-tests-review/` for tests whose outcome it disagrees with. Each has a README.

### Fixed

#### Assertion checking
- `forbid` assertions reported valid without looking at a single execution (`4998e70`).
- Conditions were checked without the execution's own path predicates, so outcomes the execution contradicts still came back satisfiable (`48026cd`).
- Set-membership tests gave answers about events the execution does not contain (`0bca217`).
- Refinement verdicts depended only on the `allow`/`forbid` keyword; neither program was ever run ([#85](https://github.com/christiankissig/mordor/issues/85)).
- Use-after-free and unbounded-dereference detection only found a pointer that was the allocation's own symbol, such as a register assigned by `malloc`. A pointer loaded from memory is a read's symbol, and its rf edge to the allocation was never followed, so a use after free through a pointer held in a global, or in any other cell, went unreported. `symmrd/LB+UB+data+arr.lit` now reports an unbounded dereference: in executions where `r1 = 1`, its read `*(ra + 1)` is past the end of the allocation and takes its value from `x` or `y`, not from any store to the allocation. Those executions exist only because an offset into an allocation may still alias a global.
- A condition over registers holding references compared the values of the globals they refer to: over `rp := &x; rq := &y`, `forbid (rp = rq)` failed whenever `x` and `y` held the same value.

#### Interpretation
- Symbolic `while` and `do` loops produced no executions ([#11](https://github.com/christiankissig/mordor/pull/11)).
- `do { B } while (c)` never reached the loop after its first iteration (`76cc05c`).
- `x := malloc n` did not store the address to `x`, so a later load from `x` read whatever it held before, and two allocations held in globals could be the same cell. It is now an allocation followed by a store to `x`.
- `free(x)` of a global freed nothing: the parser turned it into a free of an unbound register, so the deallocation had no location. It is now refused (see Breaking).
- A global reached only through a reference, `r := &y`, was left out of the constraint that distinct globals are distinct locations. Forwarding and elaboration read that constraint, so a write through the reference was treated as possibly overwriting every other global.
- `interpret` printed every deallocation as `Free _`.
- The `e / !r -> e` undefined-behaviour fold was applied under every model. It now applies only when the model allows it, as `[UB11]` does (`365fa76`).

#### Dependencies and elaboration
- Value assignment took a value from whichever model the solver returned. It now fills in a value only when the justification's predicates force it. This closes an out-of-thin-air witness in `avoidoota/listing16.lit` ([#43](https://github.com/christiankissig/mordor/issues/43), `ae177d0`).
- Value assignment dropped the guard that fixed a write's value, and fired even when it left the write unchanged (`71ba377`, `bf93af4`).
- Forwarding is followed when freezing the dependency relation, so a forwarded read no longer drops a dependency (`f7c45d3`).
- An elided write could stop a read from reading an earlier write (`15df03a`). `dslwb` now decides shadowing under the same path predicates as the rf edge beside it (`540171f`).
- Preserved program order kept same-location read pairs, and now orders accesses that *may* alias ([#38](https://github.com/christiankissig/mordor/issues/38)).
- The RMW part of preserved program order composed `ppo_sync` with each (read, write) pair rather than (write, read), as the episodic loops paper defines it. For a CAS or fetch-and-add that ordered nothing, so neither acted as a synchronisation point, and forwarding could cross one. `popl_bridging/ARM FADD.lit` drops from 93 to 79 executions. No verdict changes.

#### Coherence
- sMRD's happens-before relation had no synchronises-with edge, so release-acquire chains were invisible to it ([#67](https://github.com/christiankissig/mordor/issues/67), [#68](https://github.com/christiankissig/mordor/issues/68)).
- IMM's coherence check overwrote a set it shared across every candidate coherence order, so the search's answer depended on the order candidates were tried ([#88](https://github.com/christiankissig/mordor/issues/88)).
- A nonatomic store or load matched RC11's "relaxed or stronger" tests, because matching also asked the mode fields an event's type does not use, and those default to relaxed. A nonatomic store could then synchronise two fences (`own/nonatomic-store-no-sync.lit`).
- RC11's SC check ignored sc stores and loads: it collected sc accesses from `Init` events, of which there are none, so only `fence(sc)` took part. Store buffering over sc accesses came out allowed (`own/SB+sc.lit`). Its `scb` also had `sbl;hb` where RC11 has `sbl;hb;sbl`.
- The coherence order grouped writes by location without the execution's predicates, so a write through a pointer was never ordered against a write to the location it points at, and a read could take the value it had overwritten. This applied under every model (`own/ptr-overwrite-coherence.lit`). `fowm2024/load intro` (both variants) drop from 4 to 1 execution, `own/JCTC12.lit` from 12 to 8 and `avoidoota/listing9.lit` from 21 to 19. No verdict changes.
- RC11 applied the full coherence check only to executions without RMWs (`27271c9`), and built both ends of `psc_base` from one shared set (`cbb4b3a`).
- IMM and RC11 were over-permissive ([#9](https://github.com/christiankissig/mordor/pull/9)): release/acquire synchronisation ignored the mode lattice, the coherence axioms were skipped for programs with fewer than two writes, and the init write could be permuted out of first place.

#### Episodicity
- Many fixes to the write and events conditions and to loop handling: loop conditions and guards recorded per path and per occurrence, allocation interiors kept apart from other allocations, reads no longer reported against writes they conflict with, and RMW preserved program order used in the events condition. `hp-1` and `rcu-1` are back in the suite and reported episodic.

#### Web UI
- Parse errors are shown instead of breaking the page (`b1cf28e`).
- A statement at the start of a line was placed at the end of the line before, in the source span that highlights its events in the editor.
- Errors from the server never reached the log: the page looked for a field the server does not send, so a parse error or an unknown model only turned the status to *Error*. They are now logged. A parse error quotes the offending line with a caret, and the editor marks the token. Its message gives the 1-based column where the token starts and names the token, where it used to give a column past the token's end and say only "Parse error: Parse error at …". The program is sent untrimmed, so line numbers are the editor's.
- The justification panels are laid out one entry per line, and their Show/Hide button works (`0779cdf`).
- Every event in a graph was drawn with the ring meant for the initial event, and in the light theme edge labels sat on a dark backing.
- Messages about loading a file, loading a program from a link and sharing were put at the top of the log, above older entries.
- The language reference's examples: the CAS example did not parse and read a failed swap as success, the store-buffering example was not store buffering, the load-buffering example allowed an outcome only thin air produces, and all of them used `[x = 0]`, a de facto guarantee, as if it initialised memory. `cas` and `fadd` now say what they put in the register, and the model names `c11` and `sc`, which MoRDor rejects, are gone.

### Changed
- The web UI has a new look: panels as cards, one set of line icons in place of emoji, and matching Inter and JetBrains Mono type in the app and the manual. The top bar runs in the order you work: the action button, whose menu says what each action runs; Settings, with a summary of the models and loop semantics the next run uses; the run's status; Share, moved up from the editor; Tests; then Manual and the theme toggle. The log has a Clear button.
- Litmus corpus: tests MoRDor's verdict disagrees with are parked in `litmus-tests-review/`, each linked to an issue. Tests since decided correctly have returned to the suite.
- The RCU read-side critical-section markers in `programs/` are `volatile`.

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
