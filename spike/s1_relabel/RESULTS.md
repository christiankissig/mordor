# S1 — Relabeling feasibility and cost (#14)

**Verdict: feasible, and it reproduces today's labels exactly.** Fragments
interpreted on their own and relabelled by offset compose into a structure that
is identical to the classic one — every field, labels and symbol names
included, with no canonical renumbering in between — on all 243 programs the
prototype covers. Five things have to be true for that, none of them hard, and
all five are things R8 must carry (below).

Run from the repo root:

    dune exec spike/s1_relabel/s1_relabel.exe -- [-v] [DIR|FILE ...]
    dune exec spike/s1_relabel/s1_relabel.exe -- --cost FILE ...

`run_output.txt` is the output of both. The prototype uses only the public
interfaces of `mordor_lib`, as they stand after R2–R6.

## What was built

A program of the shape `prefix ; { t1 } ||| ... ||| { tn } ; rest` is cut into
fragments — the prefix, each thread, the continuation — and each is interpreted
by `Interpret.interpret_statements` with an `events_t`, and so an `Allocator`
(R5), of its own. Every fragment numbers its events from 0 and names its
symbols from α. Each is then relabelled (`relabel`: every label shifted by an
offset, every symbol renamed, every table and relation rewritten) and the
fragments are composed with the ordinary combinators: `cross` over the threads,
`seq` with the continuation, the prefix chained in front, `dot` for Init. That
the combinators can do this at all is R4 and R6: the fragments own their tables
and `cross` merges them.

The result is compared with `Interpret.interpret` of the whole program, field by
field, sets and tables rendered sorted. Loop semantics is `Generic` on both
sides, since that is the statement semantics the interface exposes.

| | |
|---|--:|
| files (`litmus-tests*`, `programs/`) | 379 |
| skipped: no parallel block | 17 |
| skipped: nested or repeated parallel block | 45 |
| skipped: branching prefix | 74 |
| **compared** | **243** |
| **identical, labels and all** | **243** |

A branching prefix is skipped because classic duplicates the continuation once
per branch; that is sequencing-with-copies, which S2 (#15) answered. Nested
blocks are skipped only because the prototype numbers threads flatly.

## Answers

### 1. Does the final renumbering reproduce today's labels exactly?

**Yes, and no renumbering pass is needed to get there.** If fragments are laid
out in program order — prefix, threads left to right, continuation — and each
fragment's offset is the number of labels handed out before it, the labels *are*
today's. The same holds for symbols, with one offset per alphabet. Goldens stay
readable and byte-identical.

Two details make "the number of labels handed out" the right offset, rather than
the number of events:

- An elided branch has already taken a label (R6's phantom events). The
  allocator's count includes it; `|e|` does not.
- A fragment interpreted alone ends in a terminal event the whole program does
  not have where another fragment follows. The prefix's terminal takes the
  prefix's last label, and the next fragment starts *at* that label, not after
  it.

### 2. What relabelling has to reach (the things that went wrong first)

1. **`Event.relabel` (`events.ml:230`) does not relabel `cond`.** It covers
   `loc`, `rval` and `wval`; a branch event carries its guard in `cond`, symbols
   included. The prototype relabels `cond` itself. R8 should fix `Event.relabel`.
2. **A symbol hides inside a string.** `ub_assume` (`interpret.ml`) records a UB
   assumption in the register environment under the key `"%ub:" ^ symbol`. No
   expression traversal finds it. This was the only structural difference in the
   first full run (`avoidoota/listing27_allow`, `additional_twosource`: `p`
   differed, `%ub:α` against `%ub:β`). The prototype rewrites such keys; R8
   should either do the same or key the fact by something that is not a name.
3. **Inherited symbols can be captured.** A thread's initial environment holds
   symbols of the prefix (`r := x` before the block gives `r -> α`), and the
   thread's own first symbol is also `α`. Interpreted naively, the two are the
   same symbol. The prototype renames inherited symbols to placeholders before
   interpreting the fragment and back afterwards — S2's "symbolic initial
   register footprint", concretely. The allocator has no way to start anywhere
   but zero; R8 wants either `Allocator.create ~from` or the placeholder scheme.
4. **`Expr.relabel` re-evaluates** (`expr.ml:586` ends in `|> evaluate`). On this
   corpus that changed nothing — evaluation is idempotent on everything compared
   — but it is work done per expression, and a relabelling that could simplify
   would break identity with classic. Worth a relabel that does not evaluate.
5. **`thread_index` is interpreter state, not fragment state.** A thread
   interpreted alone stamps its events with thread 0. The prototype overwrites
   the index when it relabels; in R8 the `par` combinator has to assign it.

### 3. `constraints` is not compositional

The distinctness constraints (globals pairwise distinct, allocations pairwise
distinct and distinct from globals) are attached to each *terminal* structure,
computed from everything the interpreter has seen *so far* (`events.globals`,
every `Malloc` in `events.events`). They are a property of interpretation order,
not of any fragment:

- The union of the fragments' own constraints equals classic's on 234 of 243.
  The other 9 have allocations in different fragments, and no fragment knows of
  the pair: classic has `一 != 二`, the union has nothing.
- Recomputing the constraints once, at the top, from the composed structure
  equals classic's on 237 of 243 and is a strict superset on the other 6. Those
  6 are loop programs under `Generic` semantics, where an uninterpreted loop
  ends its thread with no terminal, so classic attaches constraints for fewer
  allocations than the program has (`uaf-bug-extended`: three allocations,
  `一 != 二` only). Under the default loop semantics classic has all three; this
  is an artifact of the comparison's loop semantics, not a bug in production.

**R8 should compute `constraints` once, at the top level, from the finished
structure**, and stop attaching them at terminals. It is the only field that
cannot be built by the combinators.

### 4. Label-order-dependent code

With labels reproduced exactly, none of this breaks under R8 as prototyped. It
is the list of what *would* break if fragments were ever laid out in another
order, or labels left fragment-local.

**Label order used as program order (semantic):**

| site | what it assumes |
|---|---|
| `canonicalize.ml:62–70` `canonical_order` | "Event labels are allocated in program order, so within a thread this reproduces program order." **This is the golden gate itself.** Its canonical form is only canonical while labels are program-ordered within a thread. |
| `assertion.ml:879–882` `Refinement.allocations` | Sorts `malloc_events` by label and takes the index as the allocation's identity: "program order gives the two programs of a chain a correspondence between their allocations." |
| `isa_export.ml:426` | Sorts the events of one statement by label and names them `#0, #1, …`; with `command_and_events`' tables (`:96–320`, `[(0,"R"); (1,"Branch"); (2,"W")]`) it assumes a statement's events are labelled consecutively in a fixed order. |

**Label 0 is the initial event (semantic):**

`eventstructures.ml:463` · `forwarding.ml:430–432` · `coherence.ml:1000`,
`:1789`, `:1819–1820`, `:1882` · `executions.ml:384`, `:425`, `:763`, `:801` ·
`eventstructureviz.ml:614`, `:724` (`isRoot`) · `canonicalize.ml` (init kept
visible as an rf endpoint).

**Sorted by label for determinism only (output order, hashing; any injective
relabelling is fine):** `executions.ml:96`, `:268`, `:1402` ·
`executions_export.ml:121` · `elaborations.ml:1317` · `justifications.ml:129–130`
· `coherence.ml:1338`, `:1884`, `:1896` · `episodicity.ml:497`, `:806`, `:1018`,
`:1423`, `:1470`, `:1475` · `eventstructureviz.ml:789`.

No site compares two labels with `<` to decide program order directly; the
dependence is always through a sort.

### 5. Cost

On the compared programs relabelling is 3ms in total against 13ms to interpret
the fragments and 51ms to interpret the programs classically — the litmus tests
are 20-odd events each and tell us nothing. For realistic sizes, `--cost` takes
the structure the default pipeline builds (loops unrolled) and relabels all of
it:

| program | events | po | conflict | interpret | relabel | |
|---|--:|--:|--:|--:|--:|--:|
| `rcu-3` | 1463 | 60,064 | 607,428 | 1.11s | 0.31s | 28% |
| `rcu-2` | 371 | 12,135 | 46,752 | 0.13s | 0.013s | 10% |
| `hp-1` | 291 | 9,680 | 65,030 | 0.13s | 0.017s | 13% |
| `rcu-1` | 83 | 1,966 | 2,874 | 0.013s | 0.001s | 8% |

Timings on this machine move by a factor of two between runs (`rcu-3` interprets
in 1.1–2.1s); `rcu-3`'s ratio holds at 18–28%.

**The cost is the conflict relation.** Of `rcu-3`'s 0.31s, 0.27s is rewriting
607k conflict pairs; `po` is 0.01s and the register environments — 15,762
bindings, each through `Expr.relabel` — 0.002s. `conflict` is stored
extensionally and `plus` adds a full cross product to it, so it is quadratic in
the size of the branches.

Against the pipeline this is nothing: `rcu-3` does not finish in six minutes
(S4). But it is per relabelling, and a bottom-up build that relabelled at every
merge would pay it once per level of nesting. Two ways out, either enough:

- **Relabel once.** Sizes are known bottom-up and offsets top-down: count first,
  then relabel each leaf fragment straight to its final offset. The prototype
  does exactly this, which is why it needs no renumbering pass.
- **Keep `conflict` intensional** — as the pairs of sibling branches rather than
  the pairs of their events — and relabelling it costs nothing. That is a bigger
  change and pays off elsewhere too (`generate_max_conflictfree_sets`).

## For R7 and R8

- The relabel utility R7 needs for its law tests ("commutativity up to
  relabeling") is `relabel` here, plus the fix to `Event.relabel`. It belongs in
  `eventstructures.ml`.
- R8's top-level renumbering pass can be dropped from the plan if offsets are
  assigned in program order from allocator counts; the goldens then hold by
  construction rather than by a pass.
- R8 must: assign `thread_index` in `par`; compute `constraints` at the top;
  protect inherited symbols; reach the `%ub:` keys.
- `Canonicalize.canonical_order` should be made independent of label order (a
  topological order of `po` within a thread) *before* R8, so that the gate is
  not the thing R8 silently depends on.
