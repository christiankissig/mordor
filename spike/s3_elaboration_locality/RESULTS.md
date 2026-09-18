# S3: elaboration per thread against elaboration of the whole (#16)

**Verdict: elaboration is local to a thread, and code after a join is
elaborated at the join.** Each top-level thread, with any blocks nested in it
and the events outside every thread, elaborated on its own, gives exactly the
whole program's justifications for its events. On 315 of the 318 multi-threaded
programs the plain per-thread union is already the whole set. The other 3 have
code after a join, whose justifications carry forwarding edges of every thread
it joins. Elaborated per thread, that code gets contexts with one thread's
edges, and the pipeline then finds no execution at all. Elaborated where the
threads are joined, it gets the whole program's justifications. So Phase 2b can
compute justifications locally, fragment by fragment, if a fragment that
follows a join is elaborated over the join and not over one thread.

Run from the repo root:

    dune exec spike/s3_elaboration_locality/s3_elaboration_locality.exe -- FILE ...

(`S3_SHOW=1` prints the justifications that differ.)

## (a) The definitions

The Symbolic MRD elaborations, as `episodic-loops-paper/app-defs.tex` restates
them from Richards et al. (Definition `def:gen-just` and the elaboration
definitions after it), and what each of them reaches:

| elaboration | reads | reach |
|---|---|---|
| Value Assignment | the justification's own `P` and expressions | the justification |
| Forwarding, Write Elision | a pair of events, and `ppo` under `P` and the forwarding context | events `ppo`-related to the justified write |
| Strengthening | origins of the symbols it adds, each required to be `⊑` the write or after it, and not `ppo`-after it | events po-related to the write |
| Lifting | two justifications whose writes are closed relabel-equivalent, through `pred_δ` | writes in conflicting branches, and their `ppo` predecessors; conflict only arises within a thread |
| Weakening | `Ω`, the program's global guarantees | a constant of the whole program, not other threads' justifications |

None of them is defined over the whole structure in a way that reaches
another thread's events, except through `po`. And `po` reaches across threads
at exactly two places: the fork (code before a block precedes every thread)
and the join (every thread precedes the code after the block). So the
definitions compose over fragments that are closed under those two. A thread
fragment has to include what precedes the block. What follows a join has to be
elaborated with every thread it joins. `Ω` is supplied from the top, as R8
already computes the distinctness constraints once, from the whole structure.

## (b) The experiment

For each tracked program with a parallel block, justifications are generated
three ways:

- **whole:** `Elaborations.step_generate_justifications` on the whole
  structure, as the pipeline does;
- **per thread:** for each thread, on the structure restricted to that
  thread's events and the events outside every thread (Init, before the block,
  after it); the union of these;
- **join-aware:** for each top-level thread, on the structure restricted to it,
  the threads nested in it (found through `po`: sibling threads are not
  po-related) and the events outside every thread, keeping the justifications
  of that fragment's thread events; and the justifications of events outside
  every thread taken at the top, where everything is joined.

They are compared justification by justification, on a rendering independent
of hash-table order. Where they differ, the rest of the pipeline is run from
each set and the verdict and canonical execution set compared, as the golden
gate renders them.

| | programs | justifications |
|---|--:|--:|
| tracked `.lit` files | 404 | |
| single-threaded | 86 | |
| multi-threaded | 318 | 7,405 |
| per thread = whole | 315 | |
| per thread ≠ whole | 3 | 26 missing, 30 extra |
| **join-aware = whole** | **318** | **7,405** |

The three that differ:

| program | missing | extra | from | executions (whole / per thread) | join-aware |
|---|--:|--:|---|---|---|
| `own/join-continuation` | 10 | 18 | Forwarding (and Value Assignment on top) | 12 / 0 | same justifications, same 12 executions, same verdict |
| `jmm/jctc/JCTC19` | 8 | 6 | Forwarding (and Value Assignment) | 19 / 0 | same |
| `jmm/jctc/JCTC20` | 8 | 6 | Forwarding (and Value Assignment) | 19 / 0 | same |

Every differing justification is of a write after a join. In
join-continuation it is `y := r1`, after the block. In JCTC19 and JCTC20 it is
`y := r1` in the outer thread, after the inner block it forked. Whole, its
forwarding contexts combine edges from both threads, e.g. `(1,5)` from one and
`(2,3)` from the other: both forwardings are `ppo`-before the write once the
join orders the threads before it. Per thread, its contexts hold one thread's
edges, and no justification combination is consistent. The verdicts happen to
agree only because no execution was found either way that would change them.

## Answers

1. **Paper check:** the elaborations are stated over `ppo`, conflict and `Ω`.
   They reach other threads only through fork and join, and `Ω` is global but
   constant. They compose over fragments closed under fork and join.
2. **Per thread against whole:** equal on 315 of 318 multi-threaded programs.
   Not equal on 3, all with code after a join, all through Forwarding.
   Join-aware fragments are equal on all 318, with the same executions and
   verdicts where it matters.
3. **Diverging operator:** Forwarding, and Value Assignment through it. It does
   not have to stay global. It has to see every thread a join brings together.
4. **Decision for Phase 2b:** fully local justifications, computed per
   fragment, with one rule: a fragment after a join (a parallel block's
   continuation) is elaborated over the merged block, not over any one thread.
   The globally-computed, fragment-indexed fallback is not needed.
