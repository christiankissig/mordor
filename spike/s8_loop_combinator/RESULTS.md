# S8: a regression net for symbolic loops (#20)

**Verdict: `po_iter` can be produced compositionally, and the regression net is
in place.** A loop occurrence that adds the pairs of its own body's events to
its own structure's `po_iter` produces a subset of what symbolic loop semantics
rebuilds at the end from `loop_indices`, never more. What it leaves out are
exactly pairs between events in conflict: copies of one loop that
interpretation made in the two branches of an earlier choice, which no
execution contains together. Episodicity gives the same results with either,
on all 34 loop programs. The `loop_indices` reconstruction need not be a
permanent fallback.

The characterization goldens (`test/goldens-loops/`, 34 programs) catch what
the main golden gate cannot. Breaking the do-while peeling changes 23 of them,
while `golden_diff check` stays 333/333 green.

## 1. Characterization goldens

`test/golden/loop_goldens.ml`, run from the repo root:

    dune exec test/golden/loop_goldens.exe -- check
    dune exec test/golden/loop_goldens.exe -- update FILE ...

For every tracked program with a loop (34: 23 under `programs/`, and 11 litmus
tests, JCTC14 and JCTC15 among them), it renders the structure symbolic loop
semantics builds: each event's type, `po`, `po_iter`, `conflict`, `restrict`, `loop_indices` and
`loop_conditions`, each sorted. It compares the rendering with a committed
golden. A set of more than 5000 elements is kept as its size and an MD5 digest,
which takes rcu-3's golden from 6.9 MB to 212 KB. `check` walks the committed
goldens, not the program directories, which also hold local programs outside
the repository. It takes 18s and is deterministic: two runs, same result.

The main golden gate compares executions under the default loop semantics,
which unrolls loops. It is blind to all of this. The check that shows it:

| mutation | `golden_diff check` | `loop_goldens check` |
|---|--:|--:|
| do-while's peeled first unravelling keeps its loop membership | 333 pass, 0 fail | 11 pass, **23 fail** |

## 2. The loop producing its own `po_iter`

`po_iter` says that every event of a loop's symbolic iteration is po-before
every other, across iterations. Today it is not built by the structure. It is
rebuilt once interpretation is done (`generate_po_iter`): all events stamped
with a loop's index, paired with each other. That is a whole-program pass, and
the one piece of loop semantics a bottom-up construction could not do fragment
by fragment.

Behind `MORDOR_S8_COMPOSITIONAL_PO_ITER`, each interpreted occurrence of a
while loop (a do-while's residual loop included) instead adds the pairs of its
own body to the structure of its entering branch: the events of that structure
whose `loop_indices` contain the loop. The combinators carry `po_iter` from
operand to result (`dot` keeps it, `plus`/`cross` union it; both used to reset
it to empty, which nothing noticed because nothing set it before the end).
R8's relabelling of threads carries it along too.

`spike/s8_loop_combinator/`, over the 34 loop programs:

| program | rebuilt | compositional | missing | missing, in conflict | extra |
|---|--:|--:|--:|--:|--:|
| rcu-3 | 2,556 | 216 | 2,340 | 2,340 | 0 |
| episodicity/hp-1 | 1,722 | 840 | 882 | 882 | 0 |
| cas_aba | 504 | 210 | 294 | 294 | 0 |
| rcu-1 | 78 | 72 | 6 | 6 | 0 |
| the other 30 | equal | | 0 | | 0 |

Every pair the compositional relation leaves out relates two conflicting
events, and by construction it joins two different occurrences of the same
loop: one loop interpreted once in each branch of a choice before it. The
index-based rebuild pairs the occurrences because they share the loop's index.
Some pairs are the same source event twice: all of rcu-3's and rcu-1's, 90 of
cas_aba's 294 and 130 of hp-1's 882.

`mordor episodicity` gives the same results either way, on all 34: the same
verdict per loop, the same violated conditions, the same bisections (29
finish; rcu-3 times out at 300s both ways; 4 are refused by their model both
ways). Only the diagnostic dumps differ, which print the structure before `po_iter`
is filled in.

## 3. The loop combinator's contract

What a loop combinator has to do, read off the classic construction and held
to by the goldens above. For `while (c) { body }; rest` at loop index `l`:

1. **Shape.** A branch event on `c` evaluated where the loop is reached,
   followed by `choice enter exit`. A constant guard drops the branch and the
   impossible side. `enter` is the body followed by the continuation, `exit`
   the continuation alone. Each side has its own copy of the continuation,
   since `choice` puts everything in one operand in conflict with everything
   in the other.
2. **Membership.** Every event of the body, including those of loops nested in
   it, has `l` in its `loop_indices`. The continuation's events do not. In
   `do { body } while (c)` the first unravelling of `body` is not an iteration
   and carries only the enclosing loops' indices.
3. **Iteration order.** `enter`'s `po_iter` gains `cross(B, B) \ id` for the
   body's events `B`. The combinators union `po_iter`, and relabelling maps it.
4. **Guards.** Each path through the body records, for loop `l`, the guard `c`
   evaluated in the environment reached at the end of that path and conjoined
   with that path's condition. These accumulate in `loop_conditions`, one per
   path per occurrence.

Composing `body` and `rest` as two separate fragments, rather than passing
`rest` to the body as its continuation as the classic interpreter does, was not
prototyped. The continuation of each path through the body runs in that path's
environment. So a separate `rest` fragment has to be parameterised by the
registers it reads and instantiated per path, which is S2's (#15) footprint
substitution and Phase 1c's machinery, not the loop's. Point 3 is what the loop
itself has to contribute, and it does not depend on that split.

## Answers

1. **Characterization goldens:** committed for every tracked loop program (34),
   with a check that catches a loop regression the main gate misses.
2. **Loop-as-combinator prototype:** the loop produces its own `po_iter`
   (point 3 above), diffed against the classic rebuild on all 34 programs. The
   contract is above.
3. **Can `po_iter` be produced compositionally?** Yes. It differs from the
   rebuild only by pairs of conflicting events, and episodicity's results do
   not change. `loop_indices` reconstruction need not stay as a fallback. The
   flag stays in `interpret.ml`, off by default. Making it the default is a
   behaviour change to `po_iter` itself, which drops the conflicting pairs, and
   is left for a decision.
