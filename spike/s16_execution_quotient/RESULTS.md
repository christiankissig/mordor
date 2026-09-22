# S16: how far executions collapse under a quotient (#93)

**Verdict: an execution is already about as coarse as a key that keeps the
future can make it.** Over the corpus, 18,891 executions fall into 18,839
classes once the future and the final registers are both kept: read-from
choices within a combination almost always change what the registers end up
holding, so there are no inert choices for a meta execution to hide. Keys that
drop the future collapse more — 4,586 final states (registers and memory) over
the corpus, about 4× — but the future is what the primary goal needs. On rcu-2
the final states are symbolic (allocation addresses and some read values are
free symbols), so a syntactic quotient cannot test "one final memory state":
1,074 distinct states among 1,120 sampled executions. R14 (#100) should key a
class by its future, which is exact, small and cheap (one per justification
combination, S14), and list a representative execution per future.

Run from the repo root (off by default):

    MORDOR_S16=1 dune exec mordor -- futures --single FILE --allow-unknown-model

    # rcu-2, executions supplied by S19's solver, 5 per combination:
    MORDOR_S19=1 MORDOR_S19_WITNESSES=5 MORDOR_S16=1 MORDOR_S16_SHOW=1 \
      dune exec mordor -- futures --threads 3 --step-counter-per-loop 1 \
      --single programs/rcu-2.lit

`MORDOR_S16=1` makes the futures stage count the classes the final executions
fall into under successively finer keys; `MORDOR_S16_SHOW=1` also prints each
final state with its count. `corpus_output.tsv` and `rcu2_sc1_output.txt` are
the runs reported here; `analyze.py` tabulates the first.

## The keys

| key | an execution's class is fixed by |
|---|---|
| future | its events, and `dp ∪ ppo` restricted to them (`Futures.calculate_future_set`) |
| outcome | its final registers and final memory, without the future |
| + registers | the future, and each register's final value, resolved through the execution's read values |
| + memory | and each location's co-last write's value |
| + reads | and the value every read observes |
| + UB | and its use-after-free and unsequenced-race pairs, as the assertion stage finds them |

Values are resolved through `fix_rf_map`, the same substitution the assertion
stage uses, and compared as printed.

## The corpus: 375 programs, every execution

The 333 golden programs plus litmus-tests-cpp and -jmm, run with
`--allow-unknown-model`.

| key | classes |
|---|--:|
| executions | 18,891 |
| future | 8,814 |
| outcome | 4,586 |
| future + registers | 18,839 |
| + memory | 18,839 |
| + reads | 18,843 |
| + UB | 18,843 |

- In 112 programs the future alone already separates every execution.
- In 263 programs the final state adds classes beyond the future; the value
  read adds classes beyond future and final state in one.
- The largest group of executions sharing one future is 343 (3.2W).

| program | executions | futures | outcomes | future + registers |
|---|--:|--:|--:|--:|
| 3.2W | 3,375 | 27 | 343 | 3,375 |
| jctc/JCTC11 | 1,447 | 778 | 189 | 1,447 |
| avoidoota/listing15 | 1,083 | 675 | 160 | 1,083 |
| avoidoota/additional_nonlb | 701 | 409 | 199 | 701 |
| jctc/JCTC5 | 592 | 338 | 93 | 592 |

Within a future, executions differ in their read-from; a different write read
is, in these programs, almost always a different value read, and so a
different register. The hypothesis that most read-from choices are inert —
different ordered sets of events and outcomes being rare — does not hold for
the observable state: once the future is fixed, nearly every read-from choice
is a different outcome.

## rcu-2, step counter 1

rcu-2 cannot be enumerated (S13), so its executions here are S19's: up to 5
distinct read-from relations per justification combination, each found by the
solver and checked exactly (validity and smrd coherence). They are witnesses,
not a uniform sample.

| | |
|---|--:|
| combinations with a coherent execution | 224 of 256 |
| executions (5 per combination) | 1,120 |
| futures | **224 — one per combination** |
| outcomes | 1,074 |
| future + registers / + memory / + reads | 1,087 / 1,112 / 1,120 |
| executions with a use-after-free | 1,013 |
| executions with no undefined behaviour | 107 |

The final states are symbolic. A typical final memory:

    (一 + 1)=0, (三 + 1)=1, (五 + 1)=v((一 + 1)), (八 + 1)=0, 一=0,
    七=(Δ + 1), 三=七, 二=四, 五=0, 八=1, 四=((Ε + 1) + 1)

The CJK symbols are allocation addresses and the Greek ones values read that no
write pins. Two states that are equal as numbers can print differently, so
1,074 is an upper bound on the distinct outcomes, and "one final memory state"
is neither confirmed nor refuted here. Deciding it needs the solver to compare
symbolic states under each execution's predicates — the syntactic-vs-semantic
comparison S9 flagged as risk R2.

The use-after-free count is what the assertion stage finds in these witnesses
at step counter 1. One iteration also truncates the grace-period polling loops
in `sync`, which may be what admits them; that is not established here.

## What this means for R14

- **Key a class by its future.** That is exact (S14), small (at most one per
  justification combination; 224 on rcu-2 at step counter 1), and it is what
  the futures goal computes anyway.
- **List a representative per future, and more on demand.** S19 produces a
  checked witness per combination in a fraction of a second, and further
  distinct ones by blocking each and asking again; that is how the 1,120 above
  were produced.
- **Do not build a quotient that hides read-from choices within a future.**
  Over the corpus there is nothing to hide: 18,891 executions, 18,839 classes.
- **An outcome-level view** (final registers and memory, across futures) does
  collapse executions, about 4× on the corpus, and would suit assertion-style
  questions. On rcu-2 it needs semantic comparison to mean anything.
