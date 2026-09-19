# S12: how many threads, and how much work, for rcu-2?

**Verdict: about 16 threads, and rcu-2 is not within reach of any machine as it
stands.** The pipeline plateaus at 15-16 threads at about 4.4 times one thread.
Its serial share, about 13%, caps it near 8 times however many cores it gets.
Knuth's tree-size estimate puts rcu-2's read-from search, at step counter 2, at
around 10^10 CPU-seconds and about 2 x 10^8 executions. At step counter 1 no
combination finished in 20 minutes either.

Measured on an i7-13700H laptop: 6 performance cores (12 threads) and 8
efficiency cores, 20 threads in all, 62GB.

## Scaling

A fixed slice of rcu-2's futures (`--step-counter-per-loop 2`): every 30th
justification combination (`MORDOR_S10_COMBO_STRIDE=30`, 146 of 4,374), each
enumerated until 5 executions (`MORDOR_S12_FREEZE_CAP=5`) or 500 extension
steps (`MORDOR_S12_STEP_CAP=500`). Stage times from `--progress`.

| threads | wall | elaborate | prepare | freeze |
|--:|--:|--:|--:|--:|
| 1 | 969s | 676s | 57s | 231s |
| 2 | 587s (1.65x) | 412s | 36s | 137s |
| 4 | 355s (2.73x) | 242s | 23s | 88s |
| 6 | 291s (3.33x) | 196s | 18s | 74s |
| 8 | 254s (3.82x) | 169s | 18s | 65s |
| 12 | 224s (4.33x) | 142s | 18s | 63s |
| 16 | 220s (4.41x) | 135s | 20s | 62s |
| 20 | 256s (3.79x) | 165s | 27s | 62s |

Fitted to the Universal Scalability Law, C(N) = N / (1 + s(N-1) + kN(N-1)):

| | s (serial) | k (contention) | peak | peak speedup | 32 threads | 64 threads |
|---|--:|--:|--:|--:|--:|--:|
| wall | 0.128 | 0.0039 | N = 15 | 4.2x | 3.6x | 2.6x |
| elaborate | 0.117 | 0.0031 | N = 17 | 4.6x | 4.2x | 3.1x |
| freeze | 0.160 | 0.0036 | N = 15 | 3.8x | 3.4x | 2.5x |
| prepare | 0.104 | 0.0143 | N = 8 | 3.2x | 1.7x | 1.0x |

Even with no contention, s = 0.13 limits the speedup to 1/s, about 8x. On a
server with uniform cores and no turbo, k may be smaller than on this laptop,
but s is the code's.

**Not the garbage collector.** At 8 threads, a 64MB minor heap per domain
(`OCAMLRUNPARAM=s=8M`) cut minor collections from 182,012 to 5,626 and left
the time where it was (227s against 239s). The run allocates 272 billion words,
about 2.2TB, in under four minutes: memory traffic and the locks on the solver
and forwarding caches are the likelier limits.

## Work

`MORDOR_S13_PROBES=k` makes freeze estimate, instead of enumerate, each
combination's read-from search by Knuth's method: k random descents, each
multiplying the number of writes that pass every check at each read. Same 146
combinations, 20 probes each, 16 threads, 15.7 minutes:

| per combination | median | mean | max |
|---|--:|--:|--:|
| search nodes passing every check | 9.1e6 | 2.1e7 | 2.1e8 |
| valid executions | 0 | 4.9e4 | 5.6e6 |

A probe step, checking every write for one read, cost 0.16s on average; the
depth-first search does the same at every node it expands. So a median
combination is about 1.5 million CPU-seconds, and rcu-2's 2,916 kinds of
combination on the order of 10^10: hundreds of CPU-years. Only 8 of 2,920
probes reached a valid execution, so the execution count, about 2 x 10^8
scaled to all combinations, is rough; checking those for coherence at 0.4s
each would be several CPU-years more, and holding them terabytes.

**Step counter 1** (`--step-counter-per-loop 1`, 16 threads, plain pipeline):
interpretation and elaboration take 3.6s (84 justifications), 384 combinations
(256 kinds), and in 20 minutes freezing found 95,943 executions and finished
none of the 256.
