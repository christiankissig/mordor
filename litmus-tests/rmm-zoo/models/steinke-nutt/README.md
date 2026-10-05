# The distributed consistency models

Local, Slow, PRAM, Causal and PC (Steinke and Nutt, JPDC 2004), per-object
causal consistency (POCausal, Burckhardt et al., POPL 2014), and the session
guarantees RYW, MR, MW and WFR (Terry et al., PDIS 1994, in Viotti and
Vukolić's form, ACM CSUR 2016) are stated over *histories*: each process's
sequence of operations with the values they read and wrote, with visibility and
arbitration existentially quantified. MoRDor decides them on its own candidate
executions instead. This file states that encoding, justifies it, and records
how it was checked.

## The encoding

| Definition says | MoRDor reads it as | Why that is the same thing |
|---|---|---|
| process | thread | A process is a sequential stream of operations with its own view; a thread is that. |
| a read returns the value of a write | a read reads one write, by `rf` | Every `rf` is enumerated, so a read of value `v` is matched against every write of `v` in turn. With the values a litmus test writes, each store unique per location, this is exactly value matching. |
| the initial value | the initialising stores, before every thread | `x := 0` before a parallel block is `po`-before every thread's events, and every view and arbitration puts it first, so reading it means seeing no other write, as reading the initial value does. |
| a view (Steinke–Nutt): a legal serialisation of all writes and the process's own operations | the same, found by search (`Coherence.Views`) | The definitions verbatim; the search is exhaustive and memoised on the events placed and the latest write per location. |
| Causal's causality order | `(po ∪ rf)⁺` | Ahamad et al.'s causal order is program order with writes-into, which is `rf`. |
| PC's common order of each location's writes | the candidate `co` | Goodman's PC is PRAM with one write order per location agreed by every view: that is a coherence order, and MoRDor's search enumerates them. |
| POCausal's visibility and arbitration | least visibility `rf`, arbitration `co` | Every axiom is weakest under least visibility, so taking it least decides existence; arbitration only matters per object, which `co` is. |
| session guarantees over one arbitration | one arbitration per reader (`Coherence.Sessions`) | A deliberate reading: with one order, RYW forbids two threads each reading the other's write after writing their own, which PRAM allows, and the zoo's edge from PRAM to RYW would fail. |
| RMWs | not atomic | Histories have none. |

Visibility is taken *least* throughout: the guarantees only constrain what a
read may see more of, so the least visibility closed under them is the one
under which an outcome is most allowed.

## The oracle

`test/oracles/distributed_models.py` decides every one of these models from its
definition over the history, independently of MoRDor: values instead of `rf`,
the initial values as a pre-state instead of stores, and views, visibility and
arbitration found by its own search. It agrees with every verdict the tests
here and in `../sessions/` assert (80 of them):

```
python3 test/oracles/distributed_models.py litmus-tests/rmm-zoo/models/steinke-nutt/*.lit litmus-tests/rmm-zoo/models/sessions/*.lit
```

`test/oracles/compare_with_mordor.py` goes further: random straight-line
programs of two or three threads over two locations, every outcome, all ten
models, MoRDor against the oracle.

```
python3 test/oracles/compare_with_mordor.py SEED COUNT SCRATCH_DIR
```

Two batteries were run when the oracle was written: seed 1 with 40 programs
(2,890 verdicts, 464 disagreements) and a second of 60 programs (4,930
verdicts, 766 disagreements). Every disagreement is an outcome the definitions
allow and MoRDor forbids, and every one is an outcome MoRDor's candidate
executions cannot express:

- **own-future-read**: a read takes a value only a later store of its own
  thread writes;
- **skips-own-store**: a read does not see its own thread's latest earlier
  store to the location;
- **same-location load buffering**: reads and stores to one location form a
  cycle through program order and reads-from.

sMRD's preserved program order keeps same-location accesses in order, so its
candidates never have these shapes, under any model. No disagreement runs the
other way, and none is unexplained: within the executions MoRDor generates,
its encoding and the definitions agree.

That is the remaining limit of these models in MoRDor, and it is not theirs:
they are very weak, weaker than sMRD's candidate space on a single location, so
MoRDor answers *forbid* for outcomes they allow but sMRD cannot produce. Local,
Slow, PRAM, MR, MW, WFR and RYW are affected; Causal, PC and POCausal never
were in the batteries run.
