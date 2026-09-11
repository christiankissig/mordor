# Java Causality Test Cases (reference only)

`jctc/` holds MoRDor's transcriptions of [William Pugh, *Java Causality Test
Cases*, 2004](https://www.cs.umd.edu/~pugh/java/memoryModel/CausalityTestCases.html),
the test battery that accompanies [JSR-133](https://www.cs.umd.edu/~pugh/java/memoryModel/jsr133.pdf),
Manson and Pugh's Java Memory Model. Each file's assertion message quotes Pugh's
decision for that test.

There are 24 files:
- the twenty tests on Pugh's page;
- `JCTC8b` and `JCTC9b`, variants of tests 8 and 9 that were added to MoRDor
  alongside the rest in its first litmus commit, `8aa5b1a`, and do not appear on
  Pugh's page;
- `JCTC17-left` and `JCTC17-smaller`, two cut-down probes from investigating
  JCTC17. Neither has an assertion, so both used to pass the suite vacuously.

## Why they live here and not in the test suite

**Pugh's decisions are judgments under the Java Memory Model, which MoRDor does
not implement.** `ModelRegistry` in `src/coherence.ml` registers `imm`, `rc11`,
`rc11c`, `smrd` and `undefined`, and `JMM` is in neither the registry nor
`model_options_table`. So the `[JMM]` annotation these files carry is a hard
error:

```
$ mordor run --single jctc/JCTC1.lit
Error: Unknown memory model "jmm". MoRDor implements imm, rc11, rc11c and smrd,
and maps a further set of names onto those; this one is in neither, so no
coherence model can be applied. Re-run with --allow-unknown-model to check the
test under the model already in effect instead -- the verdict is then that
model's, not "jmm"'s.
```

That is intentional. Until the move the files were annotated `[]`, so they ran
under the `smrd` default. A JMM expectation was being answered by sMRD without
anything saying so, and wherever the two happened to agree the test simply
passed.

The table below uses `--allow-unknown-model` to run each file under sMRD. What it
reports is sMRD's answer, which is a different question from the one the file
asks.

## No source gives sMRD's own verdict on these tests

[Symbolic MRD (Richards, Wright, Cooksey, Batty, OOPSLA
2025)](https://graymalk.in/papers/oopsla25.pdf), §3.1:

> Symbolic MRDer evaluates a suite of 173 litmus tests, drawn from literature
> discussing the specification of C/C++ [34] and Java [31] ... Each test probes
> one memory behaviour, **specifying the expectation for C++ in its assertion**.

> Symbolic MRDer provides the desired behaviour in all test cases, **except where
> open questions of thread inlining and optimisations using global analysis leave
> the desired behaviour ambiguous**.

So an sMRD test would carry the C++ expectation, not Pugh's. The paper works
through only one of these tests itself: JCTC12, as Example 2.4, in a pointer
encoding. Its 173-test suite shipped with a browser tool, and no published copy
has been found.

[P2850R0, *Minimal Compiler Preserved Dependencies*](https://graymalk.in/iso-papers/p2850/p2850r0.html)
(Batty and Cooksey, 2023) is the nearest thing. Its §4 gives a C++ verdict for
each JCTC test. It is not an sMRD source, though:

- **It is a draft.** It is revision 0 of a proposal to SG1 that says it "poses
  questions to WG21 members", and its JCTC18 section ends "Does SG1 agree?".
- **It is about a different relation.** It argues about `sdep`, which
  [P1780](https://graymalk.in/iso-papers/p1780/p1780r2.html) would add to the C++
  standard as an *implementation-defined* relation, under the rule
  `acyclic(sdep ∪ rf)`. Symbolic MRD's rule is `acyclic(dp ∪ ≤ ∪ rf)`.

For tests 1–13, P2850R0's verdicts are the same as Pugh's.

## Three assertions contradict the decision they quote

Three files assert `forbid` while their message quotes Pugh's "Allowed":

- **`JCTC8`** asserts `forbid (r1 = 1 && r2 = 1)` and has done since `8aa5b1a`.
  `JCTC8b` rewrites the program slightly and asserts `allow` of
  `r1 = 1 && r3 = 1`.
- **`JCTC9`** asserts `forbid (r1 = 1 && r3 = 1)`, also since `8aa5b1a`.
  `JCTC9b` is **the same program with the opposite assertion**, so under any
  one model at most one of the pair can pass.
- **`JCTC16`** asserted `allow` until `96b40eb` ("improve rendering in web ui:
  node labels, node shapes, hiearchical view"), which flipped it to `forbid`.
  That looks accidental.

sMRD forbids all three outcomes. So all three files pass, while sMRD's answer
differs from Pugh's. The `⚠` marks them in the table below.

## Where sMRD and Pugh differ

Measured with `--allow-unknown-model`:

| Test | Issue | Pugh | sMRD fallback | Note |
|---|---|---|---|---|
| `JCTC2` | #50 | allow | forbids | Pugh: "redundant read elimination" |
| `JCTC3` | #52 | allow | forbids | same reasoning as test 2 |
| `JCTC6` | #36 | allow | forbids | needs the fact that `B` only ever holds 0 or 1 |
| `JCTC8` | — | allow | forbids | hidden: the file asserts `forbid` |
| `JCTC9`, `JCTC9b` | #53 | allow | forbids | JCTC9's `forbid` hides it; JCTC9b's `allow` shows it |
| `JCTC12` | #48 | forbid | allows | see below |
| `JCTC16` | — | allow | forbids | hidden: `96b40eb` flipped the assertion |
| `JCTC18` | — | allow | forbids | see below |
| `JCTC19`, `JCTC20` | #49, #51 | allow | forbids | see below |

**JCTC12.** The sMRD paper forbids this test in its pointer encoding, and so
does MoRDor's `litmus-tests/own/JCTC12.lit`, which is in the scanned suite and
passes. The file here is Pugh's original, which reaches the same shape through
per-index globals and a chain of `if`s on `r1`, and MoRDor allows that one.
P2850R0 §4.12 prints exactly this encoding and forbids it, but as a draft C++
requirement rather than an sMRD verdict.

**JCTC18.** This test agreed with Pugh until `839d0c6` (#43), and still differs
after `ae177d0` replaced that fix. The current reason: value assignment now
concretises only values the context entails. Before, `ValueAssignElab` read a
write's value straight out of one solver model, which let it rewrite `r1 = x` to
`r1 = 42` even though nothing forced 42. That rewrite is exactly what Pugh's
justification relies on: "a compiler could determine that the only legal values
for x are 0 and 42". Without it the `allow` loses its witness. P2850R0 §2.6
proposes allowing the optimisation and leaves it as an open question to SG1.
JCTC17, whose justification needs no such step, still agrees.

**JCTC19 and JCTC20.** In Pugh's programs thread 1 joins thread 3 before reading
`x`, and runs at the same time as thread 2. The files now encode exactly that:
thread 3 is a parallel block inside thread 1's branch, and thread 1's body
follows it. This gives 15 events and 19 executions, with no witness for the
`allow`. Two earlier encodings got the join wrong in opposite directions:
- The original had thread 1 wait for thread 2 as well.
- `31e57c9` made all three threads concurrent, which dropped the join.

P2850R0 skips both tests because they probe "thread joining".

## The JMM is not a safe target even for Java

Ševčík and Aspinall, [*On Validity of Program Transformations in the Java Memory
Model*](https://link.springer.com/chapter/10.1007/978-3-540-70592-5_3) (ECOOP
2008), showed that common subexpression elimination can introduce new behaviours
under the JMM, so the model invalidates transformations it was written to allow.
"The JMM allows it" is therefore not, on its own, a reason to expect sMRD to allow
it.

## All files

The last column is what sMRD decides about the outcome in the assertion, run with
`--allow-unknown-model`. `⚠` marks an assertion that contradicts Pugh's decision.

| Test | File asserts | Pugh (JMM) | P2850R0 draft (C++ `sdep`) | sMRD fallback decides the outcome |
|---|---|---|---|---|
| `JCTC1` | allow | allow | allow | allows |
| `JCTC2` | allow | allow | allow | forbids |
| `JCTC3` | allow | allow | allow | forbids |
| `JCTC4` | forbid | forbid | forbid | forbids |
| `JCTC5` | forbid | forbid | forbid | forbids |
| `JCTC6` | allow | allow | allow | forbids |
| `JCTC7` | allow | allow | allow | allows |
| `JCTC8` | forbid ⚠ | allow | allow | forbids |
| `JCTC8b` | allow | allow (as JCTC8) | allow (as JCTC8) | allows |
| `JCTC9` | forbid ⚠ | allow | allow | forbids |
| `JCTC9b` | allow | allow (as JCTC9) | allow (as JCTC9) | forbids |
| `JCTC10` | forbid | forbid | forbid | forbids |
| `JCTC11` | allow | allow | allow | allows |
| `JCTC12` | forbid | forbid | forbid | allows |
| `JCTC13` | forbid | forbid | forbid | forbids |
| `JCTC14` | forbid | forbid | skipped (loops) | forbids |
| `JCTC15` | forbid | forbid | skipped (Java coherence) | forbids |
| `JCTC16` | forbid ⚠ | allow | skipped (Java coherence) | forbids |
| `JCTC17` | allow | allow | skipped (Java coherence) | allows |
| `JCTC17-left` | no assertion | — | — | — |
| `JCTC17-smaller` | no assertion | — | — | — |
| `JCTC18` | allow | allow | open question to SG1; proposes allow | forbids |
| `JCTC19` | allow | allow | skipped (thread joining) | forbids |
| `JCTC20` | allow | allow | skipped (thread joining) | forbids |
