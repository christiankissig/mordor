# Java Causality Test Cases (reference only)

Vendored from [William Pugh, *Java Causality Test Cases*,
2004](https://www.cs.umd.edu/~pugh/java/memoryModel/CausalityTestCases.html), the
test battery accompanying [JSR-133](https://www.cs.umd.edu/~pugh/java/memoryModel/jsr133.pdf)
(Manson and Pugh's Java Memory Model). Each file's assertion message is that
page's own justification, quoted.

## Why they live here and not in the test suite

**Pugh's verdicts are judgments under the Java Memory Model, and MoRDor does not
implement it.** `ModelRegistry` in `src/coherence.ml` registers `imm`, `rc11`,
`rc11c`, `smrd` and `undefined`; `JMM` appears in neither it nor
`model_options_table`, so the annotation these files now carry is a hard error:

```
$ mordor run --single jctc/JCTC1.lit
Error: Unknown memory model "jmm". MoRDor implements imm, rc11, rc11c and smrd,
and maps a further set of names onto those; this one is in neither, so no
coherence model can be applied. Re-run with --allow-unknown-model to check the
test under the model already in effect instead -- the verdict is then that
model's, not "jmm"'s.
```

That is the point. Until this move the files were annotated `[]`, so they ran
under the `smrd` default and a JMM expectation was being answered by sMRD --
quietly, and for fifteen of them the two happened to agree, which is what made
the other seven look like defects.

The `sMRD fallback` column below is measured by passing `--allow-unknown-model`.
It answers a different question from the one the file asks.

## The model MoRDor implements says the two need not agree

[Symbolic MRD (Richards, Wright, Cooksey, Batty, OOPSLA
2025)](https://graymalk.in/papers/oopsla25.pdf), §3.1:

> Symbolic MRDer evaluates a suite of 173 litmus tests, drawn from literature
> discussing the specification of C/C++ [34] and Java [31] ... Each test probes
> one memory behaviour, **specifying the expectation for C++ in its assertion**.

> Symbolic MRDer provides the desired behaviour in all test cases, **except where
> open questions of thread inlining and optimisations using global analysis leave
> the desired behaviour ambiguous**.

So the assertion a JCTC file should carry, to be a test of *this* model, is the
C++ expectation -- which for the tests whose JMM verdict rests on an optimisation
need not be Pugh's. Deriving those is the work these files are parked pending.

## Where sMRD and the JMM part company

Six tests, and the paper's carve-out accounts for all six:

| Test | Issue | JMM justification for its `allow` | Falls under |
|---|---|---|---|
| `JCTC2` | #50 | "redundant read elimination could result in simplification of `r1 == r2` to true" | optimisation using global analysis |
| `JCTC3` | #52 | same reasoning as test case 2 | optimisation using global analysis |
| `JCTC6` | #36 | "Intrathread analysis could determine that thread 2 always writes 1 to A and hoist the write" | optimisation using global analysis |
| `JCTC9b` | #53 | "a compiler might determine that the read ..." | optimisation using global analysis |
| `JCTC19` | #49 | "the same as test case 17, except that thread 1 has been **split into two threads**" | thread inlining |
| `JCTC20` | #51 | "the same as test case 18, except that thread 1 has been **split into two threads**" | thread inlining |

`JCTC12` (#48) is the seventh. The sMRD paper works this test through as its
**Example 2.4**, the pointer-aliasing example, and says both the aliasing
execution and the strengthened one are *forbidden by the model*, by
`acyclic(dp ∪ ≤ ∪ rf)`.

That is not lost by this move. The paper's version is the **pointer** encoding,
and MoRDor already has it as `litmus-tests/own/JCTC12.lit` -- `rp := malloc(2)`,
`*(rp + r1) := 0`, `r2 := *rp` -- which is in the scanned suite and **passes**:
12 executions, the `forbid` holds. So sMRD's own worked example is under test and
agrees with the paper.

What is parked here is Pugh's original encoding, which reaches the same shape
through per-index globals and a chain of `if`s on `r1` rather than through a
pointer. MoRDor allows that one. Whether the two encodings should agree is the
open question on #48, and it is a question about elaboration on branches, not
about the JMM.

## The JMM is not a safe target even for Java

Ševčík and Aspinall, [*On Validity of Program Transformations in the Java Memory
Model*](https://link.springer.com/chapter/10.1007/978-3-540-70592-5_3) (ECOOP
2008), showed that common subexpression elimination can introduce new behaviours
under the JMM -- the model invalidates transformations it was written to allow.
"The JMM allows it" is therefore not on its own a reason to expect sMRD to.

## Files

Twenty-four files: the twenty numbered cases, `JCTC8b` and `JCTC9b` (the
lettered variants on the page), and two fragments.

`JCTC17-left.lit` and `JCTC17-smaller.lit` carry **no assertion at all** -- they
are cut-down probes written while investigating JCTC17's upclosure, not test
cases with a verdict. They were passing the suite vacuously, since a file with no
assertion is valid by default.

Reference verdicts are Pugh's; the `sMRD fallback` column is what MoRDor reports
through `--allow-unknown-model`, measured at `2761ec5`.

| Test | Asserts | JMM | sMRD fallback |
|---|---|---|---|
| `JCTC1` | allow | allow | allows ✓ |
| `JCTC2` | allow | allow | **forbids** ✗ |
| `JCTC3` | allow | allow | **forbids** ✗ |
| `JCTC4` | forbid | forbid | forbids ✓ |
| `JCTC5` | forbid | forbid | forbids ✓ |
| `JCTC6` | allow | allow | **forbids** ✗ |
| `JCTC7` | allow | allow | allows ✓ |
| `JCTC8`, `JCTC8b` | allow | allow | allows ✓ |
| `JCTC9` | allow | allow | allows ✓ |
| `JCTC9b` | allow | allow | **forbids** ✗ |
| `JCTC10` | forbid | forbid | forbids ✓ |
| `JCTC11` | allow | allow | allows ✓ |
| `JCTC12` | forbid | forbid | **allows** ✗ |
| `JCTC13`, `JCTC14`, `JCTC15` | forbid | forbid | forbids ✓ |
| `JCTC16` | allow | allow | allows ✓ |
| `JCTC17`, `JCTC18` | allow | allow | allows ✓ |
| `JCTC19`, `JCTC20` | allow | allow | **forbids** ✗ |
