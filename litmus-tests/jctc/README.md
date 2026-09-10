# Java Causality Test Cases

Vendored from [William Pugh, *Java Causality Test Cases*,
2004](https://www.cs.umd.edu/~pugh/java/memoryModel/CausalityTestCases.html), the
test battery accompanying [JSR-133](https://www.cs.umd.edu/~pugh/java/memoryModel/jsr133.pdf)
(Manson and Pugh's Java Memory Model). Each file's assertion message is that
page's own justification, quoted.

## What the verdicts mean here

**Pugh's verdicts are judgments under the Java Memory Model.** These files are
annotated `[]` — no model — so they run under the `smrd` default. That is legal,
but it means a JMM expectation is being decided by sMRD, and the two are not the
same model.

The model MoRDor implements says as much. [Symbolic MRD (Richards, Wright,
Cooksey, Batty, OOPSLA 2025)](https://graymalk.in/papers/oopsla25.pdf), §3.1:

> Symbolic MRDer evaluates a suite of 173 litmus tests, drawn from literature
> discussing the specification of C/C++ [34] and Java [31] ... Each test probes
> one memory behaviour, **specifying the expectation for C++ in its assertion**.

> Symbolic MRDer provides the desired behaviour in all test cases, **except where
> open questions of thread inlining and optimisations using global analysis leave
> the desired behaviour ambiguous**.

So the assertion a JCTC file should carry is the C++ expectation, which for the
tests whose JMM verdict rests on an optimisation need not be Pugh's.

## Which are here, and which are parked

Fifteen are in this directory and pass. The rest are in
`litmus-tests-review/jctc/`, and the split follows the carve-out above rather
than being a list of defects:

| Test | Issue | JMM justification for its `allow` | Falls under |
|---|---|---|---|
| `JCTC2` | #50 | "redundant read elimination could result in simplification of `r1 == r2` to true" | optimisation using global analysis |
| `JCTC3` | #52 | same reasoning as test case 2 | optimisation using global analysis |
| `JCTC6` | #36 | "Intrathread analysis could determine that thread 2 always writes 1 to A and hoist the write" | optimisation using global analysis |
| `JCTC9b` | #53 | "a compiler might determine that the read ..." | optimisation using global analysis |
| `JCTC19` | #49 | "the same as test case 17, except that thread 1 has been **split into two threads**" | thread inlining |
| `JCTC20` | #51 | "the same as test case 18, except that thread 1 has been **split into two threads**" | thread inlining |

Six for six, which is why they carry `smrd-unsupported` and not `bug`.

`JCTC12` (#48) is the exception and does carry `bug`. It is **Example 2.4 of the
sMRD paper** — the worked pointer-aliasing example — where both the aliasing
execution and the strengthened one are said to be *forbidden by the model*, by
`acyclic(dp ∪ ≤ ∪ rf)`. MoRDor allows it, so that one is a defect measured
against the paper's own worked example.

## The JMM is not a safe target even for Java

Ševčík and Aspinall, [*On Validity of Program Transformations in the Java Memory
Model*](https://link.springer.com/chapter/10.1007/978-3-540-70592-5_3) (ECOOP
2008), showed that common subexpression elimination can introduce new behaviours
under the JMM — the model invalidates transformations it was written to allow.
"The JMM allows it" is therefore not on its own a reason to expect sMRD to.
