# RGSep under Release/Acquire Consistency

The litmus programs of Ellen Arlt and Viktor Vafeiadis, *RGSep under
Release/Acquire Consistency*, PACMPL 10 (OOPSLA2), Article 375, 2026,
doi:[10.1145/3839507](https://doi.org/10.1145/3839507). The paper proves the
RGSep logic sound under release-acquire (RA) and unsound under weak RA (WRA) and
strong coherence (SCOH); these are the programs it reasons about.

| test | section | RA (paper) | asserted besides |
|---|---|---|---|
| `IRIW.lit` | 1 | allows | SC, TSO forbid; SRA, WRA, Coherence, RC11 allow |
| `CohRR.lit` | 3 | forbids `b < a` | every model forbids |
| `CohRR+rlx.lit` | (3) | — | relaxed: RA, SRA, WRA allow; SC, TSO, Coherence, RC11 forbid |
| `MP.lit` | 3 | forbids | Coherence allows |
| `MP+rlx.lit` | 3 | — | relaxed: RC11 allows, as the paper states |
| `MP-repeat.lit` | 3 | forbids | the paper's spin loop; SC, RA, RC11, PS1, PS2 forbid |
| `MP-par-MP.lit` | 3 | forbids | Coherence allows |
| `Coh.lit` | 3 | forbids | WRA allows |
| `Coh+rlx.lit` | (3) | — | WRA allows; RC11 and Coherence forbid, contrary to the paper |
| `OT.lit` | 5.2 | forbids | Coherence allows |

Every program is written with release writes and acquire reads, as the paper's
RA treats every access; the `+rlx` variants make them relaxed. Each test asserts
the paper's RA verdict and the verdicts of herd7 7.58 on the C translation in
`herd/`, under the rmm-zoo's `abstract-sc`, `abstract-tso`, `ra`, `sra`, `wra`
and `abstract-coherence` cat models and herd's `rc11.cat`. MoRDor agrees with
herd7 on all 63 of those verdicts. `MP-repeat.lit` has a loop, which herd7's C
front end cannot run; it asserts MP's verdicts, since its loop exits on `y = 1`
only.

```sh
for m in abstract-sc abstract-tso ra sra wra abstract-coherence; do
  herd7 -model <rmm-zoo-dataset>/litmus/models/$m.cat herd/Coh.litmus
done
herd7 -model rc11.cat herd/Coh.litmus
```

**Where the paper and the models part.** Section 3 says Coh's weak outcome
(Thread 1 reads 2, Thread 2 reads 1) "is possible under the relaxed fragment of
the C++ memory model and under the slightly stronger strong coherence model
(SCOH)". herd7's `rc11.cat` and MoRDor's RC11 and Coherence forbid it with
relaxed accesses: reading 2 after writing 1 orders `W x 1` before `W x 2` in
coherence order, and reading 1 after writing 2 orders them the other way. WRA,
which has no coherence order, allows it, and so is a witness for the paper's
claim that RGSep is unsound under WRA. The paper names no program for that.

Not checked: the paper's remark that CohRR's assertion fails under the Java
memory model. MoRDor does not implement the JMM, and JAM keeps plain accesses
coherent.
