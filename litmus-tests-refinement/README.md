# Refinement litmus tests

These files are **refinement chains**, not `allow`/`forbid` predicates. The
format is two whole programs separated by a `~~>` header:

```
<source program>
%% ~~> [_=forbid] %%
<target program>
```

The question is whether the target refines the source — whether every behaviour
of the target is a behaviour of the source. `[_=allow]` asserts that it does,
`[_=forbid]` that it does not. `[UB11=allow]` names the model the chain is read
under, and that model governs the whole chain.

Moved out of the scanned suite in `f467724` ("shelfing refinement litmus tests"),
which records no reason, and held here while refinement checking was a stub
(#85).

## Five have returned to the suite

With #85 fixed, `avoidoota/listing7.lit`, `avoidoota/listing8.lit` and the
`symmrd/refinement/` triple decide correctly and live in `litmus-tests/` again:

| File | Asserts | Refinement | Why |
|---|---|---|---|
| `avoidoota/listing7.lit` | forbid | does not hold | the target invents a write (`x := 3`) |
| `avoidoota/listing8.lit` | forbid | does not hold | same shape |
| `symmrd/refinement/LB+UB+data.lit` | allow (`UB11`) | holds | under `UB11` the `e / !r -> e` fold makes the two programs agree |
| `symmrd/refinement/LB+UB+data+z.lit` | allow (`UB11`) | holds | same, with the extra `z` hop |
| `symmrd/refinement/LB+UBoff+data.lit` | forbid | does not hold | the UB fold off, so the target's `r1 = 1` outcome is genuinely new |

The `UB11` pair is what forced a second fix alongside #85: `step_parse_litmus`
applies the model of an `Outcome` or a `Model` assertion but never a `Chained`
one, so a chain's model annotation had never reached the options and `ubopt`
stayed false.

## What is left — #87

`avoidoota/listing9.lit` is the pointer-publication idiom: the source loads the
published pointer once and reads both fields through it, the target re-loads
between them and can mix a field of the old object with one of the new. The
refinement genuinely does not hold, which is what the file asserts, but MoRDor
reports **undecided** rather than deciding it:

```
Refinement: execution 16 still admits new observations after 512; at least one
  of [ra; rb] is unconstrained, so its behaviour cannot be enumerated
```

`rglob` is initialised to 0, so `rfp` may be null and `*(rfp + 0)` is a load
through a null pointer whose result nothing constrains. See #87.
