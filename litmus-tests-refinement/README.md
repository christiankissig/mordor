# Refinement litmus tests (reference only)

These six files are **refinement chains**, not `allow`/`forbid` predicates. The
format is two whole programs separated by a `~~>` header:

```
<source program>
%% ~~> [_=forbid] %%
<target program>
```

The question is whether the target refines the source — whether every behaviour
of the target is a behaviour of the source. `[_=allow]` asserts that it does,
`[_=forbid]` that it does not. `[UB11=allow]` names the model the chain is read
under.

Moved out of the scanned suite in `f467724` ("shelfing refinement litmus tests"),
which records no reason.

## Why they are still here — #85

**MoRDor does not decide these assertions.** `Refinement.do_check_refinement`
(`src/assertion.ml:949`) compares an empty placeholder result against itself
rather than the two programs, so `refinement_holds` is unconditionally `true` and
the reported verdict reduces to `outcome = Allow`. Every `allow` chain reports
`Valid: true`; every `forbid` chain reports `Valid: false`. The programs are
never looked at.

Measured at `c91c19a`:

| File | Asserts | Reports | Decided? |
|---|---|---|---|
| `symmrd/refinement/LB+UB+data.lit` | `[UB11=allow]` | `Valid: true` | no |
| `symmrd/refinement/LB+UB+data+z.lit` | `[UB11=allow]` | `Valid: true` | no |
| `symmrd/refinement/LB+UBoff+data.lit` | `[_=forbid]` | `Valid: false` | no |
| `avoidoota/listing7.lit` | `[_=forbid]` | `Valid: false` | no |
| `avoidoota/listing8.lit` | `[_=forbid]` | `Valid: false` | no |
| `avoidoota/listing9.lit` | `[_=forbid]` | `Valid: false` | no |

The two `true` rows are the trap: they would go green in the integration suite
without anything being checked. That is the same vacuous-pass shape as #41, #44
and #45, and the reason none of these six can be returned to `litmus-tests/`
until #85 is fixed.

`litmus-tests-cpp/properties/global-transformations/thread-inlining/{src,opt}.lit`
is a refinement pair as well, so #85 blocks it independently of the missing C++
model.

## The programs

`avoidoota/listing7.lit` and `listing8.lit` are the same shape: a target that
invents a write (`x := 3` where the source has none), asserted `forbid` because
write introduction is not a refinement. `listing9.lit` is the pointer-publication
shape, where the target re-loads the published pointer between the two field
reads; the `TEMP FIX` comments record where `&global` had to be replaced by an
explicit `malloc`.

The `symmrd/refinement/` triple is load-buffering with a division by `!r1`, so
`r1 = 0` is undefined behaviour. The target replaces `y := 1 / !r1` with `y := 1`,
which is a refinement exactly when the UB assumption may be exploited: allowed
under `[UB11]`, forbidden with the UB fold off (`LB+UBoff+data.lit`). See #65 for
the related question of propagating UB assumptions into later uses.
