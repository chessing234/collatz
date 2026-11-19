# Optimal excursion-error charges

This development refines the repository's existing conditional excursion
budget. It is **not a proof of the Collatz conjecture**. The rounding argument
is elementary; mathematical priority has not been assessed.

## The charge and its exact scope of optimality

For an odd run of length `v`, its affine contribution, divided by its
homogeneous coefficient, is

\[
1-\left(\frac23\right)^v.
\]

At integer scale `s`, define

\[
c_s(v)=s-\left\lfloor\frac{s2^v}{3^v}\right\rfloor.
\]

`Collatz.ExcursionCharge.charge_le_iff` proves, for every natural `s,v,c`,

\[
c_s(v)\le c
\quad\Longleftrightarrow\quad
s(3^v-2^v)\le c3^v.
\]

Thus this is the **least valid integer charge at a fixed scale**. This does
not assert optimality among all possible orbit-dependent error estimates.
Zero scale and zero-length runs are included in the arithmetic theorem;
the descent theorem requires positive scale and a genuine excursion trace.

At scale nine the charges at lengths `0,1,2,3,4,5,6` are
`0,3,5,7,8,8,9`. The previous `ninths` charge was `0,3,5,9,9,9,9`.
The new charge is never larger than the old one.

## Refinement, exactness, and a limitation

The kernel-checked refinement law is

\[
c_{ms}(v)\le m c_s(v).
\]

It extends to the sum of charges on a finite trace and preserves every
previously valid weighted budget. Here refinement means multiplying the
scale by an integer. Merely taking a larger scale does not suffice:
`c_3(1)/3 = 1/3`, whereas `c_4(1)/4 = 1/2`.

For `v <= S`, the ternary scale `s=3^S` removes rounding completely:

\[
c_{3^S}(v)=3^S-2^v3^{S-v},\qquad
c_{3^S}(v)3^v=3^S(3^v-2^v).
\]

Consequently every finite collection of run lengths admits a common exact
scale: choose `S` at least every length. This observation does not remove
the separate overestimate from replacing individual prefix multipliers
by a single bound.

A fixed scale cannot retain a strict discount at all lengths. Lean proves
both the exact saturation criterion and an explicit saturating length:

\[
c_s(v)=s\quad\Longleftrightarrow\quad s2^v<3^v,
\qquad c_s(2s)=s.
\]

## Conditional descent

Let a genuine excursion trace start at `n>0` and end at `e`. Write `A` for
its total odd-run length, `T` for its total accelerated duration, and
`W_s` for the sum of its optimal charges. If

1. every proper prefix with totals `a,t` satisfies `d 2^t <= p 3^a`;
2. the endpoint satisfies the strict crossing `p 3^A < d 2^T`;
3. `s>0` and `d s n + p W_s <= p s n`;

then `drop_of_crossing` proves `e<n`. There is no fixed bound on the number
of excursions. This theorem reuses the existing `ExcursionBudget`
affine telescope; its contribution is optimal integer charging and its
precision laws, not a new telescope identity.

The first-half specialization uses `(p,d,s)=(2,1,9)` and budget
`2 W_9 <= 9 n`.

## Strict improvement on a genuine trace

Lean constructs the trace `7 -> 13 -> 5`, whose run pairs `(v,W)` in
chronological order are `(3,1),(1,2)`. At `(p,d,s)=(6,5,9)`:

- all proper-prefix coefficient bounds hold;
- `6*3^4 < 5*2^7`;
- optimal total charge is `7+3=10`, and `5*9*7+6*10 <= 6*9*7`;
- old total charge is `9+3=12`, and its budget fails.

`seven_drop_from_budget` invokes the general descent theorem on this trace.
The improvement is at the **same trace, threshold, and scale**. This does
not claim that the source was previously unproved, or that no other old
choice of parameters could certify it.

## Verification

```sh
lake build Collatz.Strategy.ExcursionCharge
python3 -I scripts/audit_excursion_charge.py
```

The arithmetic layer is `ExcursionChargeCore.lean`; the trace application is
`ExcursionCharge.lean`. `ExcursionData.lean` isolates the unchanged excursion
predicate and an elementary proof of its orbit endpoint, avoiding unrelated
finite-search dependencies. `ExcursionMap` re-exports the same predicate and
endpoint theorem. The existing budget also needed a reserved binder renamed
and an affine rewrite made explicit before it compiled on the pinned Lean.

The audit independently checks ceiling minimality, refinement, exact ternary
charges, saturation, and actual finite traces. It inspects every theorem's
transitive axiom footprint and requires deliberately false statements to
fail in Lean. It accepts only the standard logical axioms `propext`,
`Classical.choice`, and `Quot.sound`; it does not accept `sorryAx` or a new
mathematical axiom.

The targeted build and audit passed. The audit checked 20,289 minimality
comparisons, 64,233 refinements, 496 exact ternary charges, 5,042 saturation
cases, and 49,564 valid finite trace certificates. One sampled certificate
passed the optimal budget but failed the old one at the same threshold.
All 32 public theorem footprints across the charge core, charge application,
excursion data, and inherited budget were checked; all five false controls
were rejected. The full repository build was not run.

Neither the finite audit nor the formal conditional theorem proves that
every positive input eventually has a suitable crossing and budget.
That universal obligation remains open.
