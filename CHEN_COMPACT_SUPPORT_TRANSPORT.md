# Chen transport for compact lower-sieve coefficients

## Status

This document is the written specification for Chen issue #48.  It consumes
the generic ANT specification in issue #66 / PR #67 and maps it to the
corrected Chen sieve.  It makes no Lean-certification claim.

Its purpose is narrow: replace the current use of the broad all-divisor
`errSum(1)` by the error sum of a compactly supported lower-sieve coefficient
sequence.  This removes the false `lcm(d,e)` truncation input at the level
where it was created.

## 1. Current Chen seam

For

```text
S_N = correctedChenBoundingSieve(N),
P_N = correctedChenSiftingProduct(N),
Δ_N(d) = panDistributionError(N-2;1,d,N mod d),
w(d) = 3^ω(d),
D(N,B) = floor(sqrt(N)/(log N)^B),
```

the finite lower-sieve inequality fundamentally needs

```text
S_N.totalMass · S_N.mainSum(μ⁻) - S_N.errSum(μ⁻) ≤ S_N.siftedSum.  (1)
```

This is already available generically in ANT.  The current Chen consumers
instead use `S_N.errSum(1)`, then try to control all divisor moduli through
`correctedChenPanSum_reduction` and `CorrectedChenPanTruncationInput`.

That broad detour has two defects already documented in the companion audit:

1. the intermediate `ChenPanTruncationSieveBound` is false (`d=1,e=2`);
2. its tail is created only because the support of `μ⁻` was discarded before
   applying the distribution input.

The repair is to retain `μ⁻` from (1) through the error estimate.

## 2. Required Chen-side coefficient contract

For each sufficiently large even `N`, the lower-sieve source must provide a
coefficient function `μ⁻_N` and a fixed logarithmic parameter `B` such that

```text
IsLowerMoebius(μ⁻_N),
|μ⁻_N(d)| ≤ 1,
μ⁻_N(d) ≠ 0 and d | P_N  =>  d ≤ D(N,B),                      (S)
```

together with the uniform Jurkat--Richert main-term inequality.  The support
condition is a property of the selected lower-sieve coefficients, not of
every divisor of `P_N`.

From `(S)`, the exact finite error becomes

```text
S_N.errSum(μ⁻_N)
 = Σ_{d|P_N, d≤D(N,B)} |μ⁻_N(d)| |S_N.rem(d)|.                 (2)
```

This equality, and the corresponding supported lower-bound theorem, are the
first formal artifacts required from ANT #66.  Chen must not replace its
right side by `S_N.errSum(1)`.

## 3. Error decomposition without the false lcm input

For every `d|P_N`, the existing finite identity is

```text
S_N.rem(d) - Δ_N(d)
 = [li(N-2)-li(N)]/φ(d)
   + Σ_{1≠e|F_N} μ(e) base_N(lcm(d,e)).                         (3)
```

The entire signed `e`-sum in (3) has already been evaluated algebraically as
a negative cardinality.  The written MainA/MainB proof therefore gives, for
every prescribed `A>0`, the bound

```text
Σ_{d|P_N} w(d) |S_N.rem(d)-Δ_N(d)| <<_A N/(log N)^A.            (4)
```

Since `|μ⁻_N(d)|≤1≤w(d)`, (4) also controls its supported sub-sum.  This is
where the forbidden-divisor expansion ends.  In particular, no subsequent
step may form `|Δ_N(lcm(d,e))|` term by term.

After the genuine-`Li` migration, the endpoint used in `S_N.totalMass` and in
`Δ_N` is the same `Li(N-2)`.  The displayed `[li(N-2)-li(N)]/phi(d)` term is
then absent identically: the e=1 base count and the exact same Li main term
cancel.  Only the signed MainB correction remains, so the old MainA estimate
becomes unnecessary rather than another analytic input.

Using the triangle inequality only after (3) has been collapsed, (2) gives

```text
S_N.errSum(μ⁻_N)
 ≤ Σ_{d|P_N,d≤D} |μ⁻_N(d)| |Δ_N(d)|
   + O_A(N/(log N)^A).                                         (5)
```

## 4. Consumption by Pan/BV and PNT

Split the first sum in (5) at `d=1`.

### The nontrivial moduli

For `2≤d≤D(N,B)` with `d|P_N`, the existing finite coprimality bridge proves
that `N mod d` is coprime to `d`.  Hence

```text
|μ⁻_N(d)| |Δ_N(d)| ≤ w(d) · panMaxY(N,d,N,chenPanWeightOne).
```

Summing these terms is exactly within the a=1 weighted Pan/BV modulus range.
The necessary analytic input is a **specific a=1** mean-value theorem with
the `w(d)=3^ω(d)` weight and an arbitrary prescribed logarithmic saving.
The current generic ANT `PanMeanValueUniform` must be checked against this
specific specialization; a generic theorem for arbitrary bounded weights is
not silently interchangeable with the Chen delta-at-one weight.

### The modulus one term

For `d=1`, after the genuine-`Li` normalization repair,

```text
Δ_N(1) = π(N-2)-Li(N-2).
```

It is outside the coprime-residue Pan maximum and must be bounded by a
quantitative PNT consequence.  The ANT medium-strength PNT chain is the
natural supply line after its partial-summation transfer is exported.  The
current working main term `x/log x` cannot be used here: its deterministic
`x/log²x` discrepancy is audited in
`CHEN_MAIN_TERM_NORMALIZATION_AUDIT.md`.

Combining these two supplies with (4) proves the small error required by the
supported lower-sieve positivity argument, with no all-divisor tail.

## 5. Required replacement path

The intended dependency graph is

```text
ANT compact lower coefficients + supported main term       [open supply]
                         |
                         v
ANT finite supported-error lower sieve                      [finite proof]
                         |
                         v
Chen identity (3) + signed MainA/MainB                      [paper-proved]
                         |
             +-----------+-----------+
             |                       |
             v                       v
a=1 weighted Pan/BV, 2≤d≤D       quantitative PNT, d=1      [open supplies]
             |                       |
             +-----------+-----------+
                         |
                         v
supported Chen errSum and lower-bound positivity             [target]
```

The old route

```text
all-divisor errSum(1) -> lcm(d,e) absolute errors -> truncation tail
```

is rejected.  Its first analytic node is exactly the refuted proposition.

## 6. Formalization gates

No code should be added merely to make the old conditional chain type-check.
Before formalization, verify all of the following:

1. ANT exports a compact-support lower-sieve theorem whose error term is
   `errSum(μ⁻)`, not `errSum(1)`.
2. The Chen main-term lower bound consumes that theorem without a second
   all-divisor relaxation.
3. The signed correction estimate (4) is formalized or otherwise supplied
   with its stated Mertens dependency.
4. The exact a=1 Pan/BV statement and its `d=1` PNT companion have matching
   constants, cutoff, and quantifier order.
5. The final audit contains no assumption equivalent to the refuted
   `ChenPanTruncationSieveBound`.

Until these gates are met, Chen remains conditional.  This is an accurate
description of the current mathematics, not a failure of Lean verification.
