# Chen sieve main-term normalization audit

## Finding

The corrected Chen sieve currently sets

```text
correctedChenBoundingSieve(N).totalMass = N/log N
```

and defines its remainder against that first-order approximation.  This is
incompatible with the arbitrary-log-saving `errSum` targets consumed later in
the Chen chain.  The defect is inherited from ANT's working definition
`logarithmicIntegral(x) = x/log x`; it is not repaired by the Medium PNT.

This document specializes the ANT normalization audit (issue #68 / PR #67)
to the Chen consumer.  It is a paper counterexample audit, not a Lean claim.

## 1. The d=1 obstruction in the current Chen error sum

At divisor `d=1`, the corrected Chen remainder is the prime-support count
minus `N/log N`.  Its support count is the primes `p≤N-2`, so, up to the
harmless endpoint convention,

```text
rem_N(1) = pi(N-2) - N/log N.                                 (1)
```

The genuine logarithmic integral satisfies

```text
pi(x) = Li(x) + o(x/log^A x)  for every fixed A,
Li(x) = x/log x + x/log^2 x + O(x/log^3 x).
```

Putting `x=N-2` in (1) therefore gives

```text
rem_N(1) = N/log^2 N · (1+o(1)).                              (2)
```

The difference between `N/log N` and `(N-2)/log(N-2)` is only `O(1/log N)`;
it cannot cancel the term in (2).  Hence the nonnegative d=1 summand in
`errSum(1)`, in `CorrectedChenDistributionCondition`, and in any supported
lower-sieve sequence with `μ⁻(1)=1` is eventually at least a constant times
`N/log²N`.

Taking target exponent `A=3` proves that the present arbitrary-`A` error
budget is false under this normalization.

## 2. Why compact support alone is not enough

The compact-support repair removes the artificial large-divisor tail and the
false absolute-value `lcm(d,e)` expansion.  It does not remove `d=1`: a
standard lower-sieve coefficient has `μ⁻(1)=1`, and the modulus-one term is
part of its supported error.

Thus the correct dependency order is

```text
genuine Li normalization
        +
compactly supported lower coefficients
        +
signed forbidden-divisor cancellation
        +
a=1 Pan/BV for 2≤d≤D
        |
        v
valid Chen error budget.
```

Skipping the first node recreates a deterministic `N/log²N` error even if
every distribution theorem is otherwise perfect.

## 3. Required semantic migration

The source-faithful Chen object should use the same genuine main term as the
distribution theorem.  With the current endpoint convention the natural
choice is

```text
totalMass_N = Li(N-2),
rem_N(d) = count_N(d) - nu(d) · Li(N-2).
```

The following existing chains then require a deliberate migration audit:

1. `correctedChenBoundingSieve` and all identities exposing its `rem`;
2. `supportAPBaseCount_distributionError` and the Pan bridge;
3. `CorrectedChenDistributionCondition` / `ChenWeightedPanInput`;
4. the lower-sieve main-term estimates and Mertens/singular-series assembly;
5. the signed MainA identity, now with the exact endpoint difference of
   genuine `Li` rather than the working quotient;
6. every numeric positivity comparison that currently treats `N/log N` as an
   exact mass.

The familiar `N/log N` formula may remain as a coarse asymptotic consequence
for main-term lower bounds.  It must not be the definition against which an
arbitrary-log-saving remainder is measured.

## 4. Exact cancellation gained by the migration

The normalization repair is not merely defensive.  It removes an artificial
MainA term from the truncation identity.  With

```text
totalMass_N = Li(N-2),
Delta_N(d) = base_N(d) - Li(N-2)/phi(d),
```

the e=1 term in the finite Möbius expansion of `rem_N(d)` is exactly
`base_N(d)`, while the subtracted distribution error contains the same
`base_N(d)-Li(N-2)/phi(d)`.  Hence for every `d|P_N`,

```text
rem_N(d) - Delta_N(d)
 = sum_{1!=e|F_N} mu(e) base_N(lcm(d,e)).                      (3)
```

There is no residual

```text
[li(N-2)-li(N)]/phi(d)
```

because both sides use the same genuine endpoint.  The signed finite
Möbius identity then controls (3) by the previously audited MainB argument.
Thus the migration replaces

```text
working-main-term mismatch + MainA + MainB
```

by

```text
exactly matched Li main term + MainB.
```

This is a structural simplification, not a new analytic assumption.

## 5. Stop condition and acceptance

Do not attempt to prove `ChenWeightedPanInput`, a truncation input, or a
supported d=1 PNT facade at arbitrary exponent while their error definitions
use `x/log x`.  The asymptotic (2) is a direct contradiction.

The normalization workline is ready for formalization only after ANT exports
a genuine `Li` API and an explicit `pi-Li` error, and after Chen's total mass,
remainder, and distribution bridges use the same function.  Only then can the
compact-support transport in `CHEN_COMPACT_SUPPORT_TRANSPORT.md` be attached
to a Pan/BV theorem.
