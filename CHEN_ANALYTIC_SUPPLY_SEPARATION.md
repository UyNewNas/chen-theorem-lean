# Chen analytic supplies: lower sieve versus the `Omega` upper bound

## Decision

The corrected Chen proof has two analytically different consumers. They must
remain separate in the theorem map and in repository interfaces.

```text
lower candidate count W      -> a = 1 prime AP errors -> weighted BV at one;
bad-count penalty Omega      -> variable a = p1 p2    -> bilinear/dimension-two sieve.
```

The first line becomes much smaller after the compact-support and genuine-`Li`
repairs. The second does not. Calling both of them a single "Pan input" hides
the essential difference and gives a false impression of progress.

## 1. Lower candidate-count workline

The lower sieve for `correctedChenCandidates` has prime support ending at
`N-2`. After the required repairs its error splits into

```text
d = 1:                         |pi(N-2) - Li(N-2)|;
2 <= d <= D, d | P_N:          3^omega(d)|pi(N-2;d,N)-Li(N-2)/phi(d)|;
finite correction:             signed MainB.
```

This line consumes:

1. ANT's medium-PNT-to-`pi-Li` theorem for `d=1`;
2. the `a=1` specialization of the Pan weighted mean-value theorem for
   `d>=2`; and
3. compact Jurkat--Richert coefficients at level `D`, with the **logarithmic**
   sieve parameter `log D/log z`.

The detailed source match is ANT's
[`A1_WEIGHTED_BV_SOURCE_MATCH.md`](https://github.com/UyNewNas/analytic-number-theory-lean/blob/dev/A1_WEIGHTED_BV_SOURCE_MATCH.md).
The lower-sieve coefficient support, `Li` normalization, and sieve-ratio
audits are ANT issues #66 and #68.

## 2. `Omega` upper-bound workline

`correctedChenOmega` is split in the repository into a prime-power part and a
triple-factor part. The triple part is bounded through sums of

```text
switchingCount(N, a),  where a = p1*p2
```

and then through the prime-pair linear-form count

```text
#{p3 : p3 prime, N-a*p3 prime}.
```

Here `a` genuinely varies over a two-prime range. The `a=1` theorem has no
route to this assertion. The documented required supply is instead:

```text
uniform in 1 <= a and 2a <= N,
PrimePairLinearFormCount(N,a)
  << (a/phi(a)) * (N/a)/(log(N/a)*log N),                     (U)
```

or the stronger `N/(phi(a) log^2 N)` form. `PrimePairLinearForm.lean`
correctly decomposes this into three still-open ingredients:

| ingredient | role | status |
| --- | --- | --- |
| `LinearFormPairDistributionCondition` | average distribution of `n(N-a n)` | open analytic supply |
| `LinearFormPairDimensionTwoSieveBound` | dimension-two Selberg/linear upper sieve | open analytic supply |
| `LinearFormPairLocalDensityBound` | Mertens/singular-series local main term | source-matched target; proof work remains |

The q-power component has a distinct AP-error/main-term decomposition
(`q1APErrorUniformBound`, `q1MainTermAbsorption`). Its base prime count is
an `a=1` AP count, but its double Möbius expansion and even-modulus correction
must be audited independently before importing the lower-sieve `a=1` result.

## 3. Consequences for the current interfaces

`ChenWeightedPanInput` is a lower-candidate error input. It is consumed in
the final positivity theorem together with, but does not prove,
`CorrectedChenOmegaUpperBound`.

Therefore this implication is invalid:

```text
a=1 weighted BV  => CorrectedChenOmegaUpperBound.
```

The valid dependency graph is

```text
ANT medium PNT --[proven source, API pending]--> d=1 pi-Li
Pan Theorem 2 --[source theorem]---------------> lower a=1 AP errors
JR supported coefficients --[source match]-----> lower sieve main/error shape
signed MainB --[written finite proof]----------> lower remainder correction
                                                    |
                                                    v
                                             candidate lower bound

bilinear prime-pair distribution --[open]-----> triple-factor Omega bound
dimension-two upper sieve ---------[open]-----> /
local-density main term -----------[open]----->/
q-power AP decomposition ----------[open]------> prime-power Omega bound
                                                    |
                                                    v
                                             Omega upper bound
                                                    |
candidate lower bound --------------------------> final Chen positivity.
```

## 4. Workline stop conditions

- Do not use the old generic `PanMeanValueUniform` principal-part chain to
  discharge the lower `a=1` consumer; its generic main-term inequality has
  already been shown to have the wrong shape.
- Do not use the `a=1` lower-sieve theorem to justify a variable-`a`
  prime-pair estimate.
- Do not state a numerical `3.9404` `Omega` bound for the corrected penalty
  merely because the historical Chen proof has that constant. The current
  corrected `Omega` is a new consumer; its exact analytic estimates and
  numerical margin must be derived for its own definitions.
- Do not attach either workline to a distribution theorem using `x/log x` as
  an arbitrary-log-saving main term.

This separation is the current mathematical map: it names the supplies that
are reusable ANT infrastructure and the ones that are irreducibly Chen-local.
