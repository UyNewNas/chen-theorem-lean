# q1 AP-error interface audit

## Status

This is a written audit of the q1/prime-power branch of the corrected Chen
`Omega` bound. It does not prove `q1APErrorUniformBound` and it does not
license its current source attribution.

## Findings

The current q1 definitions introduce three independent obligations.

1. For odd `m`, `q1APMainValue(N,m)` uses the ANT working expression
   `N/log N / phi(m)`. Any arbitrary-log-saving error relative to this term
   is false already for `m=1`; it must be migrated to the matching genuine
   `Li(N-2)/phi(m)` endpoint. The even-modulus exact correction remains valid
   in principle but must be checked against the migrated endpoint convention.
2. `q1CandidateAPError` takes absolute values after expanding both the
   sifting and forbidden products:
   ```text
   sum_q sum_{d|P} sum_{e|F} |mu(d)mu(e)|
     |err(lcm(q,d,e))|.
   ```
   This is not the `a=1` weighted BV sum. Its moduli can exceed the supplied
   level, and taking absolute values removes the signed cancellation before
   a distribution theorem is applied.
3. Therefore the comment claiming that generic `PanMeanValueUniform` directly
   supplies `q1APErrorUniformBound` is not a source match. A theorem must
   first be stated for the exact surviving signed/repackaged object, with a
   proved modulus cutoff.

## Why there is no MainB-style automatic cancellation

For fixed `q`, the signed expression is the inclusion--exclusion expansion of
two genuine coprimality filters.  Writing `R(m)` for `q1APError(N,m)`, it is

```text
sum_{d|P} mu(d) sum_{e|F} mu(e) R(lcm(q,d,e)).                 (1)
```

Unlike the MainB base-count term, `R(m)` is not a constant function of `m`
and has no divisor-sum identity that turns (1) into a cardinality.  Reversing
the sums simply reconstructs the original doubly sifted AP count; it does not
make the distribution error disappear.  Hence a MainB-style finite Möbius
cancellation is unavailable here without an additional analytic identity.

The source-faithful object is consequently a **dimension-two (or switching)
sieve remainder** for the pair of coprimality conditions, with its own level
and averaged distribution theorem.  It may be bounded after a source theorem
repackages the lcm multiplicities, but not by asserting a pointwise bound on
every term of (1).

## Consequence

The valid lower-sieve `a=1` route controls a compact sum of ordinary AP errors
only after coefficient support and MainB cancellation. It cannot be imported
unchanged into q1. q1 belongs to the variable-`a`/`Omega` workline (Chen #50).

## Required repair order

1. migrate `q1APMainValue` to genuine `Li(N-2)` and reprove its exact even
   modulus identity;
2. retain the signed double Möbius expression long enough to identify actual
   cancellation, or prove a new source theorem for its absolute form;
3. establish the exact level of every surviving `lcm(q,d,e)` modulus;
4. only then formulate a q1 distribution input and connect it to a cited
   Pan/BV theorem.

Stop condition: no theorem or documentation may claim q1 error control from
the `a=1` lower-sieve `WeightedBVAtOne` interface while the displayed
absolute lcm sum remains its consumer.

## Minimal replacement target

The next theorem must be stated for the **sifted pair**, rather than for a
collection of individual AP errors.  There is one further prerequisite which
the displayed legacy interface cannot hide: the exact identity in
`q1CandidateAPCount_eq_doubleSum` uses *all* divisors of
`P_sift(N)` and `F_forb(N)`.  Thus its raw modulus

```text
m(q,d,e) = lcm(q,d,e)
```

has no useful uniform level bound: a divisor of either full prime product can
be far larger than any Bombieri--Vinogradov level.  Squarefreeness does not
repair this.  Consequently even a theorem controlling the signed expression
below cannot be an ordinary AP theorem until the full-divisor identity has
been replaced by source-matched **sieve weights with explicit support**, plus
an independently bounded sieve remainder.

Write

```text
Q_N = {q prime : z(N) <= q < y(N)},
P_N = correctedChenSiftingProduct(N),
F_N = correctedChenForbiddenProduct(N),
R_N(m) = q1APBaseCount(N,m) - M_N(m).
```

Here `M_N(m)` is the exact even-modulus contribution when `m` is even and
the genuine endpoint `Li(N-2)/phi(m)` when `m` is odd.  The finite algebra
already proved in Lean identifies the legacy signed remainder as

```text
B_N(q) = sum_{d|P_N} mu(d) sum_{e|F_N} mu(e) R_N(lcm(q,d,e)).   (2)
```

It is legitimate as an identity, but it is **not** a distribution-theorem
input.  A source-matched replacement must introduce weights `lambda_N(d)`
and `rho_N(e)` (or a single combined switched weight) satisfying a stated
support condition such as

```text
lambda_N(d) != 0 and rho_N(e) != 0  =>  lcm(q,d,e) <= L(N)
```

for every surviving `q in Q_N`, together with a separately stated error for
replacing the coprimality indicators by those weights.  The exact form of
`L(N)`, the weights, and that replacement error must be copied from the
chosen Chen/Pan source; they cannot be inferred from the present raw Möbius
identity.

Only after that step may the new theorem bound the signed/repackaged remainder

```text
sum_{q in Q_N} | sum_{d,e} lambda_N(d) rho_N(e)
  R_N(lcm(q,d,e)) |
  <<_A N/log^A N,                                             (Q1-2D)
```

after (and only after) the source theorem has specified the admissible level,
the coprimality hypotheses, the exceptional-even-modulus terms, and the
sieve-weight replacement error.  A one-sided signed bound is enough for the
Chen upper bound, while the displayed absolute-in-`q` version is a stronger
and easier-to-audit target; the source must say which one it supplies.

This is a Chen-local `DimensionTwoSwitchingRemainder` target. Its eventual
formal API should expose: the three finite index sets, the supported weights,
the modulus map and proved level cutoff, the sieve-weight replacement error,
the main-term convention, a uniform threshold before `N`, and the exact final
weight. It should not conceal these data behind a generic pointwise BV name.

## Formalization boundary

The existing theorems through `q1CandidateAPCount_eq_doubleSum` are valuable
finite identities and should remain available as such.  They must not be used
as the consumer of `DimensionTwoSwitchingRemainder`.  The next Lean object is
therefore a new, explicitly supported switched/sieved count, followed by a
lemma comparing it with `correctedChenQ1Count`; only that new object may
consume the analytic remainder theorem.  This preserves the audited finite
algebra while making the analytic seam mathematically real.
