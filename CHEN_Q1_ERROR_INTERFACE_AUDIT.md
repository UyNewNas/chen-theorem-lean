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
collection of individual AP errors.  In schematic notation, for the actual
Chen ranges of `q`, `d`, and `e`, it must bound the signed/repackaged remainder

```text
sum_{q in Q_N} | sum_{d|P_N} mu(d) sum_{e|F_N} mu(e)
  [pi(N-2; lcm(q,d,e), N) - M_N(q,d,e)] |
  <<_A N/log^A N,                                             (Q1-2D)
```

after (and only after) the source theorem has specified the admissible level
of the lcm modulus and any necessary coprimality or exceptional-even-modulus
terms. `M_N` must use the genuine `Li(N-2)` main term on odd moduli and the
verified exact term on even moduli.

This is a Chen-local `DimensionTwoSwitchingRemainder` target. Its eventual
formal API should expose: the three finite index sets, the modulus map, the
main-term convention, a uniform threshold before `N`, and the exact final
weight. It should not conceal these data behind a generic pointwise BV name.
