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
