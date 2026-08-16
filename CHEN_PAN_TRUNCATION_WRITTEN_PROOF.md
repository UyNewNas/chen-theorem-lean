# Chen Pan truncation: written proof audit

## Status and scope

This is a mathematical proof document, not a Lean certification claim.  It
audits the two terms in `ChenPanTruncationMainTermBound` and isolates the
separate distributional statement `ChenPanTruncationSieveBound`.

Let `N` tend to infinity through even natural numbers.  Write

```text
P(N) = correctedChenSiftingProduct(N),
F(N) = correctedChenForbiddenProduct(N),
ω(n) = number of distinct prime factors of n,
li(x) = x / log x.
```

The working `li` is the repository's asymptotic main-term normalization; it
is not the classical integral logarithmic integral.  All conclusions below
refer to this definition.

The target main-term statement is: for every real `A > 0` and every real
`B`, there are `C > 0` and `N₀` such that, for all even `N ≥ N₀`,

```text
MainA(N) + MainB(N) ≤ C N / (log N)^A,                         (MT)
```

where

```text
MainA(N) = Σ_{d | P(N)} 3^ω(d) |li(N-2)-li(N)| / φ(d),

MainB(N) = Σ_{d | P(N)} 3^ω(d)
  | Σ_{1≠e | F(N)} μ(e) · #{p<N : p prime, 2≤N-p,
                            p ≡ N (mod lcm(d,e))} |.
```

`B` does not occur on the left.  Its quantifier is therefore harmless once
the bound is proved uniformly in `N`.

## 1. MainA: a complete written proof

### 1.1 A two-unit bound for the working logarithmic integral

Set `f(x)=x/log x`.  For `x>1`,

```text
f'(x) = (log x - 1)/(log x)^2.
```

If `x ≥ exp(2)`, then `log x ≥ 2`, so

```text
0 ≤ f'(x) ≤ 1.
```

The upper inequality follows from

```text
log x - 1 ≤ (log x)^2,
```

which is immediate for `log x ≥ 2`.  Hence, for `N ≥ exp(2)+2`, the mean
value theorem on `[N-2,N]` gives

```text
|li(N)-li(N-2)| = |f(N)-f(N-2)| ≤ 2.                           (1)
```

This is a bounded local-difference estimate.  The stronger asymptotic
`O(1/log N)` is unnecessary for the present argument.

### 1.2 The weighted divisor sum

The corrected sifting product is squarefree and every prime divisor of
`P(N)` is at most `N`.  The standard Mertens divisor-sum estimate therefore
applies:

```text
Σ_{d | P(N)} 3^ω(d)/φ(d) ≤ C₁ (log N)^3                       (2)
```

for an absolute positive constant `C₁` and all sufficiently large `N`.

For completeness, this is the usual Euler-product argument.  Squarefreeness
gives

```text
Σ_{d | P} 3^ω(d)/φ(d) = ∏_{p | P} (1 + 3/(p-1)).
```

Using `1+t ≤ exp(t)`, this is at most

```text
exp(3 Σ_{p | P} 1/(p-1)).
```

Mertens' reciprocal-prime estimate gives

```text
Σ_{p≤N} 1/(p-1) ≤ log log N + C₂,
```

which proves (2), after enlarging the constant.  This is a reusable ANT
lemma, not Chen-specific analysis.

Combining (1) and (2),

```text
MainA(N) ≤ 2 C₁ (log N)^3.                                    (3)
```

Finally, for every real `A>0`,

```text
(log N)^(A+3) / N → 0.
```

Thus there is `N_A` such that `(log N)^(A+3) ≤ N` for `N≥N_A`.
Multiplying (3) by `(log N)^A` and dividing by the positive denominator
yields

```text
MainA(N) ≤ 2 C₁ N/(log N)^A.                                  (4)
```

This proves the MainA contribution to (MT), with no distribution theorem.

## 2. MainB: signed Möbius cancellation and a complete written proof

The absolute values in MainB are outside the Möbius sum.  This placement is
essential.  Moving them inside would retain an `e=2` term of order `N/log N`
and produce a false negligible-error claim.

For a fixed `d | P(N)`, Möbius inversion over the forbidden product gives

```text
Σ_{1≠e | F(N)} μ(e) · base(lcm(d,e)) = - #{p ∈ S_d},           (5)
```

where `S_d` is the set of primes `p<N` satisfying `2≤N-p`, `d | N-p`, and
having a prime divisor from `F(N)` in `N-p`.  Therefore the inner absolute
value is exactly a nonnegative cardinality.

Interchanging the finite `d` and `p` sums in (5), and using squarefreeness of
`P(N)`, gives the exact identity

```text
MainB(N) = Σ_{p ∈ S} 4^ω(gcd(P(N),N-p)),                       (6)
```

where `S` is the same forbidden-prime support without the condition `d | N-p`.
Indeed, for every squarefree `m`,

```text
Σ_{d | m} 3^ω(d) = 4^ω(m).                                    (7)
```

The elementary pointwise estimate

```text
4^ω(m) ≤ 16^8 √m   (m≥1)                                      (8)
```

follows by splitting prime divisors at 16: at most sixteen primes are below
16, while every remaining prime contributes at least 16 to their product.
Since `gcd(P(N),N-p)≤N`, (6) and (8) give

```text
MainB(N) ≤ |S|·16^8√N.                                        (9)
```

For even `N`, the support `S` injects into `{2} ∪ primeFactors(F(N))`:
if a forbidden prime divides `N-p`, then either it is 2 and forces `p=2`, or
it divides `N` and hence, because `p` is prime, equals `p`.  Consequently

```text
|S| ≤ 1 + ω(F(N)).                                             (10)
```

Every prime divisor of `F(N)` is either 2 or divides `N`, hence

```text
ω(F(N)) ≤ 1+ω(N) ≤ 1 + log N/log 2.                            (11)
```

Equations (9)--(11) show

```text
MainB(N) ≪ √N log N.                                           (12)
```

For every real `A>0`,

```text
log^(A+1) N / √N → 0.
```

Thus, after increasing the threshold,

```text
√N log N ≤ N/(log N)^A,
```

and (12) implies

```text
MainB(N) ≤ C_A N/(log N)^A.                                   (13)
```

This proves the MainB contribution to (MT).  The use of an arbitrary real
`A`, rather than a natural exponent, causes no mathematical issue: choose an
integer `k ≥ A`; for `log N ≥ 1`, `(log N)^A ≤ (log N)^k`, and the usual
log-power-versus-power limit applies.

## 3. Conclusion for the main-term input

Add (4) and (13), and take the larger threshold.  This proves the full
statement `ChenPanTruncationMainTermBound` as written.  The proof is uniform
in the unused parameter `B`.

Status: **proved on paper**, conditional only on the standard Mertens
reciprocal-prime estimate already supplied by the ANT foundation.  It is not
yet asserted as a completed Lean theorem; the former WIP Lean attempt was
closed so this document, not CI status, is the current source of truth.

## 4. The genuinely open input: truncated distribution error

The preceding proof does **not** prove
`ChenPanTruncationSieveBound`.  Its left side contains two averaged AP error
terms:

```text
Σ_{d|P} 3^ω(d) Σ_{1≠e|F} |μ(e)| |Δ(N-2; lcm(d,e), N mod lcm(d,e))|

+ Σ_{d|P, d outside the truncation range} 3^ω(d)|Δ(N-2;d,N mod d)|.
```

Here `Δ` is the prime-counting error relative to `li/φ`.  A pointwise AP
bound cannot be summed over these divisor families; the required statement
is a Pan/Bombieri--Vinogradov-type *weighted mean-value theorem*, with the
correct truncation and a log-saving of every prescribed order.

This is an essential analytic obstruction, not a Lean-engineering gap.  The
ANT supply line is:

```text
Vaughan identity
  -> Type-I and Type-II character mean values
  -> weighted Pan mean-value theorem
  -> Chen-specific lcm/truncation bridge
  -> ChenPanTruncationSieveBound.
```

The first and last arrows have substantial finite/algebraic reductions in the
repositories.  The Type-I/II character mean-value estimates remain the
research-level core.  Any claim that Chen is complete before this averaged
estimate is supplied is false.

## 5. Atlas entry and stop condition

```text
corrected finite bridge                       [proven]
          +
MainA/MainB truncation main term              [proved on paper]
          +
weighted Pan/BV truncated error               [conditional: open]
          |
          v
CorrectedChenPanTruncationInput               [conditional]
          |
          v
Chen weighted error control and positivity    [conditional]
          |
          v
prime + P2 representation for large even N   [universal target]
```

The next smallest falsifiable artifact is a written derivation of the exact
weighted Pan statement needed for the two displayed error sums, including its
modulus range and lcm multiplicities.  Stop the current route if that
derivation requires a stronger statement than the classical Pan theorem or
if its weights cannot be reduced to the existing `3^ω(q)` mean-value form.
