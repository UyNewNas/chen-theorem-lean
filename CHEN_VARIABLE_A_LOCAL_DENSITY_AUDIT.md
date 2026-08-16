# Variable-`a` Omega supply: local-density audit

## Status

This is a written source-matching audit of the variable-`a` prime-pair input
used by the corrected `Omega` workline.  It replaces an over-compressed target
with the actual local sieve data that a two-dimensional upper sieve must
consume.  It proves no new analytic estimate.

The affected interface is `PrimePairLinearFormBound` in
`MathlibNt/SieveTheory/PrimePair.lean`.  Its present right hand side contains
only `a / phi(a)`.  That is not the full local-density factor for the pair
of forms

```text
L1(n) = n,                 L2(n) = N - a n.
```

Consequently it must not yet be attributed directly to a standard uniform
Selberg/linear-sieve theorem.

## 1. Exact local calculation

For a prime `ell`, put

```text
nu_{N,a}(ell) = #{n mod ell : ell divides n (N-a n)}.
```

Assume first that `ell` does not divide `a`.  The forbidden residues are
`0` and `a^{-1} N`.  Hence

```text
nu_{N,a}(ell) = 1   if ell divides N,
                 2   if ell does not divide N.                 (LD)
```

The `ell | N` case is exactly the Goldbach local enhancement: the two
forbidden classes coalesce.  Relative to the generic dimension-two factor,
the Euler product therefore acquires

```text
product_{ell | N, ell > 2} (ell-1)/(ell-2),
```

or an equivalent singular-series normalization.  It is not uniformly
bounded in `N`; it cannot be hidden in a universal implied constant.

If `ell | a`, then `L2(n) = N (mod ell)`.  If also `ell | N`, the second
form has a fixed prime divisor; the sieve must first remove this imprimitive
case (and its possible exceptional exact-prime solutions), or state a
coprimality/factorization condition.  If `ell | a` but `ell` does not divide
`N`, only `L1` contributes a forbidden class.  Thus a source theorem also
has to specify how factors shared by `a` and `N` are treated.

This is a direct finite residue-class computation, not a heuristic.

## 2. Correct shape of the external input

For the primitive range after the fixed-divisor cases have been separated,
the required supply has schematic form

```text
PrimePairLinearFormCount(N,a)
  <= C * S(N,a) * (N/a)/(log(N/a) log N),                       (PP)
```

where `S(N,a)` is the explicitly defined singular/local-density factor built
from `nu_{N,a}`.  A coarser source theorem may replace `S(N,a)` by a proved
majorant containing both the `a`-local and `N`-local factors, for example
an appropriate multiple of

```text
(a/phi(a)) * product_{ell | N, ell > 2} (ell-1)/(ell-2).
```

The precise normalisation is a source choice, but omitting the `N` factor is
not.  Constants and thresholds must precede `forall N a`; the allowed range
and every coprimality condition belong in the statement.

## 3. Consequences for Omega and q1

`a = p1*p2` in the triple-factor branch is genuinely variable.  The valid
proof architecture is therefore

```text
finite switching reparameterization             [proven in Lean]
        -> primitive/imprimitive split          [new finite interface]
        -> distribution of n(N-a n)             [external analytic supply]
        -> dimension-two upper sieve with S(N,a)[external analytic supply]
        -> weighted sum over the actual a-range [Chen-local finite/analytic step]
        -> corrected Omega upper bound.
```

The q1 double-Mobius remainder is a separate dimension-two consumer and
still requires the repair described in `CHEN_Q1_ERROR_INTERFACE_AUDIT.md`.
Neither it nor the triple branch follows from the `a=1` lower-sieve weighted
BV interface.

## 4. Repository repair

Before any formal theorem is added, replace the current bare
`PrimePairLinearFormBound` target by an interface that includes:

1. the finite definition of `nu_{N,a}` and its Euler/local factor;
2. a primitive-range hypothesis or a separately formalized fixed-divisor
   reduction for `gcd(a,N)`;
3. a uniform source theorem in the form (PP); and
4. a proof that the resulting local factor sums correctly over the exact
   `chenF N a` support.

Stop condition: a statement with only `a/phi(a)` may be used solely as an
explicit provisional hypothesis, never labelled as the standard Chen/Selberg
prime-pair supply.

## References

* J.-R. Chen, *On the representation of a larger even integer as the sum of
  a prime and the product of at most two primes*, Scientia Sinica 16 (1973),
  157--176, DOI 10.1360/YA1973-16-2-157.
* H. Halberstam and H.-E. Richert, *Sieve Methods* (1974), Chapter 11
  (Chen's theorem and its upper-sieve stage).

These are provenance for the analytic supply; the residue computation above
is included so that the Lean interface can be audited independently of the
historical notation.
