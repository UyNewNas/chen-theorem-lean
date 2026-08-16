# Omega prime-count object audit

## Verdict

The legacy `SelbergUpperBound` Omega route is not presently a formalization
of the prime count used in the Chen switching argument.  Its definition

```text
primesInAP_weighted(x,a,q,l)
  = #{p <= x : a*p is prime and a*p == l (mod q)}
```

does not match the switched inner count, which has the shape

```text
#{p <= x/a : p is prime and N-a*p is prime,
                 N-a*p == 0 (mod q)}.                         (P)
```

For the Omega range `a = p1*p2 > 1`, the implemented count is identically
zero: if `a*p` is prime then `a = 1` or `p = 1`, while neither is possible
there.  Thus the proved theorem

```text
(a,d) > 1  ->  primesInAP_weighted(N,a,d,N mod d) <= 1
```

is true for the implemented object for a vacuous reason.  It is **not** the
Liu exceptional-fibre estimate and cannot be consumed as such.

This is an object/interface error, not a missing tactic.

## 1. Direct comparison

The relevant switched condition is that the complementary value is prime:

```text
N - a*p is prime,                 N - a*p == 0 (mod d).       (1)
```

Equivalently, `a*p == N (mod d)`, together with primality of `N-a*p`.
The legacy definition instead asks for primality of `a*p`.  These predicates
are unrelated.  In particular the implication

```text
a > 1 and (a*p).Prime  -> p = 1
```

proves an upper bound for the wrong finite set; it says nothing about (1).

## 2. The correct non-coprime argument for (P)

Let `g = gcd(a,d)`.  The congruence in (1) has:

```text
no solutions       if g does not divide N;
a reduced class    modulo d/g  if g divides N.
```

For the *correct* prime count the required `<= 1` conclusion is valid, but
for a different and very short reason.  If (1) holds, then `g` divides the
prime `N-a*p`.  Since `g>1`, primality forces

```text
N-a*p = g.
```

Consequently `p = (N-g)/a`, so there is at most one possible `p` (and often
none).  This is the genuine Liu-style exceptional-fibre reduction.  It
depends essentially on primality of **the complement** `N-a*p`; it cannot be
proved by saying that `a*p` is composite.

Thus the correct exceptional analysis must retain the actual source range,
the divisors shared by `a` and `d`, and the prime condition on `N-a*p`.  The
main-term side still has to track the corresponding imprimitive contribution
when it is separated from the primitive averaged distribution input.  This
agrees with the existing local-density audit: primes dividing `gcd(a,N)` are
fixed-divisor cases that must be stated explicitly before applying a
primitive two-dimensional sieve.

## 3. Correct replacement objects

There are two distinct counts; their separate APIs must not be conflated.

1.  **Primitive switched prime-pair count.**  For `gcd(a,d)=1`, define

    ```text
    Pi_pair(N,a,d) = #{p in the exact Chen range : p.Prime,
      (N-a*p).Prime, a*p == N (mod d)}.
    ```

    Its main term and error must be supplied by a prime-pair/dimension-two
    sieve with the local factor `S(N,a)` of
    `CHEN_VARIABLE_A_LOCAL_DENSITY_AUDIT.md`; a one-variable BV theorem is
    insufficient.

2.  **Imprimitive exceptional fibre.**  For `gcd(a,d)>1`, the actual
    complement-primality condition gives the exact `<= 1` lemma above.  What
    remains analytic is the weighted summation of its *main-term/error*
    contribution over the Chen `a,d` ranges, not the cardinality assertion
    itself.  This is part of the Omega/q1 error budget and must not be
    replaced by an assertion about `a*p` being composite.

The `q1` branch requires the same discipline after its double Mobius
expansion: it is a signed/repackaged pair-sieve remainder, not this old
one-variable proxy.

## 4. Required repository action

Until a source-matched replacement is proved, the following legacy items
must be labelled as finite algebra for an auxiliary, non-Chen object only:

```text
primesInAP_weighted
weightedDistributionError
coprime_condition_implies_bounded_ap
R1 auxiliary bound and every consumer that attributes it to Liu correction
```

Do not use them to discharge `CorrectedChenAnalyticPositivity`, the
variable-`a` Omega bound, or `q1APErrorUniformBound`.

The repair order is:

```text
exact switched finite count
  -> primitive / imprimitive partition
  -> local-density product and main-term convention
  -> source-stated dimension-two distribution/sieve bound
  -> exact weighted summation over Chen's a-range
  -> corrected Omega upper bound.
```

## References and scope

Chen's original theorem is the relevant historical target; the modern
explicit account by Bordignon--Johnston--Starichkova also displays the
Goldbach singular factor involving primes dividing `N`.  This note does not
claim a replacement analytic bound.  It records only the exact predicate
comparison and the elementary gcd reduction needed before a source theorem
can be formalized.

* J.-R. Chen, *On the representation of a larger even integer as the sum of
  a prime and the product of at most two primes*, Scientia Sinica 16 (1973),
  157--176, DOI 10.1360/YA1973-16-2-157.
* M. Bordignon, D. Johnston, V. Starichkova, *An explicit version of Chen's
  theorem*, arXiv:2207.09452.
