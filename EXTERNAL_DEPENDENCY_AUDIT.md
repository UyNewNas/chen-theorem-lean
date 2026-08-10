# External PNT dependency audit

This repository does not currently vendor or import an external prime number
theorem development.  The following audit records a candidate dependency that
was checked separately, so that later integration begins from reproducible
evidence rather than from a citation alone.

## Candidate

- Repository: [`math-inc/strongpnt`](https://github.com/math-inc/strongpnt)
- Audited revision: `2f5835c322314f55f1026ec2f139d704b7c45c69`
- Toolchain: Lean `v4.21.0`
- Pinned upstream PNTAnd revision: `47f29a1e5a4fe1daf5c3f8c5fc8408626e95fda5`

The candidate's complete build produced both `StrongPNT.olean` and
`StrongPNT/PNT5_Strong.olean`.  Lean reported the central declaration as:

```lean
Strong_PNT : ∃ c > 0,
  (ChebyshevPsi - id) =O[Filter.atTop]
    fun x => x * Real.exp (-c * Real.log x ^ (1 / 2))
```

At that revision, running `#print axioms Strong_PNT` reported only:

```text
[propext, Classical.choice, Quot.sound]
```

In particular, it did **not** report `sorryAx`.

## Verified prime-counting consequence

The pinned `PrimeNumberTheoremAnd` dependency also contains
`PrimeNumberTheoremAnd.Consequences.pi_alt`, a standard prime-counting
asymptotic:

```lean
pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
  ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x
```

At the same pinned dependency revision, `Consequences.olean` was built
separately and `#print axioms pi_alt` reported only:

```text
[propext, Classical.choice, Quot.sound]
```

The source file and one of its transitive files contain unrelated unfinished
declarations.  They do not occur in the dependency closure of `pi_alt`, as the
axiom report confirms.

## Newer PNTAnd release candidate

PNTAnd has a newer standalone release that is much closer to this repository's
toolchain:

- Repository: [`AlexKontorovich/PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
- Release: `v4.32.2`
- Audited revision: `6a380f0c4658c04a420a9eb00b1ed62a1e3fde01`
- Toolchain: Lean `v4.32.2`

Its `PrimeNumberTheoremAnd.Consequences` module was built from a clean
dependency resolution.  The release's `pi_alt` has the same relevant shape,
and `#print axioms pi_alt` again reported only:

```text
[propext, Classical.choice, Quot.sound]
```

This is the preferred import candidate for the local prime-counting PNT: it
requires a one-release toolchain adaptation from Lean 4.32.2 to the public
Lean 4.33.0-rc1, rather than porting all of StrongPNT from Lean 4.21.

## What this establishes

The candidate supplies a kernel-checked strong prime number theorem for the
Chebyshev psi function.  Separately, the audited `pi_alt` consequence supplies
the conventional prime-counting asymptotic.  Together they give a credible
analytic foundation for the local `prime_number_theorem` after toolchain and
normalization adaptation.

The local repository already proves the normalization step independently:
`primeCount_eq_primeCounting` identifies its finite definition with
`Nat.primeCounting`, and `primeCountingPNT_implies_prime_number_theorem`
derives the local epsilon-PNT statement from the `pi_alt` shape.  Thus a future
port only needs to provide `PrimeCountingPNT`; it does not need to redo this
logical conversion.

## What it does not establish

This audit is not an integration.  The public Chen repository uses Lean
`v4.33.0-rc1`, while the audited candidate uses Lean `v4.21.0`.  Moreover, its
conclusion concerns `ChebyshevPsi`, whereas the local open theorem is stated
for the finite prime-counting function `primeCount`, and the local Mertens
statements use specific finite sums and products.

Before removing any local `sorry`, an integration must:

1. port or otherwise bridge the PNTAnd v4.32.2 dependency closure of `pi_alt`
   to the pinned public toolchain;
2. establish the local `PrimeCountingPNT` interface from the ported `pi_alt`
   statement;
3. derive the two stated Mertens estimates, including their finite-range and
   constant conventions;
4. rerun `#print axioms` on every resulting local theorem and on
   `chens_theorem`.

Until then, the three local `sorry`s remain explicit open obligations.
