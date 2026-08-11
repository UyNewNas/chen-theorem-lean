# Chen chain: formalization audit

This document is the review entry point for the Chen-theorem development in
`MathlibNt`.  It describes what Lean has checked, what is deliberately stated
as an explicit assumption, and what remains unformalized.

## Executive summary

The repository does **not** currently contain an unconditional formal proof of
Chen's theorem.  It contains a kernel-checked conditional derivation:

```text
ChenAnalyticBounds + ChenCountingBridge
  -> chen_key_inequality
  -> key_inequality_implies_chen
  -> chens_theorem
```

The two assumptions are named, typed Lean propositions rather than hidden
`sorry`s. The imported analytic foundation now discharges all three former
PNT/Mertens obligations. `ChenCountingBridge` is a historical conditional
interface that finite evaluation refutes for the present counting definitions;
its replacement, the corrected finite counting bridge on the corrected
candidates, is complete and kernel-checked (see section 3).

## Current `sorry` inventory

As of 2026-08-12, the tracked Lean sources contain no executable `sorry` or
`admit` terms. In particular:

| File | Declaration | Status | Result |
| --- | --- | --- | --- |
| `MertensTheorem.lean` | `prime_number_theorem` | Complete | Natural-number PNT consumer |
| `MertensTheorem.lean` | `mertens_second_theorem` | Complete | Mertens-II consumer |
| `MertensTheorem.lean` | `mertens_product_formula` | Complete | Precise `exp (-γ)` product constant |

No declaration in `ChensTheorem.lean`, `SwitchingPrinciple.lean`,
`SelbergUpperBound.lean`, or `BombieriVinogradov.lean` currently has a
`sorry`.

The weaker theorem `primeProduct_asymptotic_order` is also independently
kernel-checked: it derives `primeProduct x = Θ(1 / log x)` from the audited
Mertens-II interface.

## Checked conditional chain

### 1. Analytic input

`SwitchingPrinciple.ChenAnalyticBounds` is a proposition asserting, for every
even `N >= 1000`, the two uniform numerical estimates needed by the classical
Chen argument:

```lean
2.6408 * chenW N >= 2.6408 * 2.6408 * N / log N ^ 2
chenOmega N <= 3.9404 * N / log N ^ 2
```

This is intentionally an external input.  The local results named
`chenW_lower_bound` and `chenOmega_upper_bound` prove only *pointwise
additive-remainder* interfaces: their constants may depend on the fixed `N`.
They must not be read as the uniform estimates above.

### 2. Numerical key inequality

Given `ChenAnalyticBounds`, `chen_key_inequality` proves

```lean
chenW N - chenOmega N / 2 > 0
```

by elementary real arithmetic.  The positivity comes from
`2.6408 - 3.9404 / 2 = 0.6706 > 0` and from the positive scale
`N / log N ^ 2`.

### 3. Combinatorial input

`SwitchingPrinciple.ChenCountingBridge` is a historical proposition asserting that the
positive difference above is bounded by the cardinality of
`chenGoodRepresentations N`, the finite set of primes `p < N` for which
`N - p >= 2` is at most 2-almost-prime.

This proposition is **false** for the current working definitions and is
retained only as an explicit conditional boundary. For example, an external
finite evaluation at `N = 1000` gives `chenW = 153`, `chenOmega = 17`, and
`chenGoodRepresentations.card = 122`, contradicting the stated inequality.
The issue is not a missing Lean tactic: `chenW` is an unweighted filter count,
whereas `chenOmega` uses a different factor-pair index and does not establish
the claimed `/ 2` multiplicity.

The replacement is complete on the corrected objects
(`CHEN_PROOF_ATLAS.md`): `correctedChenCandidates`, the named unit boundary,
and the factor-multiplicity-aware bad fibre are defined in
`SwitchingPrinciple.lean`. The partition and the fibre theorem
`correctedChenBad_penalty_ge_two` are kernel-checked, the summed bridge
`corrected_counting_bridge` holds under the two cutoff conditions, and the
public corollary `corrected_counting_bridge_public_of_nine_le` discharges
both cutoffs uniformly for `N ≥ 9`:

```lean
((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2 ≤
  ((chenGoodRepresentations N).card : ℝ)
```

No finite counting or rounding conversion remains at that boundary.

### 4. Extraction of the representation

Given `ChenCountingBridge`, `key_inequality_implies_chen` turns positivity of
the real cardinality bound into `Finset.card_pos`, extracts an element of
`chenGoodRepresentations N`, and proves `N = p + (N - p)`.

`ChensTheorem.chens_theorem` packages that result using the project's
`Semiprime q := 2 <= q /\ Nat.IsAtMostAlmostPrime 2 q` definition.

## Pointwise interfaces versus classical theorems

Several historic declarations had a constant quantified too weakly to express
the advertised uniform analytic theorem, or claimed a stronger theorem than
their definitions supported.  They were corrected rather than filled with an
opaque proof.

| Declaration | Current meaning |
| --- | --- |
| `bombieri_vinogradov` | Fixed `x, q, y, l` multiplicative-remainder interface; not the classical average-over-moduli BV theorem. |
| `pan_mean_value_theorem` | Fixed-parameter remainder interface; the previous summand did not depend on its summation variable. |
| `main_term_bound` | Fixed-`N` additive-remainder interface; `SelbergWeights` does not encode optimality. |
| `chenOmega_simple_bound` | Fixed-`N` additive-remainder interface, derived from the complete bound. |
| `chenW_lower_bound` | Fixed-`N` additive-remainder interface. |

The names are retained for API continuity, but their docstrings state these
limitations.  Reviewers should use `ChenAnalyticBounds` when they need the
genuine uniform estimates.

## Review checklist

1. Confirm the inventory with:

   ```sh
   rg -n '^\s*sorry\s*$' MathlibNt --glob '*.lean'
   ```

2. Inspect the exact types of `ChenAnalyticBounds` and `ChenCountingBridge` in
   `MathlibNt/SieveTheory/SwitchingPrinciple.lean`.
3. Compile the chain, including dependencies, with the project toolchain.
4. Do not label `chens_theorem` unconditional unless a corrected finite bridge
   and proofs of both replacement inputs are supplied.
5. The imported `analytic-number-theory-lean` v0.3.0 discharges all local
   PNT/Mertens obligations. `Audit.lean` checks the resulting consumers, and
   CI enforces the exact standard-axiom whitelist.

## Next completion milestones

1. ✅ Define corrected W/Omega counting objects, including the unit boundary
   and a proven factor-multiplicity map.
2. ✅ Prove the corrected finite switching bridge, with the cutoff arithmetic
   discharged uniformly for `N ≥ 9`.
3. Replace `ChenAnalyticBounds` by a uniform Jurkat--Richert/Selberg proof for
   the corrected objects, then remove the two explicit assumptions.

The public repository's related documentation is `PROOF_REFERENCE.md` and
`EXTERNAL_DEPENDENCY_AUDIT.md`.  Project-wide scratch status files are
intentionally not part of this release.
