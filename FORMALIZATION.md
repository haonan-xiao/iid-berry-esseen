# Formalization guide

The main exported theorem is
`BerryEsseen.iidBerryEsseen45`. It is assembled in
`BerryEsseen/Theorem.lean` and imported by the
root module `BerryEsseen.lean`.

## Paper-to-Lean map

| Paper component | Main Lean modules |
| --- | --- |
| Definitions of normalized sums, moments, CDFs, and Kolmogorov distance | `BerryEsseen/Interface.lean` |
| Distribution-free `0.56` bound | `BerryEsseen/Probability/Universal.lean`, `BerryEsseen/Probability/Analytic.lean` |
| Stop-loss identities, range of `r`, and the constraint `(r - 1)^2 + (μ/ρ)^2 ≤ 1` | `BerryEsseen/CharacteristicFunction/MomentGeometry.lean` |
| Bound for `E[sin(uX)-uX]` | `BerryEsseen/CharacteristicFunction/SineCircle.lean` |
| Exact breakpoint, slope, and convex minorant | `BerryEsseen/CharacteristicFunction/BreakpointCertificate.lean`, `BerryEsseen/CharacteristicFunction/BreakpointNumerics.lean`, `BerryEsseen/CharacteristicFunction/ConvexMinorant.lean` |
| Single-summand characteristic-function bound combining the modulus bound with the bound for the sine remainder | `BerryEsseen/CharacteristicFunction/OneStepDisk.lean` |
| Prawitz kernel, band-limited CDF bounds, Fourier identities, and smoothing inequality | `BerryEsseen/Smoothing/` |
| Reduction to the scalar functional | `BerryEsseen/Smoothing/ExplicitSmoothing.lean` |
| Exact dyadic arithmetic and Darboux integration | `BerryEsseen/Certificate/Dyadic/` |
| Finite interval checker, coverage, and certificate data | `BerryEsseen/Certificate/Finite/` |
| Large-sample regions, coverage, and certificate data | `BerryEsseen/Certificate/LargeN/` |
| Continuous-domain coverage and numerical theorem | `BerryEsseen/Certificate/NumericalCertificate.lean` |
| Moment packaging for standardized i.i.d. sums | `BerryEsseen/Probability/StandardizedSumMoments.lean` |
| Final unconditional theorem | `BerryEsseen/Theorem.lean` |

The `routeB` prefix used by some definitions is an implementation namespace
for the scalar reduction used in the note; it does not denote an additional
hypothesis or a second theorem statement.

## Certificate boundary

The numerical certificate is finite data describing subdivision trees. Lean
proves that every accepted leaf bounds its whole parameter cell and that the
trees cover the full admissible continuous domain. The program that searched
for the trees is not part of the trusted base: the checked data are embedded
in the Lean modules and recomputed by `native_decide`.

The 99 finite data modules under `Certificate/Finite/Data/` are intentionally
separate build units. This lets Lake evaluate and cache each certificate
independently; they are proof data, not 99 distinct mathematical arguments.

Consequently:

- the probability theory, analytic reduction, checker semantics, and coverage
  theorems are kernel checked;
- evaluation of the closed Boolean certificates additionally trusts Lean's
  native compiler;
- no floating-point search result is used as a proof.

## Useful build targets

The full theorem is checked by:

```bash
lake build BerryEsseen
```

For a faster review of the analytic and checker-soundness layers without the
complete concrete certificate replay, representative modules include:

```bash
lake build BerryEsseen.Smoothing.PrawitzSmoothingInequality
lake build BerryEsseen.CharacteristicFunction.OneStepDisk
lake build BerryEsseen.Certificate.NumericalCertificate
lake build BerryEsseen.Probability.StandardizedSumMoments
```
