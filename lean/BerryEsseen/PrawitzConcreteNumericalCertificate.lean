import BerryEsseen.StandardizedSumMoments
import BerryEsseen.PrawitzNumericalCertificate
import BerryEsseen.DyadicPrawitzFiniteLeafCertificates
import BerryEsseen.DyadicPrawitzLargeNLeafCertificateSmall
import BerryEsseen.DyadicPrawitzLargeNLeafCertificateMiddle
import BerryEsseen.DyadicPrawitzLargeNLeafCertificateUpper

/-!
# Fully checked Route B numerical certificate

This module is the concrete end of the Path 1 proof.  It combines the finite
certificates for `1 ≤ n < 100` with the three large-`n` region certificates,
then feeds the resulting numerical theorem into the analytic and probabilistic
assembly.
-/

open MeasureTheory ProbabilityTheory

namespace BerryEsseen

noncomputable section

/-- The exact dyadic certificates cover the full Route B numerical domain. -/
theorem routeB_exactCertifiedNumericalBound :
    CertifiedNumericalBound (routeBU routeBKappa routeBTheta) :=
  routeB_certifiedNumericalBound_of_leaf_certificates
    routeB_finiteLeafCertificates_checked
    routeBLargeSmallLeafCode_checked
    routeBLargeMiddleLeafCode_checked
    routeBLargeUpperLeafCode_checked

/-- The i.i.d. Berry--Esseen bound with constant `0.45`, obtained from the
fully checked Route B certificate. -/
theorem iidBerryEsseen45
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1) :
    IIDBerryEsseen45Conclusion P X
      (thirdAbsoluteMoment (P.map (X 0))) :=
  iidBerryEsseen45_of_certifiedNumericalBound
    routeB_exactCertifiedNumericalBound P X hindep hident hX hmean hsecond

end

end BerryEsseen
