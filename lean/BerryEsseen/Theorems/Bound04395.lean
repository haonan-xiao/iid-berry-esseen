import BerryEsseen.Certificates.Finite.Assembly
import BerryEsseen.Certificates.Small.LowerNativeCheck
import BerryEsseen.Certificates.Small.UpperNativeCheck
import BerryEsseen.Certificates.Large.MiddleFuel5NativeCheck
import BerryEsseen.Certificates.Large.UpperFuel8NativeCheck
import BerryEsseen.Theorems.NumericalAssembly

/-!
# Theorems / Bound04395
-/

namespace BerryEsseen

open MeasureTheory ProbabilityTheory

noncomputable section

theorem iidBerryEsseen879_2000
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1) :
    IIDBerryEsseen879_2000Conclusion P X
      (thirdAbsoluteMoment (P.map (X 0))) := by
  have hsmallLower :
      variableAlphaSmallRefinedLeafCodeCertificateAt
        4 oldLargeSmallCodeValue dyadicRouteBUnitInterval
          certifiedLargeSmallLowerRootZ = true := by
    simpa [variableAlphaSmallLowerConcreteCertificate] using
      variableAlphaSmallLowerConcreteCertificate_checked
  have hsmallUpper :
      variableAlphaSmallRefinedLeafCodeCertificateAt
        8 oldLargeSmallCodeValue dyadicRouteBUnitInterval
          certifiedLargeSmallUpperRootZ = true := by
    simpa [variableAlphaSmallUpperConcreteCertificate] using
      variableAlphaSmallUpperConcreteCertificate_checked
  have hmiddle :
      bound4395LargeRefinedLeafCodeCertificate
        .middle 5 oldLargeMiddleCodeValue = true := by
    exact bound4395LargeMiddleFuel5ConcreteCertificate_checked
  have hupper :
      bound4395LargeRefinedLeafCodeCertificate
        .upper 8 oldLargeUpperCodeValue = true := by
    simpa using
      bound4395LargeUpperFuel8ConcreteCertificate_checked
  exact iidBerryEsseen879_2000_of_targetAware_certificates
    bound4395FiniteTargetAwareCertificates_checked
      hsmallLower hsmallUpper hmiddle hupper
      P X hindep hident hX hmean hsecond

end

end BerryEsseen
