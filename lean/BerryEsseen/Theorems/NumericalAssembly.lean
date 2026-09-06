import BerryEsseen.Theorems.CertificateImplication
import BerryEsseen.Interval.Finite.AdaptiveFullCover
import BerryEsseen.Interval.Small.SplitCover
import BerryEsseen.Interval.Large.TargetCover
import BerryEsseen.PrawitzNumericalCertificate

/-!
# Theorems / Numerical Assembly
-/

namespace BerryEsseen

open MeasureTheory ProbabilityTheory

noncomputable section

theorem targetAware_normalizedKolmogorovDistance_lt_879_2000
    (hfinite : ∀ n : ℕ, 1 ≤ n → n < 100 →
      ∃ extraFuel : ℕ,
        bound4395OldFiniteTargetAwareLeafCodeCertificate
          n extraFuel = true)
    {smallCode middleCode upperCode : String}
    {smallLowerFuel smallUpperFuel middleFuel upperFuel : ℕ}
    (hsmallLower : variableAlphaSmallRefinedLeafCodeCertificateAt
      smallLowerFuel smallCode dyadicRouteBUnitInterval
        certifiedLargeSmallLowerRootZ = true)
    (hsmallUpper : variableAlphaSmallRefinedLeafCodeCertificateAt
      smallUpperFuel smallCode dyadicRouteBUnitInterval
        certifiedLargeSmallUpperRootZ = true)
    (hmiddle : bound4395LargeRefinedLeafCodeCertificate
      .middle middleFuel middleCode = true)
    (hupper : bound4395LargeRefinedLeafCodeCertificate
      .upper upperFuel upperCode = true)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n)
    (hrhoUpper : thirdAbsoluteMoment (P.map (X 0)) ≤
      ((56 : ℝ) / 45) * Real.sqrt (n : ℝ)) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      bound4395TargetConstant := by
  let mu := P.map (X 0)
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let eta := rho * (r - 1)
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  have hnPos : 0 < n := Nat.zero_lt_of_lt hn
  have hrho : 1 ≤ rho := by
    dsimp only [rho, mu]
    exact thirdAbsoluteMoment_ge_one (P.map (X 0)) hX hsecond
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hr : 1 ≤ r := by
    dsimp only [r, mu]
    exact symmetrizationRatio_lower (P.map (X 0)) hX hmean hsecond
  have hrUpper : r ≤ 1 + 1 / rho := by
    dsimp only [r, rho, mu]
    exact symmetrizationRatio_upper (P.map (X 0)) hX hmean hsecond
  have heta0 : 0 ≤ eta := by
    dsimp only [eta]
    exact mul_nonneg (zero_le_one.trans hrho) (sub_nonneg.mpr hr)
  have heta1 : eta ≤ 1 := by
    have hdiff : r - 1 ≤ 1 / rho := by linarith
    have hmul := mul_le_mul_of_nonneg_left hdiff (zero_le_one.trans hrho)
    have hcancel : rho * (1 / rho) = 1 := by field_simp
    dsimp only [eta]
    linarith
  have hrouteR : routeBDboundR rho eta = r := by
    simpa only [eta] using routeBDboundR_mul_excess hrhoPos.ne'
  by_cases hnLarge : 100 ≤ n
  · have hLmax : routeBSmoothingScale n rho ≤ (56 : ℝ) / 45 :=
      routeBSmoothingScale_le_cutoff hnPos (by
        simpa only [rho, mu] using hrhoUpper)
    by_cases hsmallL : routeBSmoothingScale n rho ≤ (1 : ℝ) / 16
    · simpa only [bound4395TargetConstant, rho, mu] using
        normalizedKolmogorovDistance_lt_879_2000_of_variable_smallSplit
          hsmallLower hsmallUpper P X hindep hident hX hmean hsecond
            hnLarge hsmallL
    · have hmiddleL0 : (1 : ℝ) / 16 ≤ routeBSmoothingScale n rho :=
        le_of_lt (lt_of_not_ge hsmallL)
      by_cases hmiddleL1 : routeBSmoothingScale n rho ≤ (1 : ℝ) / 10
      · let L := routeBSmoothingScale n rho
        let xR := routeBLargeMiddleX L
        let zR := routeBLargeMiddleZ rho eta
        have hx0 : 0 ≤ xR := routeBLargeMiddleX_nonnegative
          (by simpa only [L] using hmiddleL0)
        have hx1 : xR ≤ 1 := routeBLargeMiddleX_le_one
          (by simpa only [L] using hmiddleL1)
        have hz0 : 0 ≤ zR := routeBLargeMiddleZ_nonnegative hrho heta0
        have hz1 : zR ≤ 1 := routeBLargeMiddleZ_le_one hrho heta1
        have hregionL : routeBLargeDirectRegionL .middle xR =
            routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0))) := by
          dsimp only [xR]
          rw [routeBLargeMiddleL_inverse]
        have hregionR : routeBLargeDirectRegionR .middle xR zR =
            symmetrizationRatio (P.map (X 0)) := by
          have hinv := routeBLargeMiddleR_inverse
            (rho := rho) (eta := eta) hrhoPos
          dsimp only [xR, zR]
          simpa only [routeBLargeDirectRegionR, r, mu] using hinv.trans hrouteR
        simpa only [bound4395TargetConstant, rho, mu] using
          normalizedKolmogorovDistance_lt_879_2000_of_post044LargeCode
            hmiddle hx0 hx1 hz0 hz1 P X hindep hident hX hmean hsecond
              hnLarge hregionL hregionR
      · have hupperL0 : (1 : ℝ) / 10 ≤ routeBSmoothingScale n rho :=
          le_of_lt (lt_of_not_ge hmiddleL1)
        let L := routeBSmoothingScale n rho
        let xR := routeBLargeUpperX L
        let zR := routeBLargeUpperZ n eta
        have hx0 : 0 ≤ xR := routeBLargeUpperX_nonnegative
          (by simpa only [L] using hupperL0)
        have hx1 : xR ≤ 1 := routeBLargeUpperX_le_one
          (by simpa only [L] using hLmax)
        have hz0 : 0 ≤ zR := routeBLargeUpperZ_nonnegative hnPos heta0
        have hz1 : zR ≤ 1 := routeBLargeUpperZ_le_one hnLarge heta1
        have hregionL : routeBLargeDirectRegionL .upper xR =
            routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0))) := by
          dsimp only [xR]
          rw [routeBLargeUpperL_inverse]
        have hregionR : routeBLargeDirectRegionR .upper xR zR =
            symmetrizationRatio (P.map (X 0)) := by
          have hinv := routeBLargeUpperR_inverse
            (n := n) (rho := rho) (eta := eta) hnPos hrhoPos
          dsimp only [xR, zR, L]
          simpa only [r, mu] using hinv.trans hrouteR
        simpa only [bound4395TargetConstant, rho, mu] using
          normalizedKolmogorovDistance_lt_879_2000_of_post044LargeCode
            hupper hx0 hx1 hz0 hz1 P X hindep hident hX hmean hsecond
              hnLarge hregionL hregionR
  · have hnFinite : n < 100 := Nat.lt_of_not_ge hnLarge
    obtain ⟨extraFuel, hcertificate⟩ := hfinite n hn hnFinite
    have hfiniteBound :=
      normalizedKolmogorovDistance_lt_879_2000_of_post044OldFiniteTargetAware
        P X hindep hident hX hmean hsecond hn hcertificate hrho
          (by simpa only [rho, mu] using hrhoUpper) heta0 heta1
    simpa only [bound4395TargetConstant, rho, r, eta, mu] using hfiniteBound

theorem iidBerryEsseen879_2000_of_targetAware_certificates
    (hfinite : ∀ n : ℕ, 1 ≤ n → n < 100 →
      ∃ extraFuel : ℕ,
        bound4395OldFiniteTargetAwareLeafCodeCertificate
          n extraFuel = true)
    {smallCode middleCode upperCode : String}
    {smallLowerFuel smallUpperFuel middleFuel upperFuel : ℕ}
    (hsmallLower : variableAlphaSmallRefinedLeafCodeCertificateAt
      smallLowerFuel smallCode dyadicRouteBUnitInterval
        certifiedLargeSmallLowerRootZ = true)
    (hsmallUpper : variableAlphaSmallRefinedLeafCodeCertificateAt
      smallUpperFuel smallCode dyadicRouteBUnitInterval
        certifiedLargeSmallUpperRootZ = true)
    (hmiddle : bound4395LargeRefinedLeafCodeCertificate
      .middle middleFuel middleCode = true)
    (hupper : bound4395LargeRefinedLeafCodeCertificate
      .upper upperFuel upperCode = true)
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
  apply iidBerryEsseen879_2000_of_numericalBranch
    P X hindep hident hX hmean hsecond
  intro n hn hrhoUpper
  exact targetAware_normalizedKolmogorovDistance_lt_879_2000
    hfinite hsmallLower hsmallUpper hmiddle hupper
      P X hindep hident hX hmean hsecond hn hrhoUpper

end

end BerryEsseen
