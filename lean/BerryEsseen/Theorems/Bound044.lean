import BerryEsseen.Smoothing.UniversalBound
import BerryEsseen.Certificates.Data.FinitePartitions
import BerryEsseen.Interval.Small.FixedExponentSplitCover
import BerryEsseen.Interval.Large.Cover
import BerryEsseen.PrawitzNumericalCertificate
import BerryEsseen.StandardizedSumMoments

/-!
# Theorems / Bound044
-/

namespace BerryEsseen

open MeasureTheory ProbabilityTheory

noncomputable section

def targetConstant044 : ℝ := (44 : ℝ) / 100

def universalCutoff : ℝ := (109 : ℝ) / 88

def IIDBerryEsseen44Conclusion {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (X : ℕ → Omega → ℝ) (rho : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    HasBerryEsseenBound (standardizedSumLaw P X n) rho n targetConstant044

theorem target_mul_universalCutoff :
    targetConstant044 * universalCutoff = refinedUniversalConstant := by
  norm_num [targetConstant044, universalCutoff, refinedUniversalConstant]

theorem universalCutoff_lt_routeBCutoff :
    universalCutoff < (56 : ℝ) / 45 := by
  norm_num [universalCutoff]

/-- The four exact certificate families imply the normalized strict `0.44`
bound throughout the original (slightly larger) Route B numerical domain. -/
theorem normalizedKolmogorovDistance_lt_044_of_certificates
    (hfinite : ∀ n : ℕ, 1 ≤ n → n < 100 →
      ∃ extraFuel : ℕ,
        certifiedOldRefinedLeafCodeCertificate n extraFuel = true)
    {smallCode middleCode upperCode : String}
    {smallLowerFuel smallUpperFuel middleFuel upperFuel : ℕ}
    (hsmallLower : certifiedLargeSmallRefinedLeafCodeCertificateAt
      smallLowerFuel smallCode dyadicRouteBUnitInterval
        certifiedLargeSmallLowerRootZ = true)
    (hsmallUpper : certifiedLargeSmallRefinedLeafCodeCertificateAt
      smallUpperFuel smallCode dyadicRouteBUnitInterval
        certifiedLargeSmallUpperRootZ = true)
    (hmiddle : certifiedLargeRefinedLeafCodeCertificate
      .middle middleFuel middleCode = true)
    (hupper : certifiedLargeRefinedLeafCodeCertificate
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
      targetConstant044 := by
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
    · simpa only [targetConstant044, rho, mu] using
        normalizedKolmogorovDistance_lt_044_of_largeSmallSplitCertificates
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
        simpa only [targetConstant044, rho, mu] using
          normalizedKolmogorovDistance_lt_044_of_largeRefinedLeafCodeCertificate
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
        simpa only [targetConstant044, rho, mu] using
          normalizedKolmogorovDistance_lt_044_of_largeRefinedLeafCodeCertificate
            hupper hx0 hx1 hz0 hz1 P X hindep hident hX hmean hsecond
              hnLarge hregionL hregionR
  · have hnFinite : n < 100 := Nat.lt_of_not_ge hnLarge
    obtain ⟨extraFuel, hcertificate⟩ := hfinite n hn hnFinite
    have hfiniteBound :=
      normalizedKolmogorovDistance_lt_044_of_oldRefinedLeafCodeCertificate
        P X hindep hident hX hmean hsecond hn hcertificate hrho
          (by simpa only [rho, mu] using hrhoUpper) heta0 heta1
    simpa only [targetConstant044, rho, r, eta, mu] using hfiniteBound

/-- Conditional final i.i.d. theorem.  The premises are only the four exact
certificate families; all analytic, probabilistic, regime-cover, and cutoff
steps are discharged here. -/
theorem iidBerryEsseen44_of__certificates
    (hfinite : ∀ n : ℕ, 1 ≤ n → n < 100 →
      ∃ extraFuel : ℕ,
        certifiedOldRefinedLeafCodeCertificate n extraFuel = true)
    {smallCode middleCode upperCode : String}
    {smallLowerFuel smallUpperFuel middleFuel upperFuel : ℕ}
    (hsmallLower : certifiedLargeSmallRefinedLeafCodeCertificateAt
      smallLowerFuel smallCode dyadicRouteBUnitInterval
        certifiedLargeSmallLowerRootZ = true)
    (hsmallUpper : certifiedLargeSmallRefinedLeafCodeCertificateAt
      smallUpperFuel smallCode dyadicRouteBUnitInterval
        certifiedLargeSmallUpperRootZ = true)
    (hmiddle : certifiedLargeRefinedLeafCodeCertificate
      .middle middleFuel middleCode = true)
    (hupper : certifiedLargeRefinedLeafCodeCertificate
      .upper upperFuel upperCode = true)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1) :
    IIDBerryEsseen44Conclusion P X
      (thirdAbsoluteMoment (P.map (X 0))) := by
  intro n hn
  let mu := P.map (X 0)
  let rho := thirdAbsoluteMoment mu
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  letI : IsProbabilityMeasure (standardizedSumLaw P X n) :=
    isProbabilityMeasure_standardizedSumLaw P X
      (fun k => (hident k).aemeasurable_fst) n
  have hnPos : 0 < n := Nat.zero_lt_of_lt hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  have hrho : 1 ≤ rho := by
    dsimp only [rho, mu]
    exact thirdAbsoluteMoment_ge_one (P.map (X 0)) hX hsecond
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hX0 : MemLp (X 0) 3 P := by
    have hmap := (memLp_map_measure_iff aestronglyMeasurable_id
      (hident 0).aemeasurable_fst).1 hX
    simpa only [Function.comp_apply, id_eq] using hmap
  have hsourceMean : ∫ omega, X 0 omega ∂P = 0 := by
    rw [← hmean]
    change (∫ omega, X 0 omega ∂P) =
      ∫ x : ℝ, (id : ℝ → ℝ) x ∂P.map (X 0)
    rw [integral_map (hident 0).aemeasurable_fst
      aestronglyMeasurable_id]
    rfl
  have hsourceSecond : ∫ omega, (X 0 omega) ^ 2 ∂P = 1 := by
    rw [← hsecond]
    change (∫ omega, (X 0 omega) ^ 2 ∂P) =
      ∫ x : ℝ, (fun y : ℝ => y ^ 2) x ∂P.map (X 0)
    rw [integral_map (hident 0).aemeasurable_fst (by fun_prop)]
  have hsumMem : MemLp (id : ℝ → ℝ) 2
      (standardizedSumLaw P X n) :=
    memLp_two_id_standardizedSumLaw P X hident hX0 n
  have hsumMean : ∫ x : ℝ, x ∂(standardizedSumLaw P X n) = 0 :=
    integral_id_standardizedSumLaw_eq_zero P X hident hX0 hsourceMean n
  have hsumVar : Var[(id : ℝ → ℝ); standardizedSumLaw P X n] = 1 :=
    variance_id_standardizedSumLaw_eq_one P X hindep hident hX0
      hsourceMean hsourceSecond hn
  unfold HasBerryEsseenBound normalizedRate
  by_cases hcut : universalCutoff ≤ rho / Real.sqrt (n : ℝ)
  · have huniversal := refinedUniversal_kolmogorov_bound
      (standardizedSumLaw P X n) hsumMem hsumMean hsumVar
    calc
      kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw ≤
          refinedUniversalConstant := huniversal
      _ = targetConstant044 * universalCutoff :=
        target_mul_universalCutoff.symm
      _ ≤ targetConstant044 * (rho / Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hcut (by norm_num [targetConstant044])
      _ = targetConstant044 * rho / Real.sqrt (n : ℝ) := by ring
  · have hsmall : rho / Real.sqrt (n : ℝ) < universalCutoff :=
      lt_of_not_ge hcut
    have hrhoUpper : rho ≤ ((56 : ℝ) / 45) * Real.sqrt (n : ℝ) := by
      have hcutOld : rho / Real.sqrt (n : ℝ) < (56 : ℝ) / 45 :=
        hsmall.trans universalCutoff_lt_routeBCutoff
      exact (div_lt_iff₀ hsqrt).1 hcutOld |>.le
    have hnormalized :=
      normalizedKolmogorovDistance_lt_044_of_certificates
        hfinite hsmallLower hsmallUpper hmiddle hupper
          P X hindep hident hX hmean hsecond hn
            (by simpa only [rho, mu] using hrhoUpper)
    have hfactor : 0 < Real.sqrt (n : ℝ) / rho :=
      div_pos hsqrt hrhoPos
    have hdiv :
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
          targetConstant044 / (Real.sqrt (n : ℝ) / rho) :=
      (lt_div_iff₀' hfactor).2 (by
        simpa only [rho, mu] using hnormalized)
    have heq : targetConstant044 / (Real.sqrt (n : ℝ) / rho) =
        targetConstant044 * rho / Real.sqrt (n : ℝ) := by
      field_simp
    rw [heq] at hdiv
    exact hdiv.le

end

end BerryEsseen
