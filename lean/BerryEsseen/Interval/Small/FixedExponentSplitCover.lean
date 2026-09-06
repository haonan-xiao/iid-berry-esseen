import BerryEsseen.Interval.Small.FixedExponentCover

/-!
# Interval / Small / Fixed Exponent Split Cover
-/

namespace BerryEsseen

open DyadicInterval MeasureTheory ProbabilityTheory

set_option maxRecDepth 10000

def certifiedLargeSmallLowerRootZ : DyadicInterval :=
  ⟨0, (DyadicInterval.ofRat 9 10).hi⟩

def certifiedLargeSmallUpperRootZ : DyadicInterval :=
  ⟨(DyadicInterval.ofRat 9 10).hi, dyadicScale⟩

def certifiedLargeSmallRefinedLeafCodeCertificateAt
    (extraFuel : ℕ) (code : String)
    (xRoot zRoot : DyadicInterval) : Bool :=
  match dyadicRouteBLargeLeafTreeOfCode code with
  | some tree => certifiedLargeSmallVerifyLeafTreeWithRefinement
      extraFuel tree xRoot zRoot
  | none => false

noncomputable section

theorem normalizedKolmogorovDistance_lt_044_of_largeSmallRefinedLeafCodeCertificateAt
    {extraFuel : ℕ} {code : String} {xRoot zRoot : DyadicInterval}
    (hcertificate : certifiedLargeSmallRefinedLeafCodeCertificateAt
      extraFuel code xRoot zRoot = true)
    {xR zR : ℝ} (hx : xRoot.Contains xR) (hz : zRoot.Contains zR)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 100 ≤ n)
    (hL : routeBLargeSmallRegionL xR =
      routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0))))
    (hr : routeBLargeSmallRegionR zR =
      symmetrizationRatio (P.map (X 0))) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  unfold certifiedLargeSmallRefinedLeafCodeCertificateAt at hcertificate
  split at hcertificate
  next tree htree =>
    exact certifiedLargeSmallVerifyLeafTreeWithRefinement_sound
      hcertificate hx hz P X hindep hident hX hmean hsecond hn hL hr
  next => simp at hcertificate

theorem normalizedKolmogorovDistance_lt_044_of_largeSmallSplitCertificates
    {lowerFuel upperFuel : ℕ} {code : String}
    (hlowerCertificate : certifiedLargeSmallRefinedLeafCodeCertificateAt
      lowerFuel code dyadicRouteBUnitInterval
        certifiedLargeSmallLowerRootZ = true)
    (hupperCertificate : certifiedLargeSmallRefinedLeafCodeCertificateAt
      upperFuel code dyadicRouteBUnitInterval
        certifiedLargeSmallUpperRootZ = true)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 100 ≤ n)
    (hLupper : routeBSmoothingScale n
      (thirdAbsoluteMoment (P.map (X 0))) ≤ (1 : ℝ) / 16) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  let mu := P.map (X 0)
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let eta := rho * (r - 1)
  let xR := routeBLargeSmallX n rho
  let zR := routeBLargeSmallZ rho eta
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
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
  have hx0 : 0 ≤ xR := routeBLargeSmallX_nonnegative hnPos hrhoPos
  have hx1 : xR ≤ 1 := by
    dsimp only [xR, rho, mu]
    exact routeBLargeSmallX_le_one hLupper
  have hz0 : 0 ≤ zR := routeBLargeSmallZ_nonnegative hrho heta0
  have hz1 : zR ≤ 1 := routeBLargeSmallZ_le_one hrho heta1
  have hxContains : dyadicRouteBUnitInterval.Contains xR :=
    dyadicRouteBUnitInterval_contains hx0 hx1
  have hregionL : routeBLargeSmallRegionL xR =
      routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0))) := by
    dsimp only [xR, rho, mu]
    exact routeBLargeSmallL_inverse _
  have hrouteR : routeBDboundR rho eta = r := by
    simpa only [eta] using routeBDboundR_mul_excess hrhoPos.ne'
  have hregionR : routeBLargeSmallRegionR zR =
      symmetrizationRatio (P.map (X 0)) := by
    dsimp only [zR]
    rw [routeBLargeSmallR_inverse hrhoPos, hrouteR]
  let zCut : ℝ :=
    ((DyadicInterval.ofRat 9 10).hi : ℝ) / (dyadicScale : ℝ)
  by_cases hzCut : zR ≤ zCut
  · have hzContains : certifiedLargeSmallLowerRootZ.Contains zR := by
      simp only [certifiedLargeSmallLowerRootZ,
        DyadicInterval.Contains, Set.mem_Icc, DyadicInterval.lower,
        DyadicInterval.upper]
      exact ⟨by simpa using hz0, by simpa only [zCut] using hzCut⟩
    exact normalizedKolmogorovDistance_lt_044_of_largeSmallRefinedLeafCodeCertificateAt
      hlowerCertificate hxContains hzContains P X hindep hident hX hmean
        hsecond hn hregionL hregionR
  · have hzContains : certifiedLargeSmallUpperRootZ.Contains zR := by
      simp only [certifiedLargeSmallUpperRootZ,
        DyadicInterval.Contains, Set.mem_Icc, DyadicInterval.lower,
        DyadicInterval.upper]
      exact ⟨by simpa only [zCut] using le_of_not_ge hzCut,
        by simpa [dyadicScale_pos.ne'] using hz1⟩
    exact normalizedKolmogorovDistance_lt_044_of_largeSmallRefinedLeafCodeCertificateAt
      hupperCertificate hxContains hzContains P X hindep hident hX hmean
        hsecond hn hregionL hregionR

end

end BerryEsseen
