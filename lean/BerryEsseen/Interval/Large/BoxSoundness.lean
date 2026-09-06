import BerryEsseen.Interval.Large.Cover
import BerryEsseen.Smoothing.SmallParameterBoundary

/-!
# Interval / Large / Box Soundness
-/

namespace BerryEsseen

open DyadicInterval MeasureTheory ProbabilityTheory

set_option maxRecDepth 10000

def bound4395LargeDirectCachedBoxAccepted
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (L r : DyadicInterval) : Bool :=
  decide ((certifiedLargeDirectCachedFullBound
    cellCache e1Cache L r).hi < bound4395Threshold.lo) &&
  decide (CertifiedLargeDirectCachedFullAdmissible cellCache L r)

def bound4395LargeOldCachedBoxAccepted
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (L r : DyadicInterval) : Bool :=
  decide ((dyadicRouteBLargeCachedFullBound
    cellCache e1Cache L r).hi < bound4395Threshold.lo) &&
  decide (DyadicRouteBLargeCachedFullAdmissible cellCache L r)

theorem bound4395LargeDirectCachedBoxAccepted_true_iff
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache) (L r : DyadicInterval) :
    bound4395LargeDirectCachedBoxAccepted cellCache e1Cache L r = true ↔
      (certifiedLargeDirectCachedFullBound
          cellCache e1Cache L r).hi < bound4395Threshold.lo ∧
        CertifiedLargeDirectCachedFullAdmissible cellCache L r := by
  simp [bound4395LargeDirectCachedBoxAccepted, Bool.and_eq_true]

theorem bound4395LargeOldCachedBoxAccepted_true_iff
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache) (L r : DyadicInterval) :
    bound4395LargeOldCachedBoxAccepted cellCache e1Cache L r = true ↔
      (dyadicRouteBLargeCachedFullBound
          cellCache e1Cache L r).hi < bound4395Threshold.lo ∧
        DyadicRouteBLargeCachedFullAdmissible cellCache L r := by
  simp [bound4395LargeOldCachedBoxAccepted, Bool.and_eq_true]

noncomputable section

theorem normalizedKolmogorovDistance_lt_879_2000_of_post044LargeDirectBox
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {N n : ℕ} {cellCache : DyadicRouteBCellCache N}
    {e1Cache : DyadicRouteBE1Cache}
    (hcell : cellCache.Valid) (he1 : e1Cache.Valid)
    (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0)))))
    (hr : r.Contains (symmetrizationRatio (P.map (X 0))))
    (haccepted : bound4395LargeDirectCachedBoxAccepted
      cellCache e1Cache L r = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  have haccepted' :=
    (bound4395LargeDirectCachedBoxAccepted_true_iff
      cellCache e1Cache L r).mp haccepted
  have hcanonical := haccepted'.2.toCanonical hcell
  have hbound :=
    normalizedKolmogorovDistance_le_certifiedLargeDirectFullBound
      P X hindep hident hX hmean hsecond hn hN hL hr hcanonical
  rw [← certifiedLargeDirectCachedFullBound_eq hcell he1] at hbound
  exact hbound.trans_lt <|
    (dyadic_upper_lt_lower_of_hi_lt_lo haccepted'.1).trans_le
      bound4395Threshold_contains.1

theorem normalizedKolmogorovDistance_lt_879_2000_of_post044LargeOldBox
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {N n : ℕ} {cellCache : DyadicRouteBCellCache N}
    {e1Cache : DyadicRouteBE1Cache}
    (hcell : cellCache.Valid) (he1 : e1Cache.Valid)
    (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0)))))
    (hr : r.Contains (symmetrizationRatio (P.map (X 0))))
    (haccepted : bound4395LargeOldCachedBoxAccepted
      cellCache e1Cache L r = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  letI : IsProbabilityMeasure (P.map (X 0)) :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  let rhoR := thirdAbsoluteMoment (P.map (X 0))
  let rR := symmetrizationRatio (P.map (X 0))
  let zR := rhoR * (rR - 1)
  have hnOne : 1 ≤ n := by omega
  have hrho : 1 ≤ rhoR := by
    dsimp only [rhoR]
    exact thirdAbsoluteMoment_ge_one (P.map (X 0)) hX hsecond
  have hrhoPos : 0 < rhoR := zero_lt_one.trans_le hrho
  have hrOne : 1 ≤ rR := by
    dsimp only [rR]
    exact symmetrizationRatio_lower (P.map (X 0)) hX hmean hsecond
  have hz0 : 0 ≤ zR := by
    dsimp only [zR]
    exact mul_nonneg (zero_le_one.trans hrho) (sub_nonneg.mpr hrOne)
  have hrouteR : routeBDboundR rhoR zR = rR := by
    simpa only [zR] using routeBDboundR_mul_excess hrhoPos.ne'
  have haccepted' :=
    (bound4395LargeOldCachedBoxAccepted_true_iff
      cellCache e1Cache L r).mp haccepted
  have hcanonical := haccepted'.2.toCanonical hcell
  have hrouteBound :=
    routeB_normalizedRouteBU_le_dyadicRouteBLargeFullBound_upper_of_admissible
      hn hN hrho hz0 hL (by simpa only [hrouteR] using hr) hcanonical
  rw [← dyadicRouteBLargeCachedFullBound_eq hcell he1] at hrouteBound
  rw [hrouteR] at hrouteBound
  have hkol := kolmogorovDistance_standardizedSum_le_exactRouteBU
    P X hindep hident hX hmean hsecond hnOne
  have hscale : 0 ≤ Real.sqrt (n : ℝ) / rhoR := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hkol hscale
  dsimp only [rhoR, rR] at hscaled
  have hthreshold :=
    (dyadic_upper_lt_lower_of_hi_lt_lo haccepted'.1).trans_le
      bound4395Threshold_contains.1
  dsimp only [rhoR, rR, zR] at hrouteBound ⊢
  exact hscaled.trans_lt (hrouteBound.trans_lt hthreshold)

end

def bound4395LargeHybridCachedBoxAccepted
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (L r : DyadicInterval) : Bool :=
  if (DyadicInterval.ofRat 19 10).hi ≤ r.lo then
    bound4395LargeDirectCachedBoxAccepted cellCache e1Cache L r
  else
    bound4395LargeOldCachedBoxAccepted cellCache e1Cache L r

theorem bound4395LargeHybridCachedBoxAccepted_LPos
    {N : ℕ} {cellCache : DyadicRouteBCellCache N}
    {e1Cache : DyadicRouteBE1Cache} {L r : DyadicInterval}
    (haccepted : bound4395LargeHybridCachedBoxAccepted
      cellCache e1Cache L r = true) :
    0 < L.lo := by
  by_cases hnew : (DyadicInterval.ofRat 19 10).hi ≤ r.lo
  · have hacc : bound4395LargeDirectCachedBoxAccepted
        cellCache e1Cache L r = true := by
      simpa [bound4395LargeHybridCachedBoxAccepted, hnew] using haccepted
    exact ((bound4395LargeDirectCachedBoxAccepted_true_iff
      cellCache e1Cache L r).mp hacc).2.1.toDyadicLargeBoxAdmissible.LPos
  · have hacc : bound4395LargeOldCachedBoxAccepted
        cellCache e1Cache L r = true := by
      simpa [bound4395LargeHybridCachedBoxAccepted, hnew] using haccepted
    exact ((bound4395LargeOldCachedBoxAccepted_true_iff
      cellCache e1Cache L r).mp hacc).2.1.LPos

noncomputable section

theorem normalizedKolmogorovDistance_lt_879_2000_of_post044LargeHybridBox
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {N n : ℕ} {cellCache : DyadicRouteBCellCache N}
    {e1Cache : DyadicRouteBE1Cache}
    (hcell : cellCache.Valid) (he1 : e1Cache.Valid)
    (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0)))))
    (hr : r.Contains (symmetrizationRatio (P.map (X 0))))
    (haccepted : bound4395LargeHybridCachedBoxAccepted
      cellCache e1Cache L r = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  by_cases hnew : (DyadicInterval.ofRat 19 10).hi ≤ r.lo
  · have hacc : bound4395LargeDirectCachedBoxAccepted
        cellCache e1Cache L r = true := by
      simpa [bound4395LargeHybridCachedBoxAccepted, hnew] using haccepted
    exact normalizedKolmogorovDistance_lt_879_2000_of_post044LargeDirectBox
      P X hindep hident hX hmean hsecond hcell he1 hn hN hL hr hacc
  · have hacc : bound4395LargeOldCachedBoxAccepted
        cellCache e1Cache L r = true := by
      simpa [bound4395LargeHybridCachedBoxAccepted, hnew] using haccepted
    exact normalizedKolmogorovDistance_lt_879_2000_of_post044LargeOldBox
      P X hindep hident hX hmean hsecond hcell he1 hn hN hL hr hacc

end

end BerryEsseen
