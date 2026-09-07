import BerryEsseen.Interval.Large.Integral
import BerryEsseen.Interval.Prawitz.LargeNCache

/-!
# Interval / Large / Cache
-/

namespace BerryEsseen

open DyadicInterval MeasureTheory ProbabilityTheory

set_option maxRecDepth 10000

def certifiedLargeDirectCachedLowSum
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (L r : DyadicInterval) : DyadicInterval :=
  intervalFinSum (fun i =>
    let c := cache.low.get i
    DyadicInterval.mul c.wid
      (certifiedLargeDirectLowCellValue L r c))

def certifiedLargeDirectCachedFiniteBound
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (L r : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add
    (certifiedLargeDirectCachedLowSum cache L r)
    (dyadicRouteBLargeCachedHighSum cache L r)

def certifiedLargeDirectCachedFullBound
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (L r : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add
    (certifiedLargeDirectCachedFiniteBound cellCache L r)
    (dyadicRouteBLargeCachedTailValue e1Cache L r)

theorem certifiedLargeDirectCachedLowSum_eq
    {N : ℕ} {cache : DyadicRouteBCellCache N} (hcache : cache.Valid)
    (L r : DyadicInterval) :
    certifiedLargeDirectCachedLowSum cache L r =
      certifiedLargeDirectLowSum L r N := by
  unfold certifiedLargeDirectCachedLowSum
    certifiedLargeDirectLowSum
  apply intervalFinSum_eq_intervalNatSum
  intro i
  rw [hcache.low i]

theorem certifiedLargeDirectCachedFiniteBound_eq
    {N : ℕ} {cache : DyadicRouteBCellCache N} (hcache : cache.Valid)
    (L r : DyadicInterval) :
    certifiedLargeDirectCachedFiniteBound cache L r =
      certifiedLargeDirectFiniteBound L r N := by
  rw [certifiedLargeDirectCachedFiniteBound,
    certifiedLargeDirectFiniteBound,
    certifiedLargeDirectCachedLowSum_eq hcache,
    dyadicRouteBLargeCachedHighSum_eq hcache]

theorem certifiedLargeDirectCachedFullBound_eq
    {N : ℕ} {cellCache : DyadicRouteBCellCache N}
    {e1Cache : DyadicRouteBE1Cache}
    (hcell : cellCache.Valid) (he1 : e1Cache.Valid)
    (L r : DyadicInterval) :
    certifiedLargeDirectCachedFullBound cellCache e1Cache L r =
      certifiedLargeDirectFullBound L r N := by
  rw [certifiedLargeDirectCachedFullBound,
    certifiedLargeDirectFullBound,
    certifiedLargeDirectCachedFiniteBound_eq hcell,
    dyadicRouteBLargeCachedTailValue_eq he1]

def CertifiedLargeDirectCachedFullAdmissible
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (L r : DyadicInterval) : Prop :=
  CertifiedLargeBoxAdmissible L r ∧
    DyadicLargeTailAdmissible L r ∧
    (∀ i : Fin N,
      CertifiedLargeLowCellAdmissible L r (cache.low.get i)) ∧
    (∀ i : Fin N,
      DyadicLargeHighCellAdmissible L r (cache.high.get i))

instance {N : ℕ} (cache : DyadicRouteBCellCache N)
    (L r : DyadicInterval) :
    Decidable (CertifiedLargeDirectCachedFullAdmissible cache L r) := by
  unfold CertifiedLargeDirectCachedFullAdmissible
  infer_instance

theorem CertifiedLargeDirectCachedFullAdmissible.toCanonical
    {N : ℕ} {cache : DyadicRouteBCellCache N} (hcache : cache.Valid)
    {L r : DyadicInterval}
    (h : CertifiedLargeDirectCachedFullAdmissible cache L r) :
    CertifiedLargeDirectFullAdmissible L r N := by
  rcases h with ⟨hbox, htail, hlow, hhigh⟩
  refine ⟨hbox, htail, ?_, ?_⟩
  · intro i
    rw [← hcache.low i]
    exact hlow i
  · intro i
    rw [← hcache.high i]
    exact hhigh i

def certifiedLargeThreshold044 : DyadicInterval :=
  DyadicInterval.ofRat 44 100

theorem certifiedLargeThreshold044_sound :
    certifiedLargeThreshold044.Contains (44 / 100 : ℝ) := by
  simpa [certifiedLargeThreshold044] using
    DyadicInterval.contains_ofRat 44 (b := 100) (by norm_num)

def certifiedLargeDirectCachedBoxAccepted
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (L r : DyadicInterval) : Bool :=
  decide ((certifiedLargeDirectCachedFullBound
    cellCache e1Cache L r).hi < certifiedLargeThreshold044.lo) &&
  decide (CertifiedLargeDirectCachedFullAdmissible cellCache L r)

def certifiedLargeOldCachedBoxAccepted
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (L r : DyadicInterval) : Bool :=
  decide ((dyadicRouteBLargeCachedFullBound
    cellCache e1Cache L r).hi < certifiedLargeThreshold044.lo) &&
  decide (DyadicRouteBLargeCachedFullAdmissible cellCache L r)

theorem certifiedLargeDirectCachedBoxAccepted_true_iff
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (L r : DyadicInterval) :
    certifiedLargeDirectCachedBoxAccepted
        cellCache e1Cache L r = true ↔
      (certifiedLargeDirectCachedFullBound
          cellCache e1Cache L r).hi <
        certifiedLargeThreshold044.lo ∧
      CertifiedLargeDirectCachedFullAdmissible cellCache L r := by
  simp [certifiedLargeDirectCachedBoxAccepted, Bool.and_eq_true]

theorem certifiedLargeOldCachedBoxAccepted_true_iff
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (L r : DyadicInterval) :
    certifiedLargeOldCachedBoxAccepted
        cellCache e1Cache L r = true ↔
      (dyadicRouteBLargeCachedFullBound
          cellCache e1Cache L r).hi <
        certifiedLargeThreshold044.lo ∧
      DyadicRouteBLargeCachedFullAdmissible cellCache L r := by
  simp [certifiedLargeOldCachedBoxAccepted, Bool.and_eq_true]

noncomputable section

theorem normalizedKolmogorovDistance_lt_044_of_largeDirectCachedBoxAccepted
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
      (routeBSmoothingScale n
        (thirdAbsoluteMoment (P.map (X 0)))))
    (hr : r.Contains (symmetrizationRatio (P.map (X 0))))
    (haccepted : certifiedLargeDirectCachedBoxAccepted
      cellCache e1Cache L r = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  have haccepted' :=
    (certifiedLargeDirectCachedBoxAccepted_true_iff
      cellCache e1Cache L r).mp haccepted
  have hcanonical := haccepted'.2.toCanonical hcell
  have hbound :=
    normalizedKolmogorovDistance_le_certifiedLargeDirectFullBound
      P X hindep hident hX hmean hsecond hn hN hL hr hcanonical
  rw [← certifiedLargeDirectCachedFullBound_eq hcell he1] at hbound
  exact hbound.trans_lt <|
    (dyadic_upper_lt_lower_of_hi_lt_lo haccepted'.1).trans_le
      certifiedLargeThreshold044_sound.1

theorem normalizedKolmogorovDistance_lt_044_of_largeOldCachedBoxAccepted
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
      (routeBSmoothingScale n
        (thirdAbsoluteMoment (P.map (X 0)))))
    (hr : r.Contains (symmetrizationRatio (P.map (X 0))))
    (haccepted : certifiedLargeOldCachedBoxAccepted
      cellCache e1Cache L r = true) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
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
    (certifiedLargeOldCachedBoxAccepted_true_iff
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
      certifiedLargeThreshold044_sound.1
  dsimp only [rhoR, rR, zR] at hrouteBound ⊢
  exact hscaled.trans_lt (hrouteBound.trans_lt hthreshold)

end

end BerryEsseen
