import BerryEsseen.Interval.Finite.TargetBound

/-!
# Interval / Finite / Adaptive
-/

namespace BerryEsseen

open MeasureTheory ProbabilityTheory DyadicInterval

set_option maxRecDepth 10000

def bound4395FiniteAcceptedAt
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (n : ℕ) (rho z : DyadicInterval) : Bool :=
  let bound := certifiedCachedFullBound cellCache e1Cache n rho z
  decide (bound.hi < bound4395FiniteThreshold.lo) &&
    decide (CertifiedCachedFullAdmissible cellCache n rho z)

theorem bound4395FiniteAcceptedAt_true_iff
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (n : ℕ) (rho z : DyadicInterval) :
    bound4395FiniteAcceptedAt cellCache e1Cache n rho z = true ↔
      (certifiedCachedFullBound cellCache e1Cache n rho z).hi <
          bound4395FiniteThreshold.lo ∧
        CertifiedCachedFullAdmissible cellCache n rho z := by
  simp [bound4395FiniteAcceptedAt, Bool.and_eq_true]

noncomputable section

theorem normalizedKolmogorovDistance_lt_879_2000_of_post044FiniteAcceptedAt
    {N : ℕ} {cellCache : DyadicRouteBCellCache N}
    {e1Cache : DyadicRouteBE1Cache}
    (hcell : cellCache.Valid) (he1 : e1Cache.Valid)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) (hN : 0 < N)
    {rho z : DyadicInterval}
    (haccepted : bound4395FiniteAcceptedAt
      cellCache e1Cache n rho z = true)
    (hrho : rho.Contains (thirdAbsoluteMoment (P.map (X 0))))
    (hz : z.Contains
      (thirdAbsoluteMoment (P.map (X 0)) *
        (symmetrizationRatio (P.map (X 0)) - 1))) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  have haccepted' :=
    (bound4395FiniteAcceptedAt_true_iff
      cellCache e1Cache n rho z).mp haccepted
  have hcanonical := haccepted'.2.toCanonical hcell
  rcases hcanonical with ⟨hbox, htail, hlow, hhigh⟩
  have hbound := normalizedKolmogorovDistance_le_certifiedFullBound
    P X hindep hident hX hmean hsecond hn hN hrho hz hbox
      hlow hhigh htail
  rw [← certifiedCachedFullBound_eq hcell he1] at hbound
  exact hbound.trans_lt <|
    (dyadic_upper_lt_lower_of_hi_lt_lo haccepted'.1).trans_le
      bound4395FiniteThreshold_contains.1

end

def bound4395FiniteTargetAwareAccepted
    (cache : DyadicRouteBResolutionCache)
    (n : ℕ) (rho z : DyadicInterval) : Bool :=
  bound4395FiniteAcceptedAt cache.cells256 cache.e1 n rho z ||
    bound4395FiniteAcceptedAt cache.cells1024 cache.e1 n rho z ||
    bound4395FiniteAcceptedAt cache.cells2048 cache.e1 n rho z

noncomputable section

theorem normalizedKolmogorovDistance_lt_879_2000_of_post044FiniteTargetAware
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) {rho z : DyadicInterval}
    (haccepted : bound4395FiniteTargetAwareAccepted cache n rho z = true)
    (hrho : rho.Contains (thirdAbsoluteMoment (P.map (X 0))))
    (hz : z.Contains
      (thirdAbsoluteMoment (P.map (X 0)) *
        (symmetrizationRatio (P.map (X 0)) - 1))) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  by_cases h256 : bound4395FiniteAcceptedAt
      cache.cells256 cache.e1 n rho z = true
  · exact
      normalizedKolmogorovDistance_lt_879_2000_of_post044FiniteAcceptedAt
        hcache.cells256 hcache.e1 P X hindep hident hX hmean hsecond
          hn (by norm_num) h256 hrho hz
  · by_cases h1024 : bound4395FiniteAcceptedAt
        cache.cells1024 cache.e1 n rho z = true
    · exact
        normalizedKolmogorovDistance_lt_879_2000_of_post044FiniteAcceptedAt
          hcache.cells1024 hcache.e1 P X hindep hident hX hmean hsecond
            hn (by norm_num) h1024 hrho hz
    · have h2048 : bound4395FiniteAcceptedAt
          cache.cells2048 cache.e1 n rho z = true := by
        simpa [bound4395FiniteTargetAwareAccepted, h256, h1024]
          using haccepted
      exact
        normalizedKolmogorovDistance_lt_879_2000_of_post044FiniteAcceptedAt
          hcache.cells2048 hcache.e1 P X hindep hident hX hmean hsecond
            hn (by norm_num) h2048 hrho hz

end

end BerryEsseen
