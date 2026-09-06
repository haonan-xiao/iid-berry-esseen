import BerryEsseen.Interval.Finite.Functional
import BerryEsseen.DyadicPrawitzFiniteCachedCover

namespace BerryEsseen

open MeasureTheory ProbabilityTheory DyadicInterval

set_option maxRecDepth 10000

def certifiedCachedLowSum
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (n : ℕ) (rho z : DyadicInterval) : DyadicInterval :=
  intervalFinSum (fun i =>
    let c := cache.low.get i
    DyadicInterval.mul c.wid
      (certifiedSharedLowCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c))

def certifiedCachedHighSum
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (n : ℕ) (rho z : DyadicInterval) : DyadicInterval :=
  intervalFinSum (fun i =>
    let c := cache.high.get i
    DyadicInterval.mul c.wid
      (certifiedSharedHighCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c))

def certifiedCachedFiniteBound
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (n : ℕ) (rho z : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add (certifiedCachedLowSum cache n rho z)
    (certifiedCachedHighSum cache n rho z)

def certifiedCachedFullBoundUsingTail
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (n : ℕ) (rho z tail : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add (certifiedCachedFiniteBound cache n rho z) tail

def certifiedCachedFullBound
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (n : ℕ) (rho z : DyadicInterval) : DyadicInterval :=
  certifiedCachedFullBoundUsingTail cellCache n rho z
    (dyadicRouteBCachedTailValue e1Cache n rho z)

theorem certifiedCachedLowSum_eq
    {N n : ℕ} {cache : DyadicRouteBCellCache N}
    (hcache : cache.Valid) (rho z : DyadicInterval) :
    certifiedCachedLowSum cache n rho z =
      certifiedLowSum n rho z N := by
  unfold certifiedCachedLowSum certifiedLowSum
  apply intervalFinSum_eq_intervalNatSum
  intro i
  rw [hcache.low i]

theorem certifiedCachedHighSum_eq
    {N n : ℕ} {cache : DyadicRouteBCellCache N}
    (hcache : cache.Valid) (rho z : DyadicInterval) :
    certifiedCachedHighSum cache n rho z =
      certifiedHighSum n rho z N := by
  unfold certifiedCachedHighSum certifiedHighSum
  apply intervalFinSum_eq_intervalNatSum
  intro i
  rw [hcache.high i]

theorem certifiedCachedFiniteBound_eq
    {N n : ℕ} {cache : DyadicRouteBCellCache N}
    (hcache : cache.Valid) (rho z : DyadicInterval) :
    certifiedCachedFiniteBound cache n rho z =
      certifiedFiniteBound n rho z N := by
  rw [certifiedCachedFiniteBound, certifiedFiniteBound,
    certifiedCachedLowSum_eq hcache,
    certifiedCachedHighSum_eq hcache]

theorem certifiedCachedFullBoundUsingTail_eq
    {N n : ℕ} {cellCache : DyadicRouteBCellCache N}
    {e1Cache : DyadicRouteBE1Cache}
    (hcell : cellCache.Valid) (he1 : e1Cache.Valid)
    (rho z : DyadicInterval) :
    certifiedCachedFullBoundUsingTail cellCache n rho z
        (dyadicRouteBCachedTailValue e1Cache n rho z) =
      certifiedFullBound n rho z N := by
  rw [certifiedCachedFullBoundUsingTail, certifiedFullBound,
    certifiedCachedFiniteBound_eq hcell,
    dyadicRouteBCachedTailValue_eq he1]

theorem certifiedCachedFullBound_eq
    {N n : ℕ} {cellCache : DyadicRouteBCellCache N}
    {e1Cache : DyadicRouteBE1Cache}
    (hcell : cellCache.Valid) (he1 : e1Cache.Valid)
    (rho z : DyadicInterval) :
    certifiedCachedFullBound cellCache e1Cache n rho z =
      certifiedFullBound n rho z N := by
  exact certifiedCachedFullBoundUsingTail_eq hcell he1 rho z

def CertifiedCachedFullAdmissible
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (n : ℕ) (rho z : DyadicInterval) : Prop :=
  DyadicRouteBBoxAdmissible rho z ∧
    DyadicRouteBTailAdmissible n rho z ∧
    (∀ i : Fin N,
      CertifiedLowCellAdmissible n rho z (cache.low.get i)) ∧
    (∀ i : Fin N,
      CertifiedHighCellAdmissible n rho z (cache.high.get i))

instance {N : ℕ} (cache : DyadicRouteBCellCache N)
    (n : ℕ) (rho z : DyadicInterval) :
    Decidable (CertifiedCachedFullAdmissible cache n rho z) := by
  unfold CertifiedCachedFullAdmissible
  infer_instance

theorem CertifiedCachedFullAdmissible.toCanonical
    {N n : ℕ} {cache : DyadicRouteBCellCache N}
    (hcache : cache.Valid) {rho z : DyadicInterval}
    (h : CertifiedCachedFullAdmissible cache n rho z) :
    DyadicRouteBBoxAdmissible rho z ∧
      DyadicRouteBTailAdmissible n rho z ∧
      (∀ i < N,
        CertifiedLowCellAdmissible n rho z
          (dyadicRouteBLowCell N i)) ∧
      (∀ i < N,
        CertifiedHighCellAdmissible n rho z
          (dyadicRouteBHighCell N i)) := by
  rcases h with ⟨hbox, htail, hlow, hhigh⟩
  refine ⟨hbox, htail, ?_, ?_⟩
  · intro i hi
    rw [← hcache.low ⟨i, hi⟩]
    exact hlow ⟨i, hi⟩
  · intro i hi
    rw [← hcache.high ⟨i, hi⟩]
    exact hhigh ⟨i, hi⟩

def certifiedThreshold044 : DyadicInterval :=
  DyadicInterval.ofRat 44 100

theorem certifiedThreshold044_contains :
    certifiedThreshold044.Contains ((44 : ℝ) / 100) := by
  exact DyadicInterval.contains_ofRat 44 (b := 100) (by norm_num)

structure CertifiedCachedChoice where
  N : ℕ
  cache : DyadicRouteBCellCache N
  bound : DyadicInterval

def certifiedCachedAdaptiveChoice
    (cache : DyadicRouteBResolutionCache)
    (n : ℕ) (rho z : DyadicInterval) : CertifiedCachedChoice :=
  let tail := dyadicRouteBCachedTailValue cache.e1 n rho z
  let q256 := certifiedCachedFullBoundUsingTail
    cache.cells256 n rho z tail
  if q256.hi < certifiedThreshold044.lo then
    ⟨256, cache.cells256, q256⟩
  else
    let q1024 := certifiedCachedFullBoundUsingTail
      cache.cells1024 n rho z tail
    if q1024.hi < certifiedThreshold044.lo then
      ⟨1024, cache.cells1024, q1024⟩
    else
      ⟨2048, cache.cells2048,
        certifiedCachedFullBoundUsingTail
          cache.cells2048 n rho z tail⟩

theorem certifiedCachedAdaptiveChoice_cells_pos
    (cache : DyadicRouteBResolutionCache)
    (n : ℕ) (rho z : DyadicInterval) :
    0 < (certifiedCachedAdaptiveChoice cache n rho z).N := by
  simp only [certifiedCachedAdaptiveChoice]
  split_ifs <;> norm_num

theorem certifiedCachedAdaptiveChoice_valid
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    (n : ℕ) (rho z : DyadicInterval) :
    (certifiedCachedAdaptiveChoice cache n rho z).cache.Valid := by
  rcases hcache with ⟨h256, h1024, h2048, he1⟩
  unfold certifiedCachedAdaptiveChoice
  dsimp only
  by_cases hfirst :
      (certifiedCachedFullBoundUsingTail cache.cells256 n rho z
        (dyadicRouteBCachedTailValue cache.e1 n rho z)).hi <
          certifiedThreshold044.lo
  · rw [if_pos hfirst]
    exact h256
  · rw [if_neg hfirst]
    by_cases hsecond :
        (certifiedCachedFullBoundUsingTail cache.cells1024 n rho z
          (dyadicRouteBCachedTailValue cache.e1 n rho z)).hi <
            certifiedThreshold044.lo
    · rw [if_pos hsecond]
      exact h1024
    · rw [if_neg hsecond]
      exact h2048

theorem certifiedCachedAdaptiveChoice_bound_eq
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    (n : ℕ) (rho z : DyadicInterval) :
    (certifiedCachedAdaptiveChoice cache n rho z).bound =
      certifiedFullBound n rho z
        (certifiedCachedAdaptiveChoice cache n rho z).N := by
  rcases hcache with ⟨h256, h1024, h2048, he1⟩
  unfold certifiedCachedAdaptiveChoice
  dsimp only
  by_cases hfirst :
      (certifiedCachedFullBoundUsingTail cache.cells256 n rho z
        (dyadicRouteBCachedTailValue cache.e1 n rho z)).hi <
          certifiedThreshold044.lo
  · rw [if_pos hfirst]
    exact certifiedCachedFullBoundUsingTail_eq h256 he1 rho z
  · rw [if_neg hfirst]
    by_cases hsecond :
        (certifiedCachedFullBoundUsingTail cache.cells1024 n rho z
          (dyadicRouteBCachedTailValue cache.e1 n rho z)).hi <
            certifiedThreshold044.lo
    · rw [if_pos hsecond]
      exact certifiedCachedFullBoundUsingTail_eq h1024 he1 rho z
    · rw [if_neg hsecond]
      exact certifiedCachedFullBoundUsingTail_eq h2048 he1 rho z

def certifiedCachedFiniteBoxAccepted
    (cache : DyadicRouteBResolutionCache)
    (n : ℕ) (rho z : DyadicInterval) : Bool :=
  let choice := certifiedCachedAdaptiveChoice cache n rho z
  decide (choice.bound.hi < certifiedThreshold044.lo) &&
    decide (CertifiedCachedFullAdmissible choice.cache n rho z)

theorem certifiedCachedFiniteBoxAccepted_true_iff
    (cache : DyadicRouteBResolutionCache)
    (n : ℕ) (rho z : DyadicInterval) :
    certifiedCachedFiniteBoxAccepted cache n rho z = true ↔
      let choice := certifiedCachedAdaptiveChoice cache n rho z
      choice.bound.hi < certifiedThreshold044.lo ∧
        CertifiedCachedFullAdmissible choice.cache n rho z := by
  simp [certifiedCachedFiniteBoxAccepted, Bool.and_eq_true]

theorem normalizedKolmogorovDistance_lt_044_of_cachedFiniteBoxAccepted
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
    (haccepted :
      certifiedCachedFiniteBoxAccepted cache n rho z = true)
    (hrho : rho.Contains (thirdAbsoluteMoment (P.map (X 0))))
    (hz : z.Contains
      (thirdAbsoluteMoment (P.map (X 0)) *
        (symmetrizationRatio (P.map (X 0)) - 1))) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  let choice := certifiedCachedAdaptiveChoice cache n rho z
  have haccepted' : choice.bound.hi < certifiedThreshold044.lo ∧
      CertifiedCachedFullAdmissible choice.cache n rho z :=
    (certifiedCachedFiniteBoxAccepted_true_iff cache n rho z).mp
      haccepted
  have hchoiceValid : choice.cache.Valid :=
    certifiedCachedAdaptiveChoice_valid hcache n rho z
  have hcanonical := haccepted'.2.toCanonical hchoiceValid
  rcases hcanonical with ⟨hbox, htail, hlow, hhigh⟩
  have hN : 0 < choice.N :=
    certifiedCachedAdaptiveChoice_cells_pos cache n rho z
  have hbound := normalizedKolmogorovDistance_le_certifiedFullBound
    P X hindep hident hX hmean hsecond hn hN hrho hz hbox
      hlow hhigh htail
  have hchoiceBound : choice.bound =
      certifiedFullBound n rho z choice.N :=
    certifiedCachedAdaptiveChoice_bound_eq hcache n rho z
  rw [← hchoiceBound] at hbound
  exact hbound.trans_lt <|
    (dyadic_upper_lt_lower_of_hi_lt_lo haccepted'.1).trans_le
      certifiedThreshold044_contains.1

/-- Depth-bounded certified cover for the complete finite-`n` parameter box.  Unlike the
discovery checker, every accepted node rechecks both the strict `0.44` endpoint inequality and
all arithmetic side conditions used by the analytic proof. -/
def certifiedCachedFiniteCover
    (cache : DyadicRouteBResolutionCache) (n : ℕ) :
    ℕ → DyadicInterval → DyadicInterval → Bool
  | 0, rho, z => certifiedCachedFiniteBoxAccepted cache n rho z
  | fuel + 1, rho, z =>
      if certifiedCachedFiniteBoxAccepted cache n rho z then
        true
      else if dyadicRouteBSplitRho n rho z then
        certifiedCachedFiniteCover cache n fuel
              (dyadicRouteBLeftHalf rho) z &&
          certifiedCachedFiniteCover cache n fuel
              (dyadicRouteBRightHalf rho) z
      else
        certifiedCachedFiniteCover cache n fuel rho
              (dyadicRouteBLeftHalf z) &&
          certifiedCachedFiniteCover cache n fuel rho
              (dyadicRouteBRightHalf z)

theorem certifiedCachedFiniteCover_sound
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) {fuel : ℕ} {rho z : DyadicInterval}
    (hcover : certifiedCachedFiniteCover cache n fuel rho z = true)
    (hrho : rho.Contains (thirdAbsoluteMoment (P.map (X 0))))
    (hz : z.Contains
      (thirdAbsoluteMoment (P.map (X 0)) *
        (symmetrizationRatio (P.map (X 0)) - 1))) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  induction fuel generalizing rho z with
  | zero =>
      exact normalizedKolmogorovDistance_lt_044_of_cachedFiniteBoxAccepted
        hcache P X hindep hident hX hmean hsecond hn hcover hrho hz
  | succ fuel ih =>
      cases haccepted : certifiedCachedFiniteBoxAccepted cache n rho z with
      | true =>
          exact normalizedKolmogorovDistance_lt_044_of_cachedFiniteBoxAccepted
            hcache P X hindep hident hX hmean hsecond hn haccepted hrho hz
      | false =>
          by_cases hsplit : dyadicRouteBSplitRho n rho z
          · have hchildren :
                certifiedCachedFiniteCover cache n fuel
                    (dyadicRouteBLeftHalf rho) z = true ∧
                  certifiedCachedFiniteCover cache n fuel
                    (dyadicRouteBRightHalf rho) z = true := by
              simpa [certifiedCachedFiniteCover, haccepted, hsplit,
                Bool.and_eq_true] using hcover
            rcases dyadicRouteB_contains_left_or_right hrho with hleft | hright
            · exact ih hchildren.1 hleft hz
            · exact ih hchildren.2 hright hz
          · have hchildren :
                certifiedCachedFiniteCover cache n fuel rho
                    (dyadicRouteBLeftHalf z) = true ∧
                  certifiedCachedFiniteCover cache n fuel rho
                    (dyadicRouteBRightHalf z) = true := by
              simpa [certifiedCachedFiniteCover, haccepted, hsplit,
                Bool.and_eq_true] using hcover
            rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
            · exact ih hchildren.1 hrho hleft
            · exact ih hchildren.2 hrho hright

/-- Concrete exhaustive finite-`n` certificate.  The cache is built once and shared through the
entire cover recursion. -/
def certifiedCachedFiniteCertificate (n : ℕ) : Bool :=
  let cache := dyadicRouteBBuildResolutionCache
  certifiedCachedFiniteCover cache n 30
    (dyadicRouteBFiniteRootRho n) dyadicRouteBFiniteRootZ

theorem normalizedKolmogorovDistance_lt_044_of_cachedFiniteCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n)
    (hcertificate : certifiedCachedFiniteCertificate n = true)
    (hrhoLower : 1 ≤ thirdAbsoluteMoment (P.map (X 0)))
    (hrhoUpper : thirdAbsoluteMoment (P.map (X 0)) ≤
      ((56 : ℝ) / 45) * Real.sqrt (n : ℝ))
    (hzLower : 0 ≤ thirdAbsoluteMoment (P.map (X 0)) *
      (symmetrizationRatio (P.map (X 0)) - 1))
    (hzUpper : thirdAbsoluteMoment (P.map (X 0)) *
      (symmetrizationRatio (P.map (X 0)) - 1) ≤ 1) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  exact certifiedCachedFiniteCover_sound
    dyadicRouteBBuildResolutionCache_valid P X hindep hident hX hmean hsecond
      hn hcertificate
      (dyadicRouteBFiniteRootRho_contains hrhoLower hrhoUpper)
      (dyadicRouteBFiniteRootZ_contains hzLower hzUpper)

end BerryEsseen
