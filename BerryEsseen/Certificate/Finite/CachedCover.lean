import BerryEsseen.Certificate.Finite.Cover
import BerryEsseen.Certificate.Finite.Cache
/-!
# Cached exhaustive finite-`n` cover

This is the executable finite cover used by the concrete certificate.  It is extensionally the
same checker as `DyadicPrawitzFiniteCover`, but carries the three fixed cell arrays through the
recursion so they are built once rather than once per parameter box.
-/

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 10000

structure DyadicRouteBResolutionCache where
  cells256 : DyadicRouteBCellCache 256
  cells1024 : DyadicRouteBCellCache 1024
  cells2048 : DyadicRouteBCellCache 2048
  e1 : DyadicRouteBE1Cache

def dyadicRouteBBuildResolutionCache : DyadicRouteBResolutionCache where
  cells256 := dyadicRouteBBuildCellCache 256
  cells1024 := dyadicRouteBBuildCellCache 1024
  cells2048 := dyadicRouteBBuildCellCache 2048
  e1 := dyadicRouteBBuildE1Cache

structure DyadicRouteBResolutionCache.Valid
    (cache : DyadicRouteBResolutionCache) : Prop where
  cells256 : cache.cells256.Valid
  cells1024 : cache.cells1024.Valid
  cells2048 : cache.cells2048.Valid
  e1 : cache.e1.Valid

theorem dyadicRouteBBuildResolutionCache_valid :
    dyadicRouteBBuildResolutionCache.Valid := by
  exact ⟨dyadicRouteBBuildCellCache_valid 256,
    dyadicRouteBBuildCellCache_valid 1024,
    dyadicRouteBBuildCellCache_valid 2048,
    dyadicRouteBBuildE1Cache_valid⟩

structure DyadicRouteBCachedChoice where
  N : ℕ
  cache : DyadicRouteBCellCache N
  bound : DyadicInterval

/-- Adaptive resolution selection with a shared array at every possible resolution. -/
def dyadicRouteBCachedAdaptiveChoice
    (cache : DyadicRouteBResolutionCache)
    (n : ℕ) (rho z : DyadicInterval) : DyadicRouteBCachedChoice :=
  let tail := dyadicRouteBCachedTailValue cache.e1 n rho z
  let q256 := dyadicRouteBCachedFullBoundUsingTail cache.cells256 n rho z tail
  let first : DyadicRouteBCachedChoice :=
    if dyadicRouteBRefineTo1024 q256 then
      ⟨1024, cache.cells1024,
        dyadicRouteBCachedFullBoundUsingTail cache.cells1024 n rho z tail⟩
    else
      ⟨256, cache.cells256, q256⟩
  if dyadicRouteBRefineTo2048 first.bound then
    ⟨2048, cache.cells2048,
      dyadicRouteBCachedFullBoundUsingTail cache.cells2048 n rho z tail⟩
  else
    first

theorem dyadicRouteBCachedAdaptiveChoice_cells_pos
    (cache : DyadicRouteBResolutionCache)
    (n : ℕ) (rho z : DyadicInterval) :
    0 < (dyadicRouteBCachedAdaptiveChoice cache n rho z).N := by
  simp only [dyadicRouteBCachedAdaptiveChoice]
  split_ifs <;> norm_num

theorem dyadicRouteBCachedAdaptiveChoice_valid
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    (n : ℕ) (rho z : DyadicInterval) :
    (dyadicRouteBCachedAdaptiveChoice cache n rho z).cache.Valid := by
  rcases hcache with ⟨h256, h1024, h2048, he1⟩
  unfold dyadicRouteBCachedAdaptiveChoice
  dsimp only
  by_cases hfirst : dyadicRouteBRefineTo1024
      (dyadicRouteBCachedFullBoundUsingTail cache.cells256 n rho z
        (dyadicRouteBCachedTailValue cache.e1 n rho z))
  · rw [if_pos hfirst]
    by_cases hsecond : dyadicRouteBRefineTo2048
        (dyadicRouteBCachedFullBoundUsingTail cache.cells1024 n rho z
          (dyadicRouteBCachedTailValue cache.e1 n rho z))
    · rw [if_pos hsecond]
      exact h2048
    · rw [if_neg hsecond]
      exact h1024
  · rw [if_neg hfirst]
    by_cases hsecond : dyadicRouteBRefineTo2048
        (dyadicRouteBCachedFullBoundUsingTail cache.cells256 n rho z
          (dyadicRouteBCachedTailValue cache.e1 n rho z))
    · rw [if_pos hsecond]
      exact h2048
    · rw [if_neg hsecond]
      exact h256

theorem dyadicRouteBCachedAdaptiveChoice_bound_eq
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    (n : ℕ) (rho z : DyadicInterval) :
    (dyadicRouteBCachedAdaptiveChoice cache n rho z).bound =
      dyadicRouteBFullBound n rho z
        (dyadicRouteBCachedAdaptiveChoice cache n rho z).N := by
  rcases hcache with ⟨h256, h1024, h2048, he1⟩
  unfold dyadicRouteBCachedAdaptiveChoice
  dsimp only
  by_cases hfirst : dyadicRouteBRefineTo1024
      (dyadicRouteBCachedFullBoundUsingTail cache.cells256 n rho z
        (dyadicRouteBCachedTailValue cache.e1 n rho z))
  · rw [if_pos hfirst]
    by_cases hsecond : dyadicRouteBRefineTo2048
        (dyadicRouteBCachedFullBoundUsingTail cache.cells1024 n rho z
          (dyadicRouteBCachedTailValue cache.e1 n rho z))
    · rw [if_pos hsecond]
      exact dyadicRouteBCachedFullBoundUsingTail_eq h2048 he1 rho z
    · rw [if_neg hsecond]
      exact dyadicRouteBCachedFullBoundUsingTail_eq h1024 he1 rho z
  · rw [if_neg hfirst]
    by_cases hsecond : dyadicRouteBRefineTo2048
        (dyadicRouteBCachedFullBoundUsingTail cache.cells256 n rho z
          (dyadicRouteBCachedTailValue cache.e1 n rho z))
    · rw [if_pos hsecond]
      exact dyadicRouteBCachedFullBoundUsingTail_eq h2048 he1 rho z
    · rw [if_neg hsecond]
      exact dyadicRouteBCachedFullBoundUsingTail_eq h256 he1 rho z

/-- Boolean leaf test with a shared adaptive choice. -/
def dyadicRouteBCachedFiniteBoxAccepted
    (cache : DyadicRouteBResolutionCache)
    (n : ℕ) (rho z : DyadicInterval) : Bool :=
  let choice := dyadicRouteBCachedAdaptiveChoice cache n rho z
  decide (choice.bound.hi < dyadicRouteBThreshold.lo) &&
    decide (DyadicRouteBCachedFullAdmissible choice.cache n rho z)

theorem dyadicRouteBCachedFiniteBoxAccepted_true_iff
    (cache : DyadicRouteBResolutionCache)
    (n : ℕ) (rho z : DyadicInterval) :
    dyadicRouteBCachedFiniteBoxAccepted cache n rho z = true ↔
      let choice := dyadicRouteBCachedAdaptiveChoice cache n rho z
      choice.bound.hi < dyadicRouteBThreshold.lo ∧
        DyadicRouteBCachedFullAdmissible choice.cache n rho z := by
  simp [dyadicRouteBCachedFiniteBoxAccepted, Bool.and_eq_true]

theorem routeB_normalizedRouteBU_lt_threshold_of_cachedFiniteBoxAccepted
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    {n : ℕ} (hn : 0 < n) {rho z : DyadicInterval} {rhoR zR : ℝ}
    (haccepted : dyadicRouteBCachedFiniteBoxAccepted cache n rho z = true)
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) :
    Real.sqrt (n : ℝ) / rhoR *
        routeBU routeBKappa routeBTheta n rhoR (routeBDboundR rhoR zR) <
      (4495 : ℝ) / 10000 := by
  let choice := dyadicRouteBCachedAdaptiveChoice cache n rho z
  have haccepted' : choice.bound.hi < dyadicRouteBThreshold.lo ∧
      DyadicRouteBCachedFullAdmissible choice.cache n rho z :=
    (dyadicRouteBCachedFiniteBoxAccepted_true_iff cache n rho z).mp haccepted
  have hchoiceValid : choice.cache.Valid :=
    dyadicRouteBCachedAdaptiveChoice_valid hcache n rho z
  have hcanonical := haccepted'.2.toCanonical hchoiceValid
  rcases hcanonical with ⟨hbox, htail, hlow, hhigh⟩
  have hN : 0 < choice.N :=
    dyadicRouteBCachedAdaptiveChoice_cells_pos cache n rho z
  have hbound := routeB_normalizedRouteBU_le_dyadicRouteBFullBound_upper
    hn hN hrho hz hbox
      (fun i hi => hlow ⟨i, hi⟩)
      (fun i hi => hhigh ⟨i, hi⟩) htail
  have hchoiceBound : choice.bound = dyadicRouteBFullBound n rho z choice.N :=
    dyadicRouteBCachedAdaptiveChoice_bound_eq hcache n rho z
  rw [← hchoiceBound] at hbound
  exact hbound.trans_lt <|
    (dyadic_upper_lt_lower_of_hi_lt_lo haccepted'.1).trans_le
      dyadicRouteBThreshold_contains.1

def dyadicRouteBCachedFiniteCover
    (cache : DyadicRouteBResolutionCache) (n : ℕ) :
    ℕ → DyadicInterval → DyadicInterval → Bool
  | 0, rho, z => dyadicRouteBCachedFiniteBoxAccepted cache n rho z
  | fuel + 1, rho, z =>
      if dyadicRouteBCachedFiniteBoxAccepted cache n rho z then
        true
      else if dyadicRouteBSplitRho n rho z then
        dyadicRouteBCachedFiniteCover cache n fuel (dyadicRouteBLeftHalf rho) z &&
          dyadicRouteBCachedFiniteCover cache n fuel (dyadicRouteBRightHalf rho) z
      else
        dyadicRouteBCachedFiniteCover cache n fuel rho (dyadicRouteBLeftHalf z) &&
          dyadicRouteBCachedFiniteCover cache n fuel rho (dyadicRouteBRightHalf z)

theorem dyadicRouteBCachedFiniteCover_sound
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    {n : ℕ} (hn : 0 < n) {fuel : ℕ} {rho z : DyadicInterval}
    (hcover : dyadicRouteBCachedFiniteCover cache n fuel rho z = true)
    {rhoR zR : ℝ} (hrho : rho.Contains rhoR) (hz : z.Contains zR) :
    Real.sqrt (n : ℝ) / rhoR *
        routeBU routeBKappa routeBTheta n rhoR (routeBDboundR rhoR zR) <
      (4495 : ℝ) / 10000 := by
  induction fuel generalizing rho z with
  | zero =>
      exact routeB_normalizedRouteBU_lt_threshold_of_cachedFiniteBoxAccepted
        hcache hn hcover hrho hz
  | succ fuel ih =>
      cases haccepted : dyadicRouteBCachedFiniteBoxAccepted cache n rho z with
      | true =>
          exact routeB_normalizedRouteBU_lt_threshold_of_cachedFiniteBoxAccepted
            hcache hn haccepted hrho hz
      | false =>
          by_cases hsplit : dyadicRouteBSplitRho n rho z
          · have hchildren :
              dyadicRouteBCachedFiniteCover cache n fuel
                  (dyadicRouteBLeftHalf rho) z = true ∧
                dyadicRouteBCachedFiniteCover cache n fuel
                  (dyadicRouteBRightHalf rho) z = true := by
              simpa [dyadicRouteBCachedFiniteCover, haccepted, hsplit,
                Bool.and_eq_true] using hcover
            rcases dyadicRouteB_contains_left_or_right hrho with hleft | hright
            · exact ih hchildren.1 hleft hz
            · exact ih hchildren.2 hright hz
          · have hchildren :
              dyadicRouteBCachedFiniteCover cache n fuel rho
                  (dyadicRouteBLeftHalf z) = true ∧
                dyadicRouteBCachedFiniteCover cache n fuel rho
                  (dyadicRouteBRightHalf z) = true := by
              simpa [dyadicRouteBCachedFiniteCover, haccepted, hsplit,
                Bool.and_eq_true] using hcover
            rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
            · exact ih hchildren.1 hrho hleft
            · exact ih hchildren.2 hrho hright

/-- Concrete evaluator.  The local cache value is shared through the complete recursion. -/
def dyadicRouteBCachedFiniteCertificate (n : ℕ) : Bool :=
  let cache := dyadicRouteBBuildResolutionCache
  dyadicRouteBCachedFiniteCover cache n 30
    (dyadicRouteBFiniteRootRho n) dyadicRouteBFiniteRootZ

theorem routeB_normalizedRouteBU_lt_threshold_of_cachedFiniteCertificate
    {n : ℕ} (hn : 0 < n)
    (hcertificate : dyadicRouteBCachedFiniteCertificate n = true)
    {rho z : ℝ} (hrhoLower : 1 ≤ rho)
    (hrhoUpper : rho ≤ ((56 : ℝ) / 45) * Real.sqrt (n : ℝ))
    (hzLower : 0 ≤ z) (hzUpper : z ≤ 1) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho z) <
      (4495 : ℝ) / 10000 := by
  exact dyadicRouteBCachedFiniteCover_sound
    dyadicRouteBBuildResolutionCache_valid hn hcertificate
    (dyadicRouteBFiniteRootRho_contains hrhoLower hrhoUpper)
    (dyadicRouteBFiniteRootZ_contains hzLower hzUpper)

end BerryEsseen
