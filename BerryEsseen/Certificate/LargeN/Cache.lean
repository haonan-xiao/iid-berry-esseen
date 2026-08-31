import BerryEsseen.Certificate.LargeN.Tail
import BerryEsseen.Certificate.Finite.Cache
import BerryEsseen.Certificate.Finite.Cover
/-!
# Cached direct large-`n` Route B evaluator

The direct large-`n` certificate reuses the same parameter-independent
Prawitz cells and `E1up` table at every parameter box.  This module gives the
Lean checker that sharing without changing the canonical exact dyadic bound.
-/

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 10000

def dyadicRouteBLargeCachedLowSum
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (L r : DyadicInterval) : DyadicInterval :=
  intervalFinSum (fun i =>
    let c := cache.low.get i
    DyadicInterval.mul c.wid (dyadicLargeLowCellValue L r c))

def dyadicRouteBLargeCachedHighSum
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (L r : DyadicInterval) : DyadicInterval :=
  intervalFinSum (fun i =>
    let c := cache.high.get i
    DyadicInterval.mul c.wid (dyadicLargeHighCellValue L r c))

def dyadicRouteBLargeCachedFiniteBound
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (L r : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add (dyadicRouteBLargeCachedLowSum cache L r)
    (dyadicRouteBLargeCachedHighSum cache L r)

def dyadicRouteBLargeCachedTailValue
    (cache : DyadicRouteBE1Cache)
    (L r : DyadicInterval) : DyadicInterval :=
  DyadicInterval.div
    (dyadicRouteBCachedE1Up cache (dyadicRouteBLargeTailX L r))
    (dyadicRouteBLargeTailDen L)

def dyadicRouteBLargeCachedFullBound
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (L r : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add (dyadicRouteBLargeCachedFiniteBound cellCache L r)
    (dyadicRouteBLargeCachedTailValue e1Cache L r)

theorem dyadicRouteBLargeCachedLowSum_eq
    {N : ℕ} {cache : DyadicRouteBCellCache N} (hcache : cache.Valid)
    (L r : DyadicInterval) :
    dyadicRouteBLargeCachedLowSum cache L r =
      dyadicRouteBLargeLowSum L r N := by
  unfold dyadicRouteBLargeCachedLowSum dyadicRouteBLargeLowSum
  apply intervalFinSum_eq_intervalNatSum
  intro i
  rw [hcache.low i]

theorem dyadicRouteBLargeCachedHighSum_eq
    {N : ℕ} {cache : DyadicRouteBCellCache N} (hcache : cache.Valid)
    (L r : DyadicInterval) :
    dyadicRouteBLargeCachedHighSum cache L r =
      dyadicRouteBLargeHighSum L r N := by
  unfold dyadicRouteBLargeCachedHighSum dyadicRouteBLargeHighSum
  apply intervalFinSum_eq_intervalNatSum
  intro i
  rw [hcache.high i]

theorem dyadicRouteBLargeCachedFiniteBound_eq
    {N : ℕ} {cache : DyadicRouteBCellCache N} (hcache : cache.Valid)
    (L r : DyadicInterval) :
    dyadicRouteBLargeCachedFiniteBound cache L r =
      dyadicRouteBLargeFiniteBound L r N := by
  rw [dyadicRouteBLargeCachedFiniteBound, dyadicRouteBLargeFiniteBound,
    dyadicRouteBLargeCachedLowSum_eq hcache,
    dyadicRouteBLargeCachedHighSum_eq hcache]

theorem dyadicRouteBLargeCachedTailValue_eq
    {cache : DyadicRouteBE1Cache} (hcache : cache.Valid)
    (L r : DyadicInterval) :
    dyadicRouteBLargeCachedTailValue cache L r =
      dyadicRouteBLargeTailValue L r := by
  rw [dyadicRouteBLargeCachedTailValue, dyadicRouteBLargeTailValue,
    dyadicRouteBCachedE1Up_eq hcache]

theorem dyadicRouteBLargeCachedFullBound_eq
    {N : ℕ} {cellCache : DyadicRouteBCellCache N}
    {e1Cache : DyadicRouteBE1Cache}
    (hcell : cellCache.Valid) (he1 : e1Cache.Valid)
    (L r : DyadicInterval) :
    dyadicRouteBLargeCachedFullBound cellCache e1Cache L r =
      dyadicRouteBLargeFullBound L r N := by
  rw [dyadicRouteBLargeCachedFullBound, dyadicRouteBLargeFullBound,
    dyadicRouteBLargeCachedFiniteBound_eq hcell,
    dyadicRouteBLargeCachedTailValue_eq he1]

def DyadicRouteBLargeCachedFullAdmissible
    {N : ℕ} (cache : DyadicRouteBCellCache N)
    (L r : DyadicInterval) : Prop :=
  DyadicLargeBoxAdmissible L r ∧
    DyadicLargeTailAdmissible L r ∧
    (∀ i : Fin N,
      DyadicLargeLowCellAdmissible L r (cache.low.get i)) ∧
    (∀ i : Fin N,
      DyadicLargeHighCellAdmissible L r (cache.high.get i))

instance {N : ℕ} (cache : DyadicRouteBCellCache N)
    (L r : DyadicInterval) :
    Decidable (DyadicRouteBLargeCachedFullAdmissible cache L r) := by
  unfold DyadicRouteBLargeCachedFullAdmissible
  infer_instance

theorem DyadicRouteBLargeCachedFullAdmissible.toCanonical
    {N : ℕ} {cache : DyadicRouteBCellCache N} (hcache : cache.Valid)
    {L r : DyadicInterval}
    (h : DyadicRouteBLargeCachedFullAdmissible cache L r) :
    DyadicRouteBLargeFullAdmissible L r N := by
  rcases h with ⟨hbox, htail, hlow, hhigh⟩
  refine ⟨hbox, htail, ?_, ?_⟩
  · intro i
    rw [← hcache.low i]
    exact hlow i
  · intro i
    rw [← hcache.high i]
    exact hhigh i

/-- A fixed-resolution leaf test.  The threshold comparison and every
division/ordering side condition are exact integer decisions. -/
def dyadicRouteBLargeCachedBoxAccepted
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (L r : DyadicInterval) : Bool :=
  decide ((dyadicRouteBLargeCachedFullBound cellCache e1Cache L r).hi <
    dyadicRouteBThreshold.lo) &&
  decide (DyadicRouteBLargeCachedFullAdmissible cellCache L r)

theorem dyadicRouteBLargeCachedBoxAccepted_true_iff
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (L r : DyadicInterval) :
    dyadicRouteBLargeCachedBoxAccepted cellCache e1Cache L r = true ↔
      (dyadicRouteBLargeCachedFullBound cellCache e1Cache L r).hi <
          dyadicRouteBThreshold.lo ∧
        DyadicRouteBLargeCachedFullAdmissible cellCache L r := by
  simp [dyadicRouteBLargeCachedBoxAccepted, Bool.and_eq_true]

noncomputable section

theorem routeB_normalizedRouteBU_lt_threshold_of_largeCachedBoxAccepted
    {N n : ℕ} {cellCache : DyadicRouteBCellCache N}
    {e1Cache : DyadicRouteBE1Cache}
    (hcell : cellCache.Valid) (he1 : e1Cache.Valid)
    (hn : 100 ≤ n) (hN : 0 < N)
    {rho z : ℝ} {L r : DyadicInterval}
    (hrho1 : 1 ≤ rho) (hz0 : 0 ≤ z)
    (hL : L.Contains (routeBSmoothingScale n rho))
    (hr : r.Contains (routeBDboundR rho z))
    (haccepted :
      dyadicRouteBLargeCachedBoxAccepted cellCache e1Cache L r = true) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho z) <
      (4495 : ℝ) / 10000 := by
  have haccepted' :=
    (dyadicRouteBLargeCachedBoxAccepted_true_iff
      cellCache e1Cache L r).mp haccepted
  have hcanonical := haccepted'.2.toCanonical hcell
  have hbound :=
    routeB_normalizedRouteBU_le_dyadicRouteBLargeFullBound_upper_of_admissible
      hn hN hrho1 hz0 hL hr hcanonical
  rw [← dyadicRouteBLargeCachedFullBound_eq hcell he1] at hbound
  exact hbound.trans_lt <|
    (dyadic_upper_lt_lower_of_hi_lt_lo haccepted'.1).trans_le
      dyadicRouteBThreshold_contains.1

end

end BerryEsseen
