import BerryEsseen.Smoothing.PrawitzLargeNSmallOmission
/-!
# Complete endpoint-regular large-`n` bound

This module combines the exact `y ∈ [0,4]` Darboux sum with the analytic
omission bounds.  The result is the soundness theorem for the supplied
checker's `tail_small` value, including its exact `3e-11` allowance.
-/

open MeasureTheory intervalIntegral Set

namespace BerryEsseen

open DyadicInterval

noncomputable section

theorem routeB_normalizedRouteBU_le_dyadicRouteBLargeSmallBound_upper
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {rho eta : ℝ} (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    {L r : DyadicInterval}
    (hL : L.Contains (routeBSmoothingScale n rho))
    (hr : r.Contains (routeBDboundR rho eta))
    (hbox : DyadicLargeSmallBoxAdmissible L r)
    (hadmissible : ∀ i < N, DyadicLargeSmallCellAdmissible L r
      (dyadicRouteBLargeSmallYCell N i)) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho eta) ≤
      (dyadicRouteBLargeSmallBound L r N).upper := by
  let LR := routeBSmoothingScale n rho
  let low : ℝ → ℝ := routeBNormalizedLowIntegrand n rho eta
  let high : ℝ → ℝ := routeBNormalizedHighIntegrand n rho eta
  let tail : ℝ := Real.sqrt (n : ℝ) / rho *
    (routeBE1 (routeBTailArgument n rho eta) / (2 * Real.pi))
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  have hLR : 0 < LR := routeBSmoothingScale_pos hnPos hrhoPos
  have hLRu : LR ≤ (1 : ℝ) / 16 := by
    dsimp only [LR]
    exact hbox.real_L_le_sixteenth hL
  have hfourSplit : 4 * LR ≤ prawitzSplit := by
    have hquarter : 4 * LR ≤ (1 : ℝ) / 4 := by nlinarith
    norm_num [prawitzSplit] at hquarter ⊢
    linarith
  have hhighCut : (3 : ℝ) / 4 ≤ 1 - 4 * LR := by nlinarith

  have hLowBase : IntervalIntegrable low volume 0 prawitzSplit := by
    dsimp only [low]
    exact intervalIntegrable_routeBNormalizedLowIntegrand hnPos hrhoPos heta0
  have hLowFinite : IntervalIntegrable low volume 0 (4 * LR) := by
    apply IntervalIntegrable.mono hLowBase
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc ?_) le_rfl
    exact Set.mem_uIcc_of_le (by positivity) hfourSplit
  have hLowOmit : IntervalIntegrable low volume (4 * LR) prawitzSplit := by
    apply IntervalIntegrable.mono hLowBase
      (Set.uIcc_subset_uIcc ?_ Set.right_mem_uIcc) le_rfl
    exact Set.mem_uIcc_of_le (by positivity) hfourSplit
  have hLowSplit := intervalIntegral.integral_add_adjacent_intervals
    hLowFinite hLowOmit

  have hHighBase : IntervalIntegrable high volume prawitzSplit 1 := by
    dsimp only [high]
    exact intervalIntegrable_routeBNormalizedHighIntegrand n hrhoPos heta0
  have hHighMiddle : IntervalIntegrable high volume prawitzSplit ((3 : ℝ) / 4) := by
    apply IntervalIntegrable.mono hHighBase
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc ?_) le_rfl
    exact Set.mem_uIcc_of_le (by norm_num [prawitzSplit]) (by norm_num)
  have hHighRest : IntervalIntegrable high volume ((3 : ℝ) / 4) 1 := by
    apply IntervalIntegrable.mono hHighBase
      (Set.uIcc_subset_uIcc ?_ Set.right_mem_uIcc) le_rfl
    exact Set.mem_uIcc_of_le (by norm_num [prawitzSplit]) (by norm_num)
  have hHighOmit : IntervalIntegrable high volume
      ((3 : ℝ) / 4) (1 - 4 * LR) := by
    apply IntervalIntegrable.mono hHighBase
      (Set.uIcc_subset_uIcc ?_ ?_) le_rfl
    · exact Set.mem_uIcc_of_le (by norm_num [prawitzSplit]) (by norm_num)
    · have hlower : prawitzSplit ≤ 1 - 4 * LR :=
        (by norm_num [prawitzSplit] : prawitzSplit ≤ (3 : ℝ) / 4).trans hhighCut
      have hupper : 1 - 4 * LR ≤ (1 : ℝ) := by
        have : 0 ≤ 4 * LR := by positivity
        linarith
      exact Set.mem_uIcc_of_le hlower hupper
  have hHighFinite : IntervalIntegrable high volume (1 - 4 * LR) 1 := by
    apply IntervalIntegrable.mono hHighBase
      (Set.uIcc_subset_uIcc ?_ Set.right_mem_uIcc) le_rfl
    have hlower : prawitzSplit ≤ 1 - 4 * LR :=
      (by norm_num [prawitzSplit] : prawitzSplit ≤ (3 : ℝ) / 4).trans hhighCut
    have hupper : 1 - 4 * LR ≤ (1 : ℝ) := by
      have : 0 ≤ 4 * LR := by positivity
      linarith
    exact Set.mem_uIcc_of_le hlower hupper
  have hHighSplit := intervalIntegral.integral_add_adjacent_intervals
    hHighMiddle hHighRest
  have hHighRestSplit := intervalIntegral.integral_add_adjacent_intervals
    hHighOmit hHighFinite

  have hfinite :=
    routeBNormalizedEndpointIntegrals_le_dyadicRouteBLargeSmallFiniteSum_upper
      hn hN hrho1 heta0 hL hr hbox hadmissible
  have hlowOmission := routeBNormalizedLow_omission_le
    hn hrho1 heta0 heta1 (by simpa only [LR] using hLRu)
  have hmiddleOmission := routeBNormalizedHigh_middle_omission_le
    hn hrho1 heta0 heta1 (by simpa only [LR] using hLRu)
  have hendpointOmission := routeBNormalizedHigh_endpoint_omission_le
    hn hrho1 heta0 heta1 (by simpa only [LR] using hLRu)
  have htailOmission := routeBNormalizedE1Tail_small_le
    hn hrho1 heta0 heta1 (by simpa only [LR] using hLRu)
  have homissionContains : dyadicRouteBLargeSmallOmission.Contains
      ((3 : ℝ) / 100000000000) := by
    simpa [dyadicRouteBLargeSmallOmission] using
      DyadicInterval.contains_ofRat 3 (b := 100000000000) (by norm_num)
  have homissionBudget : (16 : ℝ) / 1000000000000 ≤
      dyadicRouteBLargeSmallOmission.upper := by
    exact (by norm_num : (16 : ℝ) / 1000000000000 ≤
      3 / 100000000000).trans homissionContains.2
  have hfinite' :
      (∫ t in (0 : ℝ)..4 * LR, low t) +
          (∫ t in 1 - 4 * LR..(1 : ℝ), high t) ≤
        (dyadicRouteBLargeSmallFiniteSum L r N).upper := by
    simpa only [LR, low, high] using hfinite
  have hlowOmission' :
      (∫ t in 4 * LR..prawitzSplit, low t) ≤
        (13 : ℝ) / 1000000000000 := by
    simpa only [LR, low] using hlowOmission
  have hmiddleOmission' :
      (∫ t in prawitzSplit..(3 : ℝ) / 4, high t) ≤
        (1 : ℝ) / 1000000000000 := by
    simpa only [high] using hmiddleOmission
  have hendpointOmission' :
      (∫ t in (3 : ℝ) / 4..1 - 4 * LR, high t) ≤
        (1 : ℝ) / 1000000000000 := by
    simpa only [LR, high] using hendpointOmission
  have htailOmission' : tail ≤ (1 : ℝ) / 1000000000000 := by
    simpa only [tail] using htailOmission

  rw [routeB_normalizedRouteBU_eq_finiteIntegrals_add_tail
      hnPos hrhoPos heta0,
    routeB_normalizedGaussianTail_eq hnPos hrhoPos heta0]
  change ((∫ t in (0 : ℝ)..prawitzSplit, low t) +
      ∫ t in prawitzSplit..(1 : ℝ), high t) + tail ≤ _
  rw [← hLowSplit, ← hHighSplit, ← hHighRestSplit]
  have htotal :
      (((∫ t in (0 : ℝ)..4 * LR, low t) +
          ∫ t in 4 * LR..prawitzSplit, low t) +
        ((∫ t in prawitzSplit..(3 : ℝ) / 4, high t) +
          ((∫ t in (3 : ℝ) / 4..1 - 4 * LR, high t) +
            ∫ t in 1 - 4 * LR..(1 : ℝ), high t))) + tail ≤
        (dyadicRouteBLargeSmallFiniteSum L r N).upper +
          dyadicRouteBLargeSmallOmission.upper := by
    linarith
  have haddUpper : (dyadicRouteBLargeSmallBound L r N).upper =
      (dyadicRouteBLargeSmallFiniteSum L r N).upper +
        dyadicRouteBLargeSmallOmission.upper := by
    simp [dyadicRouteBLargeSmallBound, DyadicInterval.add,
      DyadicInterval.upper, Int.cast_add, add_div]
  rw [haddUpper]
  exact htotal

end

end BerryEsseen
