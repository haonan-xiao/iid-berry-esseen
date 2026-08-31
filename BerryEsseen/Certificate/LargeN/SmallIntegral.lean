import BerryEsseen.Certificate.LargeN.SmallCell
/-!
# Endpoint-regular large-`n` Darboux integral

This module applies the exact `y ∈ [0,4]` cells to the original normalized
Prawitz integrands.  The changes of variables `t = L*y` and `t = 1 - L*y`
are performed inside Lean; the auxiliary endpoint envelopes need not be
declared integrable.
-/

open MeasureTheory intervalIntegral

namespace BerryEsseen

open DyadicInterval

noncomputable section

theorem routeBNormalizedEndpointIntegrals_le_dyadicRouteBLargeSmallFiniteSum_upper
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {rho z : ℝ} (hrho1 : 1 ≤ rho) (hz0 : 0 ≤ z)
    {L r : DyadicInterval}
    (hL : L.Contains (routeBSmoothingScale n rho))
    (hr : r.Contains (routeBDboundR rho z))
    (hbox : DyadicLargeSmallBoxAdmissible L r)
    (hadmissible : ∀ i < N, DyadicLargeSmallCellAdmissible L r
      (dyadicRouteBLargeSmallYCell N i)) :
    (∫ t in (0 : ℝ)..4 * routeBSmoothingScale n rho,
        routeBNormalizedLowIntegrand n rho z t) +
      (∫ t in 1 - 4 * routeBSmoothingScale n rho..(1 : ℝ),
        routeBNormalizedHighIntegrand n rho z t) ≤
      (dyadicRouteBLargeSmallFiniteSum L r N).upper := by
  let LR := routeBSmoothingScale n rho
  let rR := routeBDboundR rho z
  let low := routeBNormalizedLowIntegrand n rho z
  let high := routeBNormalizedHighIntegrand n rho z
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  have hLR : 0 < LR := by
    dsimp only [LR]
    exact routeBSmoothingScale_pos hnPos hrhoPos
  have hLu : LR ≤ 1 / 16 := by
    dsimp only [LR]
    exact hbox.real_L_le_sixteenth hL
  have hfour : 4 * LR ≤ 1 / 4 := by nlinarith
  have hfourSplit : 4 * LR ≤ prawitzSplit := by
    norm_num [prawitzSplit] at hfour ⊢
    linarith
  have hLowBase : IntervalIntegrable low volume 0 prawitzSplit := by
    dsimp only [low]
    exact intervalIntegrable_routeBNormalizedLowIntegrand hnPos hrhoPos hz0
  have hLowRestricted : IntervalIntegrable low volume 0 (LR * 4) := by
    apply IntervalIntegrable.mono hLowBase
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc ?_) le_rfl
    exact Set.mem_uIcc_of_le (by positivity) (by simpa [mul_comm] using hfourSplit)
  have hLowComp : IntervalIntegrable
      (fun y => LR * low (LR * y)) volume 0 4 := by
    have hcomp := hLowRestricted.comp_mul_left (c := LR)
    have hscaled := hcomp.const_mul LR
    simpa [hLR.ne'] using hscaled
  have hhighLeft : prawitzSplit ≤ 1 - LR * 4 := by
    norm_num [prawitzSplit] at hfour ⊢
    nlinarith
  have hHighBase : IntervalIntegrable high volume prawitzSplit 1 := by
    dsimp only [high]
    exact intervalIntegrable_routeBNormalizedHighIntegrand n hrhoPos hz0
  have hHighRestricted : IntervalIntegrable high volume (1 - LR * 4) 1 := by
    apply IntervalIntegrable.mono hHighBase
      (Set.uIcc_subset_uIcc ?_ Set.right_mem_uIcc) le_rfl
    exact Set.mem_uIcc_of_le hhighLeft (by nlinarith [hLR.le])
  have hHighComp : IntervalIntegrable
      (fun y => LR * high (1 - LR * y)) volume 0 4 := by
    have hsub := (hHighRestricted.comp_sub_left 1).symm
    have hcomp := hsub.comp_mul_left (c := LR)
    have hscaled := hcomp.const_mul LR
    simpa [hLR.ne'] using hscaled
  let f : ℝ → ℝ := fun y =>
    LR * low (LR * y) + LR * high (1 - LR * y)
  have hf : IntervalIntegrable f volume 0 4 := by
    dsimp only [f]
    exact hLowComp.add hHighComp
  have hdom : ∀ y ∈ Set.Icc (0 : ℝ) 4,
      f y ≤ routeBLargeSmallIntegrand LR rR y := by
    intro y hy
    have hlo := routeBNormalizedLow_mul_scale_le_largeSmallLow
      hn hrho1 hz0 (by simpa only [LR] using hLu) hy.1 hy.2
    have hhi := routeBNormalizedHigh_mul_scale_le_largeSmallF2
      hn hrho1 hz0 (by simpa only [LR] using hLu) hy.1 hy.2
    dsimp only [f, LR, rR, low, high]
    exact add_le_add hlo hhi
  have hbound := intervalIntegral_le_dyadicRouteBLargeSmallFiniteSum_upper
    hN hL hr hbox hLR hf hdom hadmissible
  have hLowChange :
      (∫ y in (0 : ℝ)..4, LR * low (LR * y)) =
        ∫ t in (0 : ℝ)..LR * 4, low t := by
    rw [intervalIntegral.integral_const_mul]
    simpa [smul_eq_mul] using
      (intervalIntegral.smul_integral_comp_mul_left
        (f := low) (a := (0 : ℝ)) (b := (4 : ℝ)) LR)
  have hHighChange :
      (∫ y in (0 : ℝ)..4, LR * high (1 - LR * y)) =
        ∫ t in 1 - LR * 4..(1 : ℝ), high t := by
    rw [intervalIntegral.integral_const_mul]
    simpa [smul_eq_mul] using
      (intervalIntegral.smul_integral_comp_sub_mul
        (f := high) (a := (0 : ℝ)) (b := (4 : ℝ)) LR 1)
  rw [show (∫ y in (0 : ℝ)..4, f y) =
      (∫ y in (0 : ℝ)..4, LR * low (LR * y)) +
        (∫ y in (0 : ℝ)..4, LR * high (1 - LR * y)) by
        dsimp only [f]
        exact intervalIntegral.integral_add hLowComp hHighComp,
    hLowChange, hHighChange] at hbound
  simpa only [LR, rR, low, high, mul_comm] using hbound

end

end BerryEsseen
