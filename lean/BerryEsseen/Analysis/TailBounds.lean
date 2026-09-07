import BerryEsseen.Analysis.ExponentialBounds
import BerryEsseen.Interval.Prawitz.LargeNSmallTail

/-!
# Analysis / Tail Bounds
-/

namespace BerryEsseen

open MeasureTheory ProbabilityTheory intervalIntegral

noncomputable section

theorem refinedRouteBNormalizedLow_omission_le
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hLupper : routeBSmoothingScale n rho ≤ 1 / 16) :
    (∫ t in 4 * routeBSmoothingScale n rho..prawitzSplit,
      routeBNormalizedLowIntegrand n rho eta t) ≤
        (13 : ℝ) / 1000000000000 := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  let L := routeBSmoothingScale n rho
  let b := prawitzSplit / L
  let low : ℝ → ℝ := routeBNormalizedLowIntegrand n rho eta
  have hL : 0 < L := routeBSmoothingScale_pos hnPos hrhoPos
  have hfourL : L * 4 ≤ prawitzSplit := by
    have : L * 4 ≤ (1 / 16 : ℝ) * 4 :=
      mul_le_mul_of_nonneg_right (by simpa only [L] using hLupper) (by norm_num)
    norm_num [prawitzSplit] at this ⊢
    linarith
  have hLb : L * b = prawitzSplit := by
    dsimp only [b]
    field_simp [hL.ne']
  have hb : 4 ≤ b := by
    apply (le_div_iff₀ hL).2
    simpa [mul_comm] using hfourL
  have hbase : IntervalIntegrable low volume 0 prawitzSplit := by
    dsimp only [low]
    exact intervalIntegrable_routeBNormalizedLowIntegrand hnPos hrhoPos heta0
  have hrestricted : IntervalIntegrable low volume (L * 4) prawitzSplit := by
    apply IntervalIntegrable.mono hbase
      (Set.uIcc_subset_uIcc ?_ Set.right_mem_uIcc) le_rfl
    exact Set.mem_uIcc_of_le (by positivity) hfourL
  have hcomp : IntervalIntegrable (fun y => L * low (L * y)) volume 4 b := by
    have hraw := hrestricted.comp_mul_left (c := L)
    have hscaled := hraw.const_mul L
    have hleft : L * 4 / L = (4 : ℝ) := by field_simp [hL.ne']
    simpa only [hleft, b] using hscaled
  have hgauss : IntervalIntegrable
      (fun y : ℝ => 856 * y ^ 2 * Real.exp (-2 * y ^ 2)) volume 4 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hdom : ∀ y ∈ Set.Icc (4 : ℝ) b,
      L * low (L * y) ≤ 856 * y ^ 2 * Real.exp (-2 * y ^ 2) := by
    intro y hy
    have ht : routeBSmoothingScale n rho * y ≤ prawitzSplit := by
      calc
        routeBSmoothingScale n rho * y ≤
            routeBSmoothingScale n rho * b :=
          mul_le_mul_of_nonneg_left hy.2 hL.le
        _ = prawitzSplit := by simpa only [L] using hLb
    simpa only [L, low] using
      routeBNormalizedLow_low_tail_pointwise hn hrho1 heta0 heta1 hy.1 ht
  have hmono :
      (∫ y in (4 : ℝ)..b, L * low (L * y)) ≤
        ∫ y in (4 : ℝ)..b,
          856 * y ^ 2 * Real.exp (-2 * y ^ 2) :=
    intervalIntegral.integral_mono_on hb hcomp hgauss hdom
  have hchange :
      (∫ y in (4 : ℝ)..b, L * low (L * y)) =
        ∫ t in L * 4..prawitzSplit, low t := by
    rw [intervalIntegral.integral_const_mul]
    have hraw := intervalIntegral.smul_integral_comp_mul_left
      (f := low) (a := (4 : ℝ)) (b := b) L
    rw [hLb] at hraw
    simpa [smul_eq_mul] using hraw
  have hgaussTail := intervalIntegral_sq_mul_exp_neg_two_sq_le hb
  calc
    (∫ t in 4 * routeBSmoothingScale n rho..prawitzSplit,
        routeBNormalizedLowIntegrand n rho eta t) =
        ∫ t in L * 4..prawitzSplit, low t := by
      simp only [L, low, mul_comm]
    _ = ∫ y in (4 : ℝ)..b, L * low (L * y) := hchange.symm
    _ ≤ ∫ y in (4 : ℝ)..b,
          856 * y ^ 2 * Real.exp (-2 * y ^ 2) := hmono
    _ = 856 * (∫ y in (4 : ℝ)..b,
          y ^ 2 * Real.exp (-2 * y ^ 2)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _
      ring
    _ ≤ 856 * (65 / 64 * Real.exp (-32)) :=
      mul_le_mul_of_nonneg_left hgaussTail (by norm_num)
    _ ≤ 856 * (65 / 64 * ((1 : ℝ) / 70000000000000)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left expNegThirtyTwoLe (by norm_num)) (by norm_num)
    _ ≤ (13 : ℝ) / 1000000000000 := by norm_num

theorem refinedRouteBNormalizedHigh_middle_omission_le
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hLupper : routeBSmoothingScale n rho ≤ 1 / 16) :
    (∫ t in prawitzSplit..(3 : ℝ) / 4,
      routeBNormalizedHighIntegrand n rho eta t) ≤
        (1 : ℝ) / 1000000000000 := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  let L := routeBSmoothingScale n rho
  let r := routeBDboundR rho eta
  let high : ℝ → ℝ := routeBNormalizedHighIntegrand n rho eta
  have hL : 0 < L := routeBSmoothingScale_pos hnPos hrhoPos
  have hr1 : 1 ≤ r := by
    dsimp only [r]
    rw [routeBDboundR_eq_one_add hrhoPos.ne']
    exact le_add_of_nonneg_right (div_nonneg heta0 hrhoPos.le)
  have hr2 : r ≤ 2 := by
    dsimp only [r]
    rw [routeBDboundR_eq_one_add hrhoPos.ne']
    have hetaRho : eta ≤ rho := heta1.trans hrho1
    have hquot : eta / rho ≤ 1 := (div_le_one hrhoPos).2 hetaRho
    linarith
  have hpoint : ∀ t ∈ Set.Icc prawitzSplit ((3 : ℝ) / 4),
      high t ≤ (1 : ℝ) / 1000000000000 := by
    intro t ht
    have hlarge := routeBNormalizedHigh_le_largeIntegrand
      (rho := rho) (r := r) (t := t) hn hrho1 hr1
        ((by norm_num [prawitzSplit] : (0 : ℝ) ≤ prawitzSplit).trans ht.1)
    have hlarge' : high t ≤ routeBLargeHighIntegrand L r t := by
      simpa [high, L, r, routeBNormalizedHighIntegrand] using hlarge
    have hbound := routeBLargeHigh_middle_pointwise hL
      (by simpa only [L] using hLupper) hr1 hr2 ht.1 ht.2
    have hexpMon : Real.exp (-48) ≤ Real.exp (-32) :=
      Real.exp_le_exp.mpr (by norm_num)
    calc
      high t ≤ routeBLargeHighIntegrand L r t := hlarge'
      _ ≤ (200 / 19 : ℝ) * Real.exp (-48) := hbound
      _ ≤ (200 / 19 : ℝ) * Real.exp (-32) :=
        mul_le_mul_of_nonneg_left hexpMon (by norm_num)
      _ ≤ (200 / 19 : ℝ) * ((1 : ℝ) / 70000000000000) :=
        mul_le_mul_of_nonneg_left expNegThirtyTwoLe (by norm_num)
      _ ≤ (1 : ℝ) / 1000000000000 := by norm_num
  have hhigh : IntervalIntegrable high volume prawitzSplit ((3 : ℝ) / 4) := by
    have hbase := intervalIntegrable_routeBNormalizedHighIntegrand n hrhoPos heta0
    apply IntervalIntegrable.mono hbase
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc ?_) le_rfl
    exact Set.mem_uIcc_of_le (by norm_num [prawitzSplit]) (by norm_num)
  have hconst : IntervalIntegrable
      (fun _ : ℝ => (1 : ℝ) / 1000000000000) volume
      prawitzSplit ((3 : ℝ) / 4) :=
    continuous_const.intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on
    (by norm_num [prawitzSplit]) hhigh hconst hpoint
  calc
    (∫ t in prawitzSplit..(3 : ℝ) / 4,
        routeBNormalizedHighIntegrand n rho eta t) =
        ∫ t in prawitzSplit..(3 : ℝ) / 4, high t := by rfl
    _ ≤ ∫ _t in prawitzSplit..(3 : ℝ) / 4,
          (1 : ℝ) / 1000000000000 := hmono
    _ ≤ (1 : ℝ) / 1000000000000 := by
      norm_num [prawitzSplit]

theorem refinedRouteBNormalizedHigh_endpoint_omission_le
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hLupper : routeBSmoothingScale n rho ≤ 1 / 16) :
    (∫ t in (3 : ℝ) / 4..1 - 4 * routeBSmoothingScale n rho,
      routeBNormalizedHighIntegrand n rho eta t) ≤
        (1 : ℝ) / 1000000000000 := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  let L := routeBSmoothingScale n rho
  let b := 1 / (4 * L)
  let high : ℝ → ℝ := routeBNormalizedHighIntegrand n rho eta
  have hL : 0 < L := routeBSmoothingScale_pos hnPos hrhoPos
  have h16L : 16 * L ≤ 1 := by
    have hLu : L ≤ (1 : ℝ) / 16 := by simpa only [L] using hLupper
    nlinarith
  have hLb : L * b = (1 : ℝ) / 4 := by
    dsimp only [b]
    field_simp [hL.ne']
  have hb : 4 ≤ b := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hL)).2
    nlinarith
  have hinterval : (3 : ℝ) / 4 ≤ 1 - 4 * L := by nlinarith
  have hbase : IntervalIntegrable high volume prawitzSplit 1 := by
    dsimp only [high]
    exact intervalIntegrable_routeBNormalizedHighIntegrand n hrhoPos heta0
  have hrestricted : IntervalIntegrable high volume
      ((3 : ℝ) / 4) (1 - 4 * L) := by
    apply IntervalIntegrable.mono hbase
      (Set.uIcc_subset_uIcc ?_ ?_) le_rfl
    · exact Set.mem_uIcc_of_le (by norm_num [prawitzSplit]) (by norm_num)
    · have hsplit : prawitzSplit ≤ (3 : ℝ) / 4 := by
        norm_num [prawitzSplit]
      have hlower : prawitzSplit ≤ 1 - 4 * L := hsplit.trans hinterval
      have hupper : 1 - 4 * L ≤ (1 : ℝ) := by
        have hfour0 : 0 ≤ 4 * L := by positivity
        linarith
      exact Set.mem_uIcc_of_le hlower hupper
  have hcomp : IntervalIntegrable
      (fun y => L * high (1 - L * y)) volume 4 b := by
    have hsub := (hrestricted.comp_sub_left 1).symm
    have hraw := hsub.comp_mul_left (c := L)
    have hscaled := hraw.const_mul L
    have hleft : (1 - (1 - 4 * L)) / L = (4 : ℝ) := by
      field_simp [hL.ne']
      ring
    have hright : (1 - (3 : ℝ) / 4) / L = b := by
      dsimp only [b]
      ring
    simpa only [hleft, hright] using hscaled
  have hgauss : IntervalIntegrable
      (fun y : ℝ => 4 * Real.exp (-2 * y ^ 2)) volume 4 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hdom : ∀ y ∈ Set.Icc (4 : ℝ) b,
      L * high (1 - L * y) ≤ 4 * Real.exp (-2 * y ^ 2) := by
    intro y hy
    have hLy : routeBSmoothingScale n rho * y ≤ (1 : ℝ) / 4 := by
      calc
        routeBSmoothingScale n rho * y ≤
            routeBSmoothingScale n rho * b :=
          mul_le_mul_of_nonneg_left hy.2 hL.le
        _ = (1 : ℝ) / 4 := by simpa only [L] using hLb
    simpa only [L, high] using routeBNormalizedHigh_endpoint_pointwise
      hn hrho1 heta0 heta1 (by linarith [hy.1]) hLy
  have hmono := intervalIntegral.integral_mono_on hb hcomp hgauss hdom
  have hchange :
      (∫ y in (4 : ℝ)..b, L * high (1 - L * y)) =
        ∫ t in (3 : ℝ) / 4..1 - L * 4, high t := by
    rw [intervalIntegral.integral_const_mul]
    have hraw := intervalIntegral.smul_integral_comp_sub_mul
      (f := high) (a := (4 : ℝ)) (b := b) L 1
    rw [hLb] at hraw
    rw [show 1 - (1 : ℝ) / 4 = 3 / 4 by norm_num] at hraw
    simpa [smul_eq_mul] using hraw
  have htail := intervalIntegral_four_exp_neg_two_sq_le hb
  calc
    (∫ t in (3 : ℝ) / 4..1 - 4 * routeBSmoothingScale n rho,
        routeBNormalizedHighIntegrand n rho eta t) =
        ∫ t in (3 : ℝ) / 4..1 - L * 4, high t := by
      simp only [L, high, mul_comm]
    _ = ∫ y in (4 : ℝ)..b, L * high (1 - L * y) := hchange.symm
    _ ≤ ∫ y in (4 : ℝ)..b, 4 * Real.exp (-2 * y ^ 2) := hmono
    _ ≤ 65 / 256 * Real.exp (-32) := htail
    _ ≤ 65 / 256 * ((1 : ℝ) / 70000000000000) :=
      mul_le_mul_of_nonneg_left expNegThirtyTwoLe (by norm_num)
    _ ≤ (1 : ℝ) / 1000000000000 := by norm_num

theorem refinedRouteBLargeTailValue_small_le
    {L r : ℝ} (hL : 0 < L) (hLu : L ≤ 1 / 16)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
    routeBLargeTailValue L r ≤ (1 : ℝ) / 1000000000000 := by
  let x := routeBLargeTailArgument L r
  have hxLower : (160 : ℝ) ≤ x :=
    routeBLargeTailArgument_ge_one_sixty hL hLu hr1 hr2
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hxLower
  have he1 := routeBE1_le_exp_neg_div hx
  have htailDen : 0 < 2 * Real.pi * L := by positivity
  have hquot := (div_le_div_iff_of_pos_right htailDen).2 he1
  have hr : 0 < r := zero_lt_one.trans_le hr1
  have hrSq : r ^ 2 ≤ (4 : ℝ) := by
    have hp := pow_le_pow_left₀ hr.le hr2 2
    norm_num at hp
    exact hp
  have hpiCube : (27 : ℝ) ≤ Real.pi ^ 3 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3)
      Real.pi_gt_three.le 3
    norm_num at hp
    exact hp
  have hdenLower : (15 : ℝ) ≤
      4 * Real.pi ^ 3 * prawitzSplit ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hpiCube (sq_nonneg prawitzSplit)
    norm_num [prawitzSplit] at hmul ⊢
    nlinarith
  have hdenPos : 0 < 4 * Real.pi ^ 3 * prawitzSplit ^ 2 := by
    positivity
  have hnum : r ^ 2 * L ≤ (1 : ℝ) / 4 := by
    calc
      r ^ 2 * L ≤ 4 * ((1 : ℝ) / 16) :=
        mul_le_mul hrSq hLu hL.le (by norm_num)
      _ = (1 : ℝ) / 4 := by norm_num
  have hcoeff :
      r ^ 2 * L / (4 * Real.pi ^ 3 * prawitzSplit ^ 2) ≤ (1 : ℝ) / 60 := by
    apply (div_le_iff₀ hdenPos).2
    calc
      r ^ 2 * L ≤ (1 : ℝ) / 4 := hnum
      _ ≤ (1 / 60 : ℝ) *
          (4 * Real.pi ^ 3 * prawitzSplit ^ 2) := by nlinarith
  have hreform :
      (Real.exp (-x) / x) / (2 * Real.pi * L) =
        (r ^ 2 * L / (4 * Real.pi ^ 3 * prawitzSplit ^ 2)) *
          Real.exp (-x) := by
    dsimp only [x]
    unfold routeBLargeTailArgument
    field_simp [hL.ne', hr.ne', Real.pi_ne_zero,
      (by norm_num [prawitzSplit] : prawitzSplit ≠ 0)]
    ring
  have hexpArg : Real.exp (-x) ≤ Real.exp (-160) :=
    Real.exp_le_exp.mpr (by linarith)
  have hexp160 : Real.exp (-160) ≤ Real.exp (-32) :=
    Real.exp_le_exp.mpr (by norm_num)
  unfold routeBLargeTailValue
  change routeBE1 x / (2 * Real.pi * L) ≤ _
  calc
    routeBE1 x / (2 * Real.pi * L) ≤
        (Real.exp (-x) / x) / (2 * Real.pi * L) := hquot
    _ = (r ^ 2 * L / (4 * Real.pi ^ 3 * prawitzSplit ^ 2)) *
          Real.exp (-x) := hreform
    _ ≤ (1 / 60 : ℝ) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
    _ ≤ (1 / 60 : ℝ) * Real.exp (-160) :=
      mul_le_mul_of_nonneg_left hexpArg (by norm_num)
    _ ≤ (1 / 60 : ℝ) * Real.exp (-32) :=
      mul_le_mul_of_nonneg_left hexp160 (by norm_num)
    _ ≤ (1 / 60 : ℝ) * ((1 : ℝ) / 70000000000000) :=
      mul_le_mul_of_nonneg_left expNegThirtyTwoLe (by norm_num)
    _ ≤ (1 : ℝ) / 1000000000000 := by norm_num

theorem refinedRouteBNormalizedE1Tail_small_le
    {n : ℕ} (hn : 100 ≤ n) {rho eta : ℝ}
    (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hLupper : routeBSmoothingScale n rho ≤ 1 / 16) :
    Real.sqrt (n : ℝ) / rho *
        (routeBE1 (routeBTailArgument n rho eta) / (2 * Real.pi)) ≤
      (1 : ℝ) / 1000000000000 := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  let L := routeBSmoothingScale n rho
  let r := routeBDboundR rho eta
  have hL : 0 < L := routeBSmoothingScale_pos hnPos hrhoPos
  have hr1 : 1 ≤ r := by
    dsimp only [r]
    rw [routeBDboundR_eq_one_add hrhoPos.ne']
    exact le_add_of_nonneg_right (div_nonneg heta0 hrhoPos.le)
  have hr2 : r ≤ 2 := by
    dsimp only [r]
    rw [routeBDboundR_eq_one_add hrhoPos.ne']
    have hetaRho : eta ≤ rho := heta1.trans hrho1
    have hquot : eta / rho ≤ 1 := (div_le_one hrhoPos).2 hetaRho
    linarith
  rw [routeBNormalizedE1Tail_eq_largeTailValue hnPos hrhoPos]
  exact refinedRouteBLargeTailValue_small_le hL
    (by simpa only [L] using hLupper) hr1 hr2

/-- Pure-kernel counterpart of the complete Route B small-`L` tail theorem.
The dyadic finite sum is unchanged; only its four analytic omission estimates
are routed through the pure endpoint proof above. -/
theorem refinedRouteB_normalizedRouteBU_le_dyadicRouteBLargeSmallBound_upper
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
  have hlowOmission := refinedRouteBNormalizedLow_omission_le
    hn hrho1 heta0 heta1 (by simpa only [LR] using hLRu)
  have hmiddleOmission := refinedRouteBNormalizedHigh_middle_omission_le
    hn hrho1 heta0 heta1 (by simpa only [LR] using hLRu)
  have hendpointOmission := refinedRouteBNormalizedHigh_endpoint_omission_le
    hn hrho1 heta0 heta1 (by simpa only [LR] using hLRu)
  have htailOmission := refinedRouteBNormalizedE1Tail_small_le
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
