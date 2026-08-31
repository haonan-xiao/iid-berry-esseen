import BerryEsseen.Certificate.LargeN.SmallIntegral
import BerryEsseen.Certificate.LargeN.Tail
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Uniform omission bounds for the endpoint-regular large-`n` region

The exact small-`L` evaluator integrates the two endpoint changes of variables
only for `y ∈ [0,4]`.  This module bounds the remaining low-frequency tail,
the high-frequency middle and endpoint pieces, and the Gaussian `E₁` term.
-/

open MeasureTheory intervalIntegral Set

namespace BerryEsseen

noncomputable section

lemma exp_neg_le_one_sub_add_sq_half {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hquad := Real.quadratic_le_exp_of_nonneg hx
  have hdenPos : 0 < 1 + x + x ^ 2 / 2 := by positivity
  have hinv : Real.exp (-x) ≤ 1 / (1 + x + x ^ 2 / 2) := by
    rw [Real.exp_neg]
    simpa [one_div] using one_div_le_one_div_of_le hdenPos hquad
  have hpoly : 1 / (1 + x + x ^ 2 / 2) ≤ 1 - x + x ^ 2 / 2 := by
    apply (div_le_iff₀ hdenPos).2
    nlinarith [sq_nonneg (x ^ 2)]
  exact hinv.trans hpoly

lemma routeBEpsilon_one_le_c_div_eight {c : ℝ}
    (hc0 : 0 ≤ c) (hc2 : c ≤ 2) :
    routeBEpsilon 1 c ≤ c / 8 := by
  by_cases hc : c = 0
  · subst c
    simp [routeBEpsilon]
  · have hcPos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
    let x := c ^ 2 / 2
    have hx : 0 ≤ x := by dsimp only [x]; positivity
    have hrem := exp_neg_le_one_sub_add_sq_half hx
    have hrem' : Real.exp (-(c ^ 2) / 2) ≤
        1 - c ^ 2 / 2 + (c ^ 2 / 2) ^ 2 / 2 := by
      convert hrem using 1 <;> dsimp only [x] <;> ring
    have hnum : Real.exp (-(c ^ 2) / 2) - 1 + c ^ 2 / 2 ≤ c ^ 4 / 8 := by
      calc
        Real.exp (-(c ^ 2) / 2) - 1 + c ^ 2 / 2 ≤ (c ^ 2 / 2) ^ 2 / 2 := by
          linarith [hrem']
        _ = c ^ 4 / 8 := by ring
    have hpref : 0 ≤ (c ^ 3)⁻¹ := inv_nonneg.mpr (pow_nonneg hc0 3)
    unfold routeBEpsilon
    rw [if_neg hc]
    norm_num
    calc
      (c ^ 3)⁻¹ * (Real.exp (-(c ^ 2) / 2) - 1 + c ^ 2 / 2) ≤
          (c ^ 3)⁻¹ * (c ^ 4 / 8) :=
        mul_le_mul_of_nonneg_left hnum hpref
      _ = c / 8 := by field_simp [hc]

theorem routeBEpsilon_one_le_quarter {c : ℝ} (hc : 0 ≤ c) :
    routeBEpsilon 1 c ≤ 1 / 4 := by
  by_cases hc2 : c ≤ 2
  · exact (routeBEpsilon_one_le_c_div_eight hc hc2).trans (by linarith)
  · have hcPos : 0 < c := lt_of_lt_of_le (by norm_num) (le_of_not_ge hc2)
    have hcoarse := routeBEpsilon_le_inv_two_mul (rho := (1 : ℝ))
      (by norm_num) hcPos
    have hinv : 1 / (2 * c) ≤ (1 : ℝ) / 4 := by
      apply (div_le_iff₀ (mul_pos two_pos hcPos)).2
      nlinarith
    exact hcoarse.trans hinv

lemma routeBDiskScore_le_add_epsilon_sq
    {r epsilon x : ℝ} (hepsilon : 0 ≤ epsilon) (hx : 0 ≤ x) :
    routeBDiskScore (routeBBeta r) routeBD0 epsilon x ≤
      (routeBD0 + epsilon) ^ 2 := by
  have hmin : min (routeBBeta r ^ 2) (routeBD0 ^ 2 - x ^ 2) ≤
      routeBD0 ^ 2 - x ^ 2 := min_le_right _ _
  unfold routeBDiskScore
  have hcross : 0 ≤ x * epsilon := mul_nonneg hx hepsilon
  have hd0 : 0 ≤ routeBD0 := by norm_num [routeBD0]
  nlinarith

lemma routeBDiskBoundSqAtEpsilon_le_add_sq
    {r epsilon : ℝ} (hr : 1 ≤ r) (hepsilon : 0 ≤ epsilon) :
    routeBDiskBoundSqAtEpsilon routeBKappa r epsilon ≤
      (routeBD0 + epsilon) ^ 2 := by
  have hk : 0 ≤ routeBKappa := routeBKappa_pos.le
  have ha : 0 ≤ routeBTransition r := routeBTransition_nonneg hr
  unfold routeBDiskBoundSqAtEpsilon
  dsimp only
  split_ifs with hcondition
  · exact max_le
      (routeBDiskScore_le_add_epsilon_sq hepsilon (by norm_num))
      (max_le (routeBDiskScore_le_add_epsilon_sq hepsilon hk)
        (routeBDiskScore_le_add_epsilon_sq hepsilon ha))
  · exact max_le
      (routeBDiskScore_le_add_epsilon_sq hepsilon (by norm_num))
      (max_le (routeBDiskScore_le_add_epsilon_sq hepsilon hk)
        (routeBDiskScore_le_add_epsilon_sq hepsilon (by norm_num)))

theorem routeBDiskStar_le_five_twelfths
    {r c : ℝ} (hr : 1 ≤ r) (hc : 0 ≤ c) :
    routeBDiskStar r c ≤ 5 / 12 := by
  have he0 : 0 ≤ routeBEpsilon 1 c := routeBEpsilon_nonneg (by norm_num) hc
  have heq : routeBEpsilon 1 c ≤ 1 / 4 := routeBEpsilon_one_le_quarter hc
  have hzero := routeBDiskBoundSqAtEpsilon_le_add_sq (r := r)
    (epsilon := (0 : ℝ)) hr (by norm_num)
  have hone := routeBDiskBoundSqAtEpsilon_le_add_sq (r := r)
    (epsilon := routeBEpsilon 1 c) hr he0
  have hzero' : routeBDiskBoundSqAtEpsilon routeBKappa r 0 ≤ (5 / 12 : ℝ) ^ 2 := by
    norm_num [routeBD0] at hzero ⊢
    linarith
  have hone' : routeBDiskBoundSqAtEpsilon routeBKappa r (routeBEpsilon 1 c) ≤
      (5 / 12 : ℝ) ^ 2 := by
    apply hone.trans
    have hd0 : routeBD0 + routeBEpsilon 1 c ≤ (5 : ℝ) / 12 := by
      norm_num [routeBD0] at heq ⊢
      linarith
    exact pow_le_pow_left₀
      (add_nonneg (by norm_num [routeBD0]) he0) hd0 2
  unfold routeBDiskStar routeBDiskStarSq
  apply (Real.sqrt_le_iff).2
  exact ⟨by norm_num, max_le hzero' hone'⟩

/-- The linear minorant is uniformly at least `13/50` on the complete
low-frequency interval used by Route B. -/
lemma routeBMinorant_ge_thirteen_fiftieth {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ prawitzSplit) :
    13 / 50 ≤ routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t) := by
  have hline := checkerKappaUpper_line_le_routeBMinorant
    (v := 2 * Real.pi * t) (by positivity) (by
      have htOne : t ≤ 1 := ht1.trans (by norm_num [prawitzSplit])
      have hcoeff : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left htOne hcoeff)
  have hk0 : 0 ≤ routeBKappaUpper := by norm_num [routeBKappaUpper]
  have hv : 2 * Real.pi * t ≤ 2 * 3.15 * (19 / 50 : ℝ) := by
    have hpi := Real.pi_lt_d2.le
    have ht : t ≤ (19 / 50 : ℝ) := by simpa [prawitzSplit] using ht1
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpi (by norm_num)) ht
      (by positivity) (by norm_num)
  have hprod : routeBKappaUpper * (2 * Real.pi * t) ≤
      routeBKappaUpper * (2 * 3.15 * (19 / 50 : ℝ)) :=
    mul_le_mul_of_nonneg_left hv hk0
  have hnumeric : (13 : ℝ) / 50 ≤
      1 / 2 - routeBKappaUpper * (2 * 3.15 * (19 / 50 : ℝ)) := by
    norm_num [routeBKappaUpper]
  exact hnumeric.trans (by linarith)

lemma routeBLargeQ_low_tail_lower
    {L r y : ℝ} (hL : 0 < L) (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hy0 : 0 ≤ y) (ht : L * y ≤ prawitzSplit) :
    117 / 50 * y ^ 2 ≤ routeBLargeQ L r (L * y) := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr1
  have hrSq : r ^ 2 ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ hr0 hr2 2
  have hq := routeBMinorant_ge_thirteen_fiftieth
    (t := L * y) (mul_nonneg hL.le hy0) ht
  have hpiSq : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hden : 0 < r ^ 2 * L ^ 2 := mul_pos (sq_pos_of_pos (zero_lt_one.trans_le hr1))
    (sq_pos_of_pos hL)
  unfold routeBLargeQ
  apply (le_div_iff₀ hden).2
  calc
    117 / 50 * y ^ 2 * (r ^ 2 * L ^ 2) ≤
        117 / 50 * y ^ 2 * (4 * L ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by norm_num at hrSq ⊢; exact hrSq)
          (sq_nonneg L))
        (mul_nonneg (by norm_num) (sq_nonneg y))
    _ = (4 * 9 * (13 / 50 : ℝ)) * (L ^ 2 * y ^ 2) := by ring
    _ ≤ (4 * Real.pi ^ 2 * (13 / 50 : ℝ)) * (L ^ 2 * y ^ 2) := by
      have hc : 4 * 9 * (13 / 50 : ℝ) ≤ 4 * Real.pi ^ 2 * (13 / 50 : ℝ) := by
        nlinarith [hpiSq]
      exact mul_le_mul_of_nonneg_right hc
        (mul_nonneg (sq_nonneg L) (sq_nonneg y))
    _ = (2 * Real.pi * (L * y)) ^ 2 * (13 / 50 : ℝ) := by ring
    _ ≤ (2 * Real.pi * (L * y)) ^ 2 *
          routeBMinorant routeBKappa routeBTheta (2 * Real.pi * (L * y)) := by
      exact mul_le_mul_of_nonneg_left hq (sq_nonneg _)

lemma routeBLargeCellQLower_exact_hq
    {L r t : ℝ} (hL : 0 < L) (hr : 0 < r) (ht : 0 ≤ t) :
    routeBLargeCellQLower L r
        ((2 * Real.pi * t) ^ 2 *
          routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t)) =
      routeBLargeQ L r t := by
  have hq : 0 ≤ routeBLargeQ L r t := routeBLargeQ_nonneg hL hr ht
  simp only [routeBLargeCellQLower, routeBLargeQ]
  exact max_eq_left hq

lemma t_mul_norm_prawitzKernel_le_two_on_low
    {t : ℝ} (ht : 0 < t) (htSplit : t ≤ prawitzSplit) :
    t * ‖prawitzKernel t‖ ≤ 2 := by
  have hhalf : t ≤ (1 : ℝ) / 2 :=
    htSplit.trans (by norm_num [prawitzSplit])
  have hk := norm_prawitzKernel_le_two_div ht hhalf
  calc
    t * ‖prawitzKernel t‖ ≤ t * (2 / t) :=
      mul_le_mul_of_nonneg_left hk ht.le
    _ = 2 := by field_simp [ht.ne']

/-- After `t = L*y`, the omitted low-frequency difference tail is controlled
by a fixed Gaussian polynomial envelope.  The coefficient `854` deliberately
uses only the coarse global kernel estimate; it still fits comfortably inside
the exact `3e-11` omission budget. -/
theorem routeBLargeLowerDifference_low_tail_pointwise
    {L r y : ℝ} (hL : 0 < L) (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hy4 : 4 ≤ y) (ht : L * y ≤ prawitzSplit) :
    L * routeBLargeLowerDifferenceIntegrand L r (L * y) ≤
      854 * y ^ 2 * Real.exp (-2 * y ^ 2) := by
  have hr : 0 < r := zero_lt_one.trans_le hr1
  have hy0 : 0 ≤ y := (by linarith)
  have htPos : 0 < L * y := mul_pos hL (lt_of_lt_of_le (by norm_num) hy4)
  let hq : ℝ := (2 * Real.pi * (L * y)) ^ 2 *
    routeBMinorant routeBKappa routeBTheta (2 * Real.pi * (L * y))
  have hk : L * y * ‖prawitzKernel (L * y)‖ ≤ 2 :=
    t_mul_norm_prawitzKernel_le_two_on_low htPos ht
  have hD : routeBDiskStar r (2 * Real.pi * (L * y) / r) ≤ 5 / 12 :=
    routeBDiskStar_le_five_twelfths hr1 (by positivity)
  have hbase := routeBLargeLowerDifference_le_cellTelescoping
    hL hr htPos.le (hq := hq) (k0 := (2 : ℝ)) (D := (5 : ℝ) / 12)
      (by exact le_rfl) hk hD
  have hscaled := mul_le_mul_of_nonneg_left hbase hL.le
  have hqEq : routeBLargeCellQLower L r hq = routeBLargeQ L r (L * y) := by
    dsimp only [hq]
    exact routeBLargeCellQLower_exact_hq hL hr htPos.le
  have hreform :
      L * routeBLargeCellTelescoping L r (L * y) 2 hq (5 / 12) =
        ((5 : ℝ) / 3 * (2 * Real.pi) ^ 3 / r ^ 3 * y ^ 2) *
          Real.exp (-routeBLargeNAlpha * routeBLargeQ L r (L * y)) := by
    unfold routeBLargeCellTelescoping
    rw [hqEq]
    field_simp [hL.ne', hr.ne']
    <;> ring
  have htwoPi : 2 * Real.pi ≤ (8 : ℝ) := by
    nlinarith [Real.pi_le_four]
  have hcube : (2 * Real.pi) ^ 3 ≤ (512 : ℝ) := by
    have hp := pow_le_pow_left₀ (by positivity) htwoPi 3
    norm_num at hp
    exact hp
  have hrCube : (1 : ℝ) ≤ r ^ 3 := one_le_pow₀ hr1
  have hrCubePos : 0 < r ^ 3 := pow_pos hr 3
  have hquot : (2 * Real.pi) ^ 3 / r ^ 3 ≤ (512 : ℝ) := by
    apply (div_le_iff₀ hrCubePos).2
    nlinarith
  have hcoeff :
      (5 : ℝ) / 3 * (2 * Real.pi) ^ 3 / r ^ 3 * y ^ 2 ≤
        854 * y ^ 2 := by
    have hySq : 0 ≤ y ^ 2 := sq_nonneg y
    have hpre : (5 : ℝ) / 3 * ((2 * Real.pi) ^ 3 / r ^ 3) ≤ 854 := by
      nlinarith
    convert mul_le_mul_of_nonneg_right hpre hySq using 1 <;> ring
  have hQ := routeBLargeQ_low_tail_lower hL hr1 hr2 hy0 ht
  have halphaQ : 2 * y ^ 2 ≤
      routeBLargeNAlpha * routeBLargeQ L r (L * y) := by
    have hmul := mul_le_mul_of_nonneg_left hQ routeBLargeNAlpha_nonneg
    norm_num [routeBLargeNAlpha] at hmul ⊢
    nlinarith [sq_nonneg y]
  have hexp :
      Real.exp (-routeBLargeNAlpha * routeBLargeQ L r (L * y)) ≤
        Real.exp (-2 * y ^ 2) := by
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    L * routeBLargeLowerDifferenceIntegrand L r (L * y) ≤
        L * routeBLargeCellTelescoping L r (L * y) 2 hq (5 / 12) := hscaled
    _ = ((5 : ℝ) / 3 * (2 * Real.pi) ^ 3 / r ^ 3 * y ^ 2) *
          Real.exp (-routeBLargeNAlpha * routeBLargeQ L r (L * y)) := hreform
    _ ≤ 854 * y ^ 2 *
          Real.exp (-routeBLargeNAlpha * routeBLargeQ L r (L * y)) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
    _ ≤ 854 * y ^ 2 * Real.exp (-2 * y ^ 2) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)

/-- The Gaussian correction in the omitted low-frequency tail is much smaller
than the difference term. -/
theorem routeBLargeCorrection_low_tail_pointwise
    {L r y : ℝ} (hL : 0 < L) (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hy4 : 4 ≤ y) (ht : L * y ≤ prawitzSplit) :
    L * routeBLargeCorrectionIntegrand L r (L * y) ≤
      2 * y ^ 2 * Real.exp (-2 * y ^ 2) := by
  have hr : 0 < r := zero_lt_one.trans_le hr1
  have hy0 : 0 ≤ y := by linarith
  have ht0 : 0 ≤ L * y := mul_nonneg hL.le hy0
  have ht1 : L * y ≤ 1 :=
    ht.trans (by norm_num [prawitzSplit])
  have hkernel := norm_prawitzKernelCorrection_le_ten ht0 ht1
  have hreform :
      L * routeBLargeCorrectionIntegrand L r (L * y) =
        2 * ‖prawitzKernelCorrection (L * y)‖ *
          Real.exp (-((2 * Real.pi * y) ^ 2 / (2 * r ^ 2))) := by
    unfold routeBLargeCorrectionIntegrand
    rw [routeBLargeNormalEnvelope_mul_scale hL hr]
    field_simp [hL.ne']
  have hrSq : r ^ 2 ≤ (4 : ℝ) := by
    have := pow_le_pow_left₀ hr.le hr2 2
    norm_num at this
    exact this
  have hpiSq : (9 : ℝ) < Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hrPi : r ^ 2 ≤ Real.pi ^ 2 := by linarith
  have hden : 0 < 2 * r ^ 2 := mul_pos two_pos (sq_pos_of_pos hr)
  have harg : 2 * y ^ 2 ≤ (2 * Real.pi * y) ^ 2 / (2 * r ^ 2) := by
    apply (le_div_iff₀ hden).2
    have hmul := mul_le_mul_of_nonneg_right hrPi (sq_nonneg y)
    nlinarith
  have hexp :
      Real.exp (-((2 * Real.pi * y) ^ 2 / (2 * r ^ 2))) ≤
        Real.exp (-2 * y ^ 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hcoefficient :
      2 * ‖prawitzKernelCorrection (L * y)‖ ≤ 2 * y ^ 2 := by
    have hySq : (10 : ℝ) ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 4)]
    nlinarith
  calc
    L * routeBLargeCorrectionIntegrand L r (L * y) =
        2 * ‖prawitzKernelCorrection (L * y)‖ *
          Real.exp (-((2 * Real.pi * y) ^ 2 / (2 * r ^ 2))) := hreform
    _ ≤ 2 * y ^ 2 *
          Real.exp (-((2 * Real.pi * y) ^ 2 / (2 * r ^ 2))) :=
      mul_le_mul_of_nonneg_right hcoefficient (Real.exp_nonneg _)
    _ ≤ 2 * y ^ 2 * Real.exp (-2 * y ^ 2) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)

private def routeBLargeLowTailAntiderivative (y : ℝ) : ℝ :=
  -(y / 4 + 1 / 64) * Real.exp (-2 * y ^ 2)

private lemma routeBLargeLowTailAntiderivative_hasDerivAt (y : ℝ) :
    HasDerivAt routeBLargeLowTailAntiderivative
      ((y ^ 2 + y / 16 - 1 / 4) * Real.exp (-2 * y ^ 2)) y := by
  have hlinear : HasDerivAt (fun x : ℝ => -(x / 4 + 1 / 64)) (-1 / 4) y := by
    convert (((hasDerivAt_id y).div_const 4).add_const (1 / 64)).neg using 1 <;> ring
  have hquadratic : HasDerivAt (fun x : ℝ => -2 * x ^ 2) (-4 * y) y := by
    convert ((hasDerivAt_id y).pow 2).const_mul (-2) using 1 <;> norm_num <;> ring
  convert hlinear.mul hquadratic.exp using 1 <;>
    simp [routeBLargeLowTailAntiderivative, id] <;> ring

/-- A finite-interval Mills-type estimate, stated in the form needed after the
low-endpoint change of variables. -/
theorem intervalIntegral_sq_mul_exp_neg_two_sq_le
    {b : ℝ} (hb : 4 ≤ b) :
    (∫ y in (4 : ℝ)..b, y ^ 2 * Real.exp (-2 * y ^ 2)) ≤
      65 / 64 * Real.exp (-32) := by
  let f : ℝ → ℝ := fun y => y ^ 2 * Real.exp (-2 * y ^ 2)
  let g : ℝ → ℝ := fun y =>
    (y ^ 2 + y / 16 - 1 / 4) * Real.exp (-2 * y ^ 2)
  have hf : IntervalIntegrable f volume 4 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hg : IntervalIntegrable g volume 4 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hfg : ∫ y in (4 : ℝ)..b, f y ≤ ∫ y in (4 : ℝ)..b, g y := by
    apply intervalIntegral.integral_mono_on hb hf hg
    intro y hy
    dsimp only [f, g]
    have hfactor : 0 ≤ y / 16 - 1 / 4 := by linarith [hy.1]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
  have hFTC :
      (∫ y in (4 : ℝ)..b, g y) =
        routeBLargeLowTailAntiderivative b -
          routeBLargeLowTailAntiderivative 4 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro y _
      simpa only [g] using routeBLargeLowTailAntiderivative_hasDerivAt y
    · exact hg
  have hendpoint : routeBLargeLowTailAntiderivative b ≤ 0 := by
    unfold routeBLargeLowTailAntiderivative
    have hcoeff : 0 ≤ b / 4 + 1 / 64 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcoeff)
      (Real.exp_nonneg _)
  calc
    (∫ y in (4 : ℝ)..b, y ^ 2 * Real.exp (-2 * y ^ 2)) =
        ∫ y in (4 : ℝ)..b, f y := by rfl
    _ ≤ ∫ y in (4 : ℝ)..b, g y := hfg
    _ = routeBLargeLowTailAntiderivative b -
          routeBLargeLowTailAntiderivative 4 := hFTC
    _ ≤ 65 / 64 * Real.exp (-32) := by
      calc
        routeBLargeLowTailAntiderivative b -
            routeBLargeLowTailAntiderivative 4 ≤
          0 - routeBLargeLowTailAntiderivative 4 :=
            sub_le_sub_right hendpoint _
        _ = 65 / 64 * Real.exp (-32) := by
          norm_num [routeBLargeLowTailAntiderivative]

/-- Exact dyadic evaluation of the only transcendental endpoint appearing in
the low-tail omission estimate. -/
theorem exp_neg_thirty_two_le :
    Real.exp (-32) ≤ (1 : ℝ) / 70000000000000 := by
  let I : DyadicInterval := DyadicInterval.point 32
  have hx : I.Contains (32 : ℝ) := by
    simpa only [I] using DyadicInterval.contains_point (32 : ℤ)
  have hlo : 0 ≤ I.lo := by norm_num [I, DyadicInterval.point, dyadicScale]
  have hsound := dyadicExpNeg_sound hx hlo
  have hhi : (dyadicExpNeg I).hi ≤ 4 := by
    native_decide
  calc
    Real.exp (-32) ≤ (dyadicExpNeg I).upper := hsound.2
    _ ≤ (1 : ℝ) / 70000000000000 := by
      unfold DyadicInterval.upper
      have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
        exact_mod_cast dyadicScale_pos
      apply (div_le_iff₀ hscale).2
      have hhiReal : ((dyadicExpNeg I).hi : ℝ) ≤ 4 := by exact_mod_cast hhi
      norm_num [dyadicScale, dyadicPrecision] at hhiReal ⊢
      linarith

/-- The two normalized low-frequency terms, after `t = L*y`, satisfy the
common omitted-tail envelope for the actual Route B parameters. -/
theorem routeBNormalizedLow_low_tail_pointwise
    {n : ℕ} (hn : 100 ≤ n) {rho eta y : ℝ}
    (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hy4 : 4 ≤ y)
    (ht : routeBSmoothingScale n rho * y ≤ prawitzSplit) :
    routeBSmoothingScale n rho *
        routeBNormalizedLowIntegrand n rho eta
          (routeBSmoothingScale n rho * y) ≤
      856 * y ^ 2 * Real.exp (-2 * y ^ 2) := by
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
  have hdiff := routeBNormalizedLowerDifference_le_largeIntegrand
    (rho := rho) (r := r) (t := L * y) hn hrho1 hr1
      (mul_nonneg hL.le (by linarith))
  have hcorr := routeBNormalizedCorrection_le_largeIntegrand
    (rho := rho) (r := r) (t := L * y) hn hrho1 hr1
  have hdiff' :
      routeBNormalizedLowerDifferenceIntegrand n rho eta (L * y) ≤
        routeBLargeLowerDifferenceIntegrand L r (L * y) := by
    simpa [routeBNormalizedLowerDifferenceIntegrand, L, r] using hdiff
  have hcorr' :
      routeBNormalizedCorrectionIntegrand n rho eta (L * y) ≤
        routeBLargeCorrectionIntegrand L r (L * y) := by
    simpa [routeBNormalizedCorrectionIntegrand, L, r] using hcorr
  have hdiffScaled := mul_le_mul_of_nonneg_left hdiff' hL.le
  have hcorrScaled := mul_le_mul_of_nonneg_left hcorr' hL.le
  have hlargeDiff := routeBLargeLowerDifference_low_tail_pointwise
    hL hr1 hr2 hy4 (by simpa only [L] using ht)
  have hlargeCorr := routeBLargeCorrection_low_tail_pointwise
    hL hr1 hr2 hy4 (by simpa only [L] using ht)
  unfold routeBNormalizedLowIntegrand
  dsimp only [L, r] at hdiffScaled hcorrScaled hlargeDiff hlargeCorr ⊢
  calc
    routeBSmoothingScale n rho *
        (routeBNormalizedLowerDifferenceIntegrand n rho eta
            (routeBSmoothingScale n rho * y) +
          routeBNormalizedCorrectionIntegrand n rho eta
            (routeBSmoothingScale n rho * y)) =
      routeBSmoothingScale n rho *
          routeBNormalizedLowerDifferenceIntegrand n rho eta
            (routeBSmoothingScale n rho * y) +
        routeBSmoothingScale n rho *
          routeBNormalizedCorrectionIntegrand n rho eta
            (routeBSmoothingScale n rho * y) := by ring
    _ ≤ routeBSmoothingScale n rho *
          routeBLargeLowerDifferenceIntegrand (routeBSmoothingScale n rho)
            (routeBDboundR rho eta) (routeBSmoothingScale n rho * y) +
        routeBSmoothingScale n rho *
          routeBLargeCorrectionIntegrand (routeBSmoothingScale n rho)
            (routeBDboundR rho eta) (routeBSmoothingScale n rho * y) :=
      add_le_add hdiffScaled hcorrScaled
    _ ≤ 854 * y ^ 2 * Real.exp (-2 * y ^ 2) +
          2 * y ^ 2 * Real.exp (-2 * y ^ 2) :=
      add_le_add hlargeDiff hlargeCorr
    _ = 856 * y ^ 2 * Real.exp (-2 * y ^ 2) := by ring

/-- The whole omitted low-frequency interval costs at most `13e-12` in the
normalized Route B bound. -/
theorem routeBNormalizedLow_omission_le
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
  have hexp := exp_neg_thirty_two_le
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
        (mul_le_mul_of_nonneg_left hexp (by norm_num)) (by norm_num)
    _ ≤ (13 : ℝ) / 1000000000000 := by norm_num

/-- On the high-frequency middle interval the exponent numerator is already
at least one.  Below the breakpoint this follows from three rational line
segments; above it, it is `1 - cos v` on the negative-cosine half-period. -/
lemma one_le_routeB_hq_on_middle {t : ℝ}
    (ht0 : prawitzSplit ≤ t) (ht1 : t ≤ 3 / 4) :
    1 ≤ (2 * Real.pi * t) ^ 2 *
      routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t) := by
  let v := 2 * Real.pi * t
  have hsplit0 : 0 ≤ prawitzSplit := by norm_num [prawitzSplit]
  have htNonneg : 0 ≤ t := hsplit0.trans ht0
  have htPos : 0 < t :=
    (by norm_num [prawitzSplit] : (0 : ℝ) < prawitzSplit).trans_le ht0
  have hv0 : 0 ≤ v := by dsimp only [v]; positivity
  have hvPos : 0 < v := by
    dsimp only [v]
    positivity
  have hvLower : (57 : ℝ) / 25 ≤ v := by
    dsimp only [v]
    have h := mul_le_mul Real.pi_gt_three.le ht0 hsplit0 Real.pi_pos.le
    norm_num [prawitzSplit] at h ⊢
    nlinarith
  have hvUpper : v ≤ 3 * Real.pi / 2 := by
    dsimp only [v]
    nlinarith [Real.pi_pos]
  have hvTwoPi : v ≤ 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  by_cases hvTheta : v ≤ routeBTheta
  · have hk : routeBKappa ≤ (1 : ℝ) / 10 := by
      exact routeBKappa_lt_upper.le.trans (by norm_num [routeBKappaUpper])
    have hline : (1 : ℝ) / 2 - v / 10 ≤ 1 / 2 - routeBKappa * v := by
      have := mul_le_mul_of_nonneg_right hk hv0
      linarith
    have hlineProduct :
        v ^ 2 * ((1 : ℝ) / 2 - v / 10) ≤
          v ^ 2 * (1 / 2 - routeBKappa * v) :=
      mul_le_mul_of_nonneg_left hline (sq_nonneg v)
    have hlowerProduct :
        1 ≤ v ^ 2 * ((1 : ℝ) / 2 - v / 10) := by
      by_cases hv3 : v ≤ 3
      · have hvSq : ((57 : ℝ) / 25) ^ 2 ≤ v ^ 2 :=
          pow_le_pow_left₀ (by norm_num) hvLower 2
        have hlineLo : (1 : ℝ) / 5 ≤ 1 / 2 - v / 10 := by linarith
        have hmul := mul_le_mul hvSq hlineLo (by norm_num) (sq_nonneg v)
        norm_num at hmul ⊢
        linarith
      · have hv3' : 3 ≤ v := le_of_not_ge hv3
        by_cases hv15 : v ≤ (15 : ℝ) / 4
        · have hvSq : (9 : ℝ) ≤ v ^ 2 := by nlinarith
          have hlineLo : (1 : ℝ) / 8 ≤ 1 / 2 - v / 10 := by linarith
          have hmul := mul_le_mul hvSq hlineLo (by norm_num) (sq_nonneg v)
          nlinarith
        · have hv15' : (15 : ℝ) / 4 ≤ v := le_of_not_ge hv15
          have htheta4 : routeBTheta < 4 := by
            exact routeBTheta_lt_upper.trans (by norm_num [routeBThetaUpper])
          have hv4 : v ≤ 4 := hvTheta.trans htheta4.le
          have hvSq : ((15 : ℝ) / 4) ^ 2 ≤ v ^ 2 :=
            pow_le_pow_left₀ (by norm_num) hv15' 2
          have hlineLo : (1 : ℝ) / 10 ≤ 1 / 2 - v / 10 := by linarith
          have hmul := mul_le_mul hvSq hlineLo (by norm_num) (sq_nonneg v)
          norm_num at hmul ⊢
          linarith
    dsimp only [v] at hvTheta hvTwoPi hlineProduct hlowerProduct ⊢
    rw [routeBMinorant, if_pos hvTheta]
    exact hlowerProduct.trans hlineProduct
  · have hhalf : Real.pi / 2 ≤ v := by
      have hpiTheta : Real.pi < routeBTheta := routeBTheta_mem.1
      nlinarith [Real.pi_pos]
    have hvUpper' : v ≤ Real.pi + Real.pi / 2 := by
      nlinarith [hvUpper]
    have hcos : Real.cos v ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hhalf hvUpper'
    have hpsi : v ^ 2 * routeBPsi v = 1 - Real.cos v := by
      unfold routeBPsi
      field_simp [hvPos.ne']
    dsimp only [v] at hvTheta hvTwoPi hcos hpsi ⊢
    rw [routeBMinorant, if_neg hvTheta, if_pos hvTwoPi, hpsi]
    linarith

lemma routeBLargeQ_middle_lower
    {L r t : ℝ} (hL : 0 < L) (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (ht0 : prawitzSplit ≤ t) (ht1 : t ≤ 3 / 4) :
    1 / (4 * L ^ 2) ≤ routeBLargeQ L r t := by
  have hr : 0 < r := zero_lt_one.trans_le hr1
  have hrSq : r ^ 2 ≤ (4 : ℝ) := by
    have hp := pow_le_pow_left₀ hr.le hr2 2
    norm_num at hp
    exact hp
  have hhq := one_le_routeB_hq_on_middle ht0 ht1
  have hden : 0 < r ^ 2 * L ^ 2 :=
    mul_pos (sq_pos_of_pos hr) (sq_pos_of_pos hL)
  unfold routeBLargeQ
  apply (le_div_iff₀ hden).2
  calc
    1 / (4 * L ^ 2) * (r ^ 2 * L ^ 2) = r ^ 2 / 4 := by
      field_simp [hL.ne']
    _ ≤ 1 := by linarith
    _ ≤ (2 * Real.pi * t) ^ 2 *
        routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t) := hhq

lemma inv_mul_exp_neg_quarter_inv_sq_le_exp_neg_forty_eight
    {L : ℝ} (hL : 0 < L) (hLu : L ≤ 1 / 16) :
    L⁻¹ * Real.exp (-(1 / (4 * L ^ 2))) ≤ Real.exp (-48) := by
  let u : ℝ := 1 / (16 * L ^ 2)
  have hden : 0 < 16 * L ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hL)
  have hinvLeU : L⁻¹ ≤ u := by
    dsimp only [u]
    apply (le_div_iff₀ hden).2
    have h16L : 16 * L ≤ 1 := by nlinarith
    field_simp [hL.ne']
    nlinarith
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hinvExp : L⁻¹ ≤ Real.exp u := by
    calc
      L⁻¹ ≤ u := hinvLeU
      _ ≤ 1 + u := by linarith
      _ ≤ Real.exp u := by simpa [add_comm] using Real.add_one_le_exp u
  have hquarterExp0 : 0 ≤ Real.exp (-(1 / (4 * L ^ 2))) :=
    Real.exp_nonneg _
  have hproduct := mul_le_mul_of_nonneg_right hinvExp hquarterExp0
  have hLuSq : L ^ 2 ≤ ((1 : ℝ) / 16) ^ 2 :=
    pow_le_pow_left₀ hL.le hLu 2
  have hfortyEight : 48 ≤ 3 / (16 * L ^ 2) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  calc
    L⁻¹ * Real.exp (-(1 / (4 * L ^ 2))) ≤
        Real.exp u * Real.exp (-(1 / (4 * L ^ 2))) := hproduct
    _ = Real.exp (-(3 / (16 * L ^ 2))) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [u]
      field_simp [hL.ne']
      ring
    _ ≤ Real.exp (-48) := Real.exp_le_exp.mpr (by linarith)

theorem routeBLargeHigh_middle_pointwise
    {L r t : ℝ} (hL : 0 < L) (hLu : L ≤ 1 / 16)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (ht0 : prawitzSplit ≤ t) (ht1 : t ≤ 3 / 4) :
    routeBLargeHighIntegrand L r t ≤
      (200 / 19 : ℝ) * Real.exp (-48) := by
  have hk := norm_prawitzKernel_le_on_split ht0
    (ht1.trans (by norm_num))
  have hq := routeBLargeQ_middle_lower hL hr1 hr2 ht0 ht1
  have hexp : Real.exp (-routeBLargeQ L r t) ≤
      Real.exp (-(1 / (4 * L ^ 2))) :=
    Real.exp_le_exp.mpr (neg_le_neg hq)
  have hscale : 0 ≤ 2 / L := div_nonneg (by norm_num) hL.le
  have hkernelExp :
      ‖prawitzKernel t‖ * Real.exp (-routeBLargeQ L r t) ≤
        (2 / prawitzSplit) * Real.exp (-(1 / (4 * L ^ 2))) := by
    calc
      ‖prawitzKernel t‖ * Real.exp (-routeBLargeQ L r t) ≤
          (2 / prawitzSplit) * Real.exp (-routeBLargeQ L r t) :=
        mul_le_mul_of_nonneg_right hk (Real.exp_nonneg _)
      _ ≤ (2 / prawitzSplit) * Real.exp (-(1 / (4 * L ^ 2))) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num [prawitzSplit])
  have hbase := mul_le_mul_of_nonneg_left hkernelExp hscale
  have habsorb := inv_mul_exp_neg_quarter_inv_sq_le_exp_neg_forty_eight hL hLu
  unfold routeBLargeHighIntegrand
  calc
    2 / L * ‖prawitzKernel t‖ * Real.exp (-routeBLargeQ L r t) =
        (2 / L) *
          (‖prawitzKernel t‖ * Real.exp (-routeBLargeQ L r t)) := by ring
    _ ≤ (2 / L) *
          ((2 / prawitzSplit) * Real.exp (-(1 / (4 * L ^ 2)))) := hbase
    _ = (200 / 19 : ℝ) *
          (L⁻¹ * Real.exp (-(1 / (4 * L ^ 2)))) := by
      norm_num [prawitzSplit]
      field_simp [hL.ne']
      ring
    _ ≤ (200 / 19 : ℝ) * Real.exp (-48) :=
      mul_le_mul_of_nonneg_left habsorb (by norm_num)

theorem routeBNormalizedHigh_middle_omission_le
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
        mul_le_mul_of_nonneg_left exp_neg_thirty_two_le (by norm_num)
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

lemma routeB_hq_high_endpoint_lower
    {s : ℝ} (hs0 : 0 ≤ s) (hs4 : s ≤ 1 / 4) :
    8 * s ^ 2 ≤
      (2 * Real.pi * (1 - s)) ^ 2 *
        routeBMinorant routeBKappa routeBTheta (2 * Real.pi * (1 - s)) := by
  let x := Real.pi * s
  let v := 2 * Real.pi * (1 - s)
  have ht : (3 : ℝ) / 4 ≤ 1 - s := by linarith
  have hv4 : 4 < v := by
    dsimp only [v]
    nlinarith [Real.pi_gt_three]
  have hvTheta : ¬v ≤ routeBTheta := by
    have htheta4 : routeBTheta < 4 :=
      routeBTheta_lt_upper.trans (by norm_num [routeBThetaUpper])
    linarith
  have hvPos : 0 < v := by linarith
  have hvTwoPi : v ≤ 2 * Real.pi := by
    dsimp only [v]
    nlinarith [Real.pi_pos]
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hxHalf : x ≤ Real.pi / 2 := by
    dsimp only [x]
    nlinarith [Real.pi_pos]
  have hsin : 2 * s ≤ Real.sin x := by
    have hraw := Real.mul_le_sin hx0 hxHalf
    dsimp only [x] at hraw ⊢
    convert hraw using 1 <;> field_simp [Real.pi_ne_zero]
  have hsin0 : 0 ≤ Real.sin x := (mul_nonneg (by norm_num) hs0).trans hsin
  have hsinSq : (2 * s) ^ 2 ≤ Real.sin x ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hs0) hsin 2
  have htrig : 1 - Real.cos (2 * x) = 2 * Real.sin x ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hcos : Real.cos v = Real.cos (2 * x) := by
    have hvEq : v = 2 * Real.pi - 2 * x := by
      dsimp only [v, x]
      ring
    rw [hvEq, Real.cos_two_pi_sub]
  have hpsi : v ^ 2 * routeBPsi v = 1 - Real.cos v := by
    unfold routeBPsi
    field_simp [hvPos.ne']
  dsimp only [v] at hvTheta hvTwoPi hpsi hcos ⊢
  rw [routeBMinorant, if_neg hvTheta, if_pos hvTwoPi, hpsi, hcos, htrig]
  nlinarith

lemma routeBLargeQ_high_endpoint_lower
    {L r y : ℝ} (hL : 0 < L) (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hy0 : 0 ≤ y) (hLy : L * y ≤ 1 / 4) :
    2 * y ^ 2 ≤ routeBLargeQ L r (1 - L * y) := by
  have hr : 0 < r := zero_lt_one.trans_le hr1
  have hrSq : r ^ 2 ≤ (4 : ℝ) := by
    have hp := pow_le_pow_left₀ hr.le hr2 2
    norm_num at hp
    exact hp
  have hhq := routeB_hq_high_endpoint_lower
    (mul_nonneg hL.le hy0) hLy
  have hden : 0 < r ^ 2 * L ^ 2 :=
    mul_pos (sq_pos_of_pos hr) (sq_pos_of_pos hL)
  unfold routeBLargeQ
  apply (le_div_iff₀ hden).2
  calc
    2 * y ^ 2 * (r ^ 2 * L ^ 2) ≤
        2 * y ^ 2 * (4 * L ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hrSq (sq_nonneg L))
        (mul_nonneg (by norm_num) (sq_nonneg y))
    _ = 8 * (L * y) ^ 2 := by ring
    _ ≤ (2 * Real.pi * (1 - L * y)) ^ 2 *
        routeBMinorant routeBKappa routeBTheta
          (2 * Real.pi * (1 - L * y)) := hhq

theorem routeBLargeHigh_endpoint_pointwise
    {L r y : ℝ} (hL : 0 < L) (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hy0 : 0 ≤ y) (hLy : L * y ≤ 1 / 4) :
    L * routeBLargeHighIntegrand L r (1 - L * y) ≤
      4 * Real.exp (-2 * y ^ 2) := by
  have htHalf : (1 : ℝ) / 2 ≤ 1 - L * y := by linarith
  have htOne : 1 - L * y ≤ 1 := by
    have : 0 ≤ L * y := mul_nonneg hL.le hy0
    linarith
  have hk := norm_prawitzKernel_le_two_of_half_le htHalf htOne
  have hq := routeBLargeQ_high_endpoint_lower hL hr1 hr2 hy0 hLy
  have hexp : Real.exp (-routeBLargeQ L r (1 - L * y)) ≤
      Real.exp (-2 * y ^ 2) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul] using neg_le_neg hq
  have hreform :
      L * routeBLargeHighIntegrand L r (1 - L * y) =
        2 * ‖prawitzKernel (1 - L * y)‖ *
          Real.exp (-routeBLargeQ L r (1 - L * y)) := by
    unfold routeBLargeHighIntegrand
    field_simp [hL.ne']
  calc
    L * routeBLargeHighIntegrand L r (1 - L * y) =
        2 * ‖prawitzKernel (1 - L * y)‖ *
          Real.exp (-routeBLargeQ L r (1 - L * y)) := hreform
    _ ≤ 4 * Real.exp (-routeBLargeQ L r (1 - L * y)) := by
      exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_nonneg _)
    _ ≤ 4 * Real.exp (-2 * y ^ 2) :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)

theorem routeBNormalizedHigh_endpoint_pointwise
    {n : ℕ} (hn : 100 ≤ n) {rho eta y : ℝ}
    (hrho1 : 1 ≤ rho) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hy0 : 0 ≤ y) (hLy : routeBSmoothingScale n rho * y ≤ 1 / 4) :
    routeBSmoothingScale n rho *
        routeBNormalizedHighIntegrand n rho eta
          (1 - routeBSmoothingScale n rho * y) ≤
      4 * Real.exp (-2 * y ^ 2) := by
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
  have ht0 : 0 ≤ 1 - L * y := by
    have hquarter : L * y ≤ (1 : ℝ) / 4 := by
      simpa only [L] using hLy
    have : L * y ≤ (1 : ℝ) := hquarter.trans (by norm_num)
    linarith
  have hlarge := routeBNormalizedHigh_le_largeIntegrand
    (rho := rho) (r := r) (t := 1 - L * y) hn hrho1 hr1 ht0
  have hlarge' :
      routeBNormalizedHighIntegrand n rho eta (1 - L * y) ≤
        routeBLargeHighIntegrand L r (1 - L * y) := by
    simpa [routeBNormalizedHighIntegrand, L, r] using hlarge
  have hscaled := mul_le_mul_of_nonneg_left hlarge' hL.le
  have hendpoint := routeBLargeHigh_endpoint_pointwise hL hr1 hr2 hy0
    (by simpa only [L] using hLy)
  dsimp only [L, r] at hscaled hendpoint ⊢
  exact hscaled.trans hendpoint

theorem intervalIntegral_four_exp_neg_two_sq_le
    {b : ℝ} (hb : 4 ≤ b) :
    (∫ y in (4 : ℝ)..b, 4 * Real.exp (-2 * y ^ 2)) ≤
      65 / 256 * Real.exp (-32) := by
  let f : ℝ → ℝ := fun y => 4 * Real.exp (-2 * y ^ 2)
  let g : ℝ → ℝ := fun y =>
    (1 / 4 : ℝ) * (y ^ 2 * Real.exp (-2 * y ^ 2))
  have hf : IntervalIntegrable f volume 4 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hg : IntervalIntegrable g volume 4 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmono : (∫ y in (4 : ℝ)..b, f y) ≤ ∫ y in (4 : ℝ)..b, g y := by
    apply intervalIntegral.integral_mono_on hb hf hg
    intro y hy
    dsimp only [f, g]
    have hySq : (16 : ℝ) ≤ y ^ 2 := by
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hy.1 2
      norm_num at hp
      exact hp
    calc
      4 * Real.exp (-2 * y ^ 2) ≤
          ((1 / 4 : ℝ) * y ^ 2) * Real.exp (-2 * y ^ 2) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_nonneg _)
      _ = (1 / 4 : ℝ) * (y ^ 2 * Real.exp (-2 * y ^ 2)) := by ring
  have htail := intervalIntegral_sq_mul_exp_neg_two_sq_le hb
  calc
    (∫ y in (4 : ℝ)..b, 4 * Real.exp (-2 * y ^ 2)) =
        ∫ y in (4 : ℝ)..b, f y := by rfl
    _ ≤ ∫ y in (4 : ℝ)..b, g y := hmono
    _ = (1 / 4 : ℝ) *
          (∫ y in (4 : ℝ)..b, y ^ 2 * Real.exp (-2 * y ^ 2)) := by
      rw [← intervalIntegral.integral_const_mul]
    _ ≤ (1 / 4 : ℝ) * (65 / 64 * Real.exp (-32)) :=
      mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = 65 / 256 * Real.exp (-32) := by ring

theorem routeBNormalizedHigh_endpoint_omission_le
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
      mul_le_mul_of_nonneg_left exp_neg_thirty_two_le (by norm_num)
    _ ≤ (1 : ℝ) / 1000000000000 := by norm_num

lemma routeBE1_le_exp_neg_div {x : ℝ} (hx : 0 < x) :
    routeBE1 x ≤ Real.exp (-x) / x := by
  have hf := routeBE1Integrand_integrableOn_Ioi hx
  have hg : IntegrableOn (fun y : ℝ => (1 / x) * Real.exp (-y)) (Set.Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).const_mul (1 / x)
  have hint : (∫ y in Set.Ioi (0 : ℝ), routeBE1Integrand x y) ≤
      ∫ y in Set.Ioi (0 : ℝ), (1 / x) * Real.exp (-y) := by
    apply MeasureTheory.integral_mono_ae hf hg
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    have hy0 : 0 ≤ y := hy.le
    unfold routeBE1Integrand
    calc
      Real.exp (-y) / (x + y) ≤ Real.exp (-y) / x :=
        div_le_div_of_nonneg_left (Real.exp_nonneg _) hx (by linarith)
      _ = (1 / x) * Real.exp (-y) := by ring
  have hexp0 : 0 ≤ Real.exp (-x) := Real.exp_nonneg _
  unfold routeBE1
  calc
    Real.exp (-x) * (∫ y in Set.Ioi (0 : ℝ), routeBE1Integrand x y) ≤
        Real.exp (-x) *
          (∫ y in Set.Ioi (0 : ℝ), (1 / x) * Real.exp (-y)) :=
      mul_le_mul_of_nonneg_left hint hexp0
    _ = Real.exp (-x) / x := by
      rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi_zero]
      ring

lemma routeBLargeTailArgument_ge_one_sixty
    {L r : ℝ} (hL : 0 < L) (hLu : L ≤ 1 / 16)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
    160 ≤ routeBLargeTailArgument L r := by
  have hr : 0 < r := zero_lt_one.trans_le hr1
  have hrSq : r ^ 2 ≤ (4 : ℝ) := by
    have hp := pow_le_pow_left₀ hr.le hr2 2
    norm_num at hp
    exact hp
  have hLSq : L ^ 2 ≤ ((1 : ℝ) / 16) ^ 2 :=
    pow_le_pow_left₀ hL.le hLu 2
  have hdenUpper : r ^ 2 * L ^ 2 ≤ (1 : ℝ) / 64 := by
    calc
      r ^ 2 * L ^ 2 ≤ 4 * ((1 : ℝ) / 16) ^ 2 :=
        mul_le_mul hrSq hLSq (sq_nonneg L) (by norm_num)
      _ = (1 : ℝ) / 64 := by norm_num
  have hpiSq : (9 : ℝ) ≤ Real.pi ^ 2 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3)
      Real.pi_gt_three.le 2
    norm_num at hp
    exact hp
  have hnumLower : (5 : ℝ) / 2 ≤
      2 * Real.pi ^ 2 * prawitzSplit ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hpiSq (sq_nonneg prawitzSplit)
    norm_num [prawitzSplit] at hmul ⊢
    nlinarith
  have hden : 0 < r ^ 2 * L ^ 2 :=
    mul_pos (sq_pos_of_pos hr) (sq_pos_of_pos hL)
  unfold routeBLargeTailArgument
  apply (le_div_iff₀ hden).2
  calc
    160 * (r ^ 2 * L ^ 2) ≤ 160 * ((1 : ℝ) / 64) :=
      mul_le_mul_of_nonneg_left hdenUpper (by norm_num)
    _ = (5 : ℝ) / 2 := by norm_num
    _ ≤ 2 * Real.pi ^ 2 * prawitzSplit ^ 2 := hnumLower

theorem routeBLargeTailValue_small_le
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
      mul_le_mul_of_nonneg_left exp_neg_thirty_two_le (by norm_num)
    _ ≤ (1 : ℝ) / 1000000000000 := by norm_num

theorem routeBNormalizedE1Tail_small_le
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
  exact routeBLargeTailValue_small_le hL
    (by simpa only [L] using hLupper) hr1 hr2

end

end BerryEsseen
