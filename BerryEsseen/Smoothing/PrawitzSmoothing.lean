import BerryEsseen.Smoothing.Prawitz
import BerryEsseen.Smoothing.PrawitzFourier
import BerryEsseen.Probability.GaussianInversion
/-!
# The Prawitz smoothing inequality

This module turns the ordinary `L¹` Abel representatives constructed in
`PrawitzFourier` into the one-sided probability bounds used in (4.2).  The
Abel limit is taken after integration against a finite measure, justified by
the uniform physical-space bounds proved there.
-/

open Filter MeasureTheory ProbabilityTheory Set intervalIntegral
open scoped ComplexConjugate ENNReal FourierTransform NNReal Real Topology

namespace BerryEsseen

noncomputable section

open StatLean.HypothesisTesting

private theorem prawitzPhaseUnit_inv_sub (t : ℝ) :
    (prawitzPhaseUnit t)⁻¹ - prawitzPhaseUnit t =
      -2 * (((Real.sin (2 * Real.pi * t) : ℝ) : ℂ)) * Complex.I := by
  rw [← prawitzPhaseUnit_neg, prawitzPhaseUnit, prawitzPhaseUnit]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((-t : ℝ) : ℂ) =
      (((-(2 * Real.pi * t) : ℝ) : ℂ) * Complex.I) by push_cast; ring,
    show 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
      ((((2 * Real.pi * t) : ℝ) : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Real.cos_neg, Real.sin_neg]
  push_cast
  ring

private theorem prawitzAbelDenominator (r t : ℝ) :
    (1 - (r : ℂ) * (prawitzPhaseUnit t)⁻¹) *
        (1 - (r : ℂ) * prawitzPhaseUnit t) =
      ((((1 - r) ^ 2 + 4 * r * Real.sin (Real.pi * t) ^ 2 : ℝ) : ℂ)) := by
  have hcircle := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
  have hcos : Real.cos (2 * Real.pi * t) =
      1 - 2 * Real.sin (Real.pi * t) ^ 2 := by
    rw [show 2 * Real.pi * t = Real.pi * t + Real.pi * t by ring,
      Real.cos_add]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * t)]
  rw [← prawitzPhaseUnit_neg, prawitzPhaseUnit, prawitzPhaseUnit]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((-t : ℝ) : ℂ) =
      (((-(2 * Real.pi * t) : ℝ) : ℂ) * Complex.I) by push_cast; ring,
    show 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
      ((((2 * Real.pi * t) : ℝ) : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Real.cos_neg, Real.sin_neg]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, neg_mul, mul_zero, mul_one,
      zero_mul, zero_sub, sub_zero]
  · rw [hcos]
    rw [hcos] at hcircle
    ring_nf at hcircle ⊢
    nlinarith
  · ring

/-- The Abel phase is a regularized cotangent.  This real-denominator form
exposes the bound that is uniform in the Abel parameter. -/
theorem prawitzAbelPhase_eq_trigRatio {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    prawitzAbelPhase r t =
      (-2 * r * Real.sin (2 * Real.pi * t) : ℂ) * Complex.I /
        (((1 - r) ^ 2 + 4 * r * Real.sin (Real.pi * t) ^ 2 : ℝ) : ℂ) := by
  have hminus : 1 - (r : ℂ) * (prawitzPhaseUnit t)⁻¹ ≠ 0 := by
    intro hzero
    have heq : (r : ℂ) * (prawitzPhaseUnit t)⁻¹ = 1 :=
      (sub_eq_zero.mp hzero).symm
    have hn := congrArg norm heq
    simp only [norm_mul, norm_inv, norm_prawitzPhaseUnit, inv_one, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, norm_one] at hn
    linarith
  have hplus : 1 - (r : ℂ) * prawitzPhaseUnit t ≠ 0 := by
    intro hzero
    have heq : (r : ℂ) * prawitzPhaseUnit t = 1 :=
      (sub_eq_zero.mp hzero).symm
    have hn := congrArg norm heq
    simp only [norm_mul, norm_prawitzPhaseUnit, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0, norm_one] at hn
    linarith
  rw [prawitzAbelPhase, div_sub_div _ _ hminus hplus]
  rw [show
      (r : ℂ) * (prawitzPhaseUnit t)⁻¹ *
            (1 - (r : ℂ) * prawitzPhaseUnit t) -
          (1 - (r : ℂ) * (prawitzPhaseUnit t)⁻¹) *
            ((r : ℂ) * prawitzPhaseUnit t) =
        (r : ℂ) * ((prawitzPhaseUnit t)⁻¹ - prawitzPhaseUnit t) by ring,
    prawitzPhaseUnit_inv_sub, prawitzAbelDenominator]
  ring

/-- On the open frequency band, Abel regularization never exceeds the
boundary cotangent in norm. -/
theorem norm_prawitzAbelPhase_le_abs_cot {r t : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    ‖prawitzAbelPhase r t‖ ≤ |Real.cot (Real.pi * t)| := by
  have ha0 : 0 < Real.pi * t := mul_pos Real.pi_pos ht0
  have hapi : Real.pi * t < Real.pi := by
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi * t) :=
    Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  have hDpos : 0 < (1 - r) ^ 2 + 4 * r * Real.sin (Real.pi * t) ^ 2 := by
    have hsq : 0 < (1 - r) ^ 2 := sq_pos_of_pos (sub_pos.mpr hr1)
    positivity
  rw [prawitzAbelPhase_eq_trigRatio hr0 hr1, norm_div, norm_mul,
    Complex.norm_I, mul_one]
  rw [show (-2 : ℂ) * (r : ℂ) * (Real.sin (2 * Real.pi * t) : ℂ) =
      ((-2 * r * Real.sin (2 * Real.pi * t) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos hDpos]
  rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring,
    Real.sin_two_mul]
  simp only [abs_mul, abs_neg, abs_of_nonneg hr0,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hsin]
  rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsin]
  have hDlower :
      4 * r * Real.sin (Real.pi * t) ^ 2 ≤
        (1 - r) ^ 2 + 4 * r * Real.sin (Real.pi * t) ^ 2 := by
    nlinarith [sq_nonneg (1 - r)]
  by_cases hr : r = 0
  · subst r
    norm_num
    exact div_nonneg (abs_nonneg _) hsin.le
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
  apply (div_le_div_iff₀ hDpos hsin).2
  calc
    2 * r * (2 * Real.sin (Real.pi * t) * |Real.cos (Real.pi * t)|) *
          Real.sin (Real.pi * t) =
        |Real.cos (Real.pi * t)| *
          (4 * r * Real.sin (Real.pi * t) ^ 2) := by ring
    _ ≤ |Real.cos (Real.pi * t)| *
          ((1 - r) ^ 2 + 4 * r * Real.sin (Real.pi * t) ^ 2) :=
      mul_le_mul_of_nonneg_left hDlower (abs_nonneg _)

/-- Multiplication by the tent removes the second endpoint singularity and
leaves only the genuine `1/t` behavior at zero. -/
theorem norm_tent_mul_prawitzAbelPhase_le {r t : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    ‖((StatLean.HypothesisTesting.tent t : ℝ) : ℂ) *
        prawitzAbelPhase r t‖ ≤
      if t ≤ (1 : ℝ) / 2 then 1 / (2 * t) else 1 / 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have htent : StatLean.HypothesisTesting.tent t = 1 - t :=
    StatLean.HypothesisTesting.tent_of_mem_Icc_zero_one ⟨ht0.le, ht1.le⟩
  rw [htent, abs_of_pos (sub_pos.mpr ht1)]
  by_cases hhalf : t ≤ (1 : ℝ) / 2
  · rw [if_pos hhalf]
    calc
      (1 - t) * ‖prawitzAbelPhase r t‖ ≤
          (1 - t) * |Real.cot (Real.pi * t)| :=
        mul_le_mul_of_nonneg_left
          (norm_prawitzAbelPhase_le_abs_cot hr0 hr1 ht0 ht1)
          (sub_pos.mpr ht1).le
      _ ≤ 1 * (1 / (2 * t)) := by
        gcongr
        · linarith
        · exact abs_cot_pi_le_inv_two_mul ht0 hhalf
      _ = 1 / (2 * t) := one_mul _
  · rw [if_neg hhalf]
    have hhalf' : (1 : ℝ) / 2 < t := lt_of_not_ge hhalf
    have hs0 : 0 < 1 - t := sub_pos.mpr ht1
    have hsHalf : 1 - t ≤ (1 : ℝ) / 2 := by linarith
    have hcot : |Real.cot (Real.pi * t)| ≤ 1 / (2 * (1 - t)) := by
      rw [abs_cot_pi_eq_one_sub]
      exact abs_cot_pi_le_inv_two_mul hs0 hsHalf
    calc
      (1 - t) * ‖prawitzAbelPhase r t‖ ≤
          (1 - t) * |Real.cot (Real.pi * t)| :=
        mul_le_mul_of_nonneg_left
          (norm_prawitzAbelPhase_le_abs_cot hr0 hr1 ht0 ht1) hs0.le
      _ ≤ (1 - t) * (1 / (2 * (1 - t))) :=
        mul_le_mul_of_nonneg_left hcot hs0.le
      _ = 1 / 2 := by field_simp [hs0.ne']

/-- The nonconstant real part of Vaaler's upper half-line majorant. -/
def prawitzUpperNonconstant (z : ℝ) : ℝ :=
  (prawitzJ z - prawitzH z) / 2

/-- The nonconstant real part of Vaaler's lower half-line minorant. -/
def prawitzLowerNonconstant (z : ℝ) : ℝ :=
  (-prawitzH z - prawitzJ z) / 2

theorem prawitzCorrectionPreimage_neg
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    prawitzCorrectionPreimage (-t) = -prawitzCorrectionPreimage t := by
  have hnegNotPos : -t ∉ Set.Ioc (0 : ℝ) 1 := by
    simp [ht0.le]
  have hnegMem : -t ∈ Set.Ioc (-1 : ℝ) 0 := by
    constructor <;> linarith
  have hposMem : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht0, ht1.le⟩
  have hposNotNeg : t ∉ Set.Ioc (-1 : ℝ) 0 := by
    intro h
    linarith [h.2]
  simp [prawitzCorrectionPreimage, hnegNotPos, hnegMem,
    hposMem, hposNotNeg]
  ring

@[simp]
theorem prawitzAbelShiftPreimage_neg (r t : ℝ) :
    prawitzAbelShiftPreimage r (-t) = -prawitzAbelShiftPreimage r t := by
  rw [prawitzAbelShiftPreimage, prawitzAbelShiftPreimage,
    neg_neg, StatLean.HypothesisTesting.tent_neg,
    prawitzAbelPhase_neg]
  ring

theorem prawitzAbelHPreimage_neg
    (r : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    prawitzAbelHPreimage r (-t) = -prawitzAbelHPreimage r t := by
  rw [prawitzAbelHPreimage, prawitzAbelHPreimage,
    prawitzAbelShiftPreimage_neg,
    prawitzCorrectionPreimage_neg ht0 ht1]
  ring

/-- The two frequency halves of the upper Abel representative are related by
the even tent term and the odd `H` term. -/
theorem prawitzAbelUpperPreimage_eq_tent_sub_neg
    (r : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    prawitzAbelUpperPreimage r t =
      prawitzTentC t - prawitzAbelUpperPreimage r (-t) := by
  rw [prawitzAbelUpperPreimage, prawitzAbelUpperPreimage,
    prawitzAbelHPreimage_neg r ht0 ht1]
  have htent : prawitzTentC (-t) = prawitzTentC t := by
    simp [prawitzTentC, StatLean.HypothesisTesting.tent_neg]
  rw [htent]
  ring

/-- The lower representative is the reflected negative of the upper one. -/
theorem prawitzAbelLowerPreimage_eq_neg_upper_neg
    (r : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    prawitzAbelLowerPreimage r t = -prawitzAbelUpperPreimage r (-t) := by
  rw [prawitzAbelLowerPreimage, prawitzAbelUpperPreimage,
    prawitzAbelHPreimage_neg r ht0 ht1]
  have htent : prawitzTentC (-t) = prawitzTentC t := by
    simp [prawitzTentC, StatLean.HypothesisTesting.tent_neg]
  rw [htent]
  ring

/-- A uniform `1/t` envelope for the half of the Abel upper representative
that converges to the Prawitz kernel.  The estimate is deliberately coarse;
its role is to combine with the first-order zero of a characteristic
function at the origin. -/
theorem norm_prawitzAbelUpperPreimage_neg_le_two_div {r t : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    ‖prawitzAbelUpperPreimage r (-t)‖ ≤ 2 / t := by
  have htent : StatLean.HypothesisTesting.tent t = 1 - t :=
    StatLean.HypothesisTesting.tent_of_mem_Icc_zero_one ⟨ht0.le, ht1.le⟩
  have htentNorm : ‖prawitzTentC (-t)‖ ≤ 1 := by
    rw [prawitzTentC, StatLean.HypothesisTesting.tent_neg, htent,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht1)]
    linarith
  have hcorr : prawitzCorrectionPreimage (-t) =
      -Complex.I / (Real.pi : ℂ) := by
    have hnotPos : -t ∉ Set.Ioc (0 : ℝ) 1 := by simp [ht0.le]
    have hneg : -t ∈ Set.Ioc (-1 : ℝ) 0 := by constructor <;> linarith
    simp [prawitzCorrectionPreimage, hnotPos, hneg]
  have hcorrNorm : ‖prawitzCorrectionPreimage (-t)‖ ≤ 1 := by
    rw [hcorr, norm_div, norm_neg, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    exact (one_div_le_one_div_of_le one_pos
      (by linarith [Real.pi_gt_three])).trans_eq (one_div_one)
  have hshift : prawitzAbelShiftPreimage r (-t) =
      ((StatLean.HypothesisTesting.tent t : ℝ) : ℂ) *
        prawitzAbelPhase r t := by
    rw [prawitzAbelShiftPreimage, neg_neg,
      StatLean.HypothesisTesting.tent_neg]
  have hshiftNorm : ‖prawitzAbelShiftPreimage r (-t)‖ ≤
      if t ≤ (1 : ℝ) / 2 then 1 / (2 * t) else 1 / 2 := by
    rw [hshift]
    exact norm_tent_mul_prawitzAbelPhase_le hr0 hr1 ht0 ht1
  rw [prawitzAbelUpperPreimage, prawitzAbelHPreimage, norm_mul,
    show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
  calc
    (1 / 2 : ℝ) *
        ‖prawitzTentC (-t) -
          (prawitzAbelShiftPreimage r (-t) +
            prawitzCorrectionPreimage (-t))‖ ≤
      (1 / 2 : ℝ) *
        (1 + (if t ≤ (1 : ℝ) / 2 then 1 / (2 * t) else 1 / 2) + 1) := by
      gcongr
      calc
        ‖prawitzTentC (-t) -
            (prawitzAbelShiftPreimage r (-t) +
              prawitzCorrectionPreimage (-t))‖ ≤
            ‖prawitzTentC (-t)‖ +
              ‖prawitzAbelShiftPreimage r (-t) +
                prawitzCorrectionPreimage (-t)‖ := norm_sub_le _ _
        _ ≤ 1 +
            (‖prawitzAbelShiftPreimage r (-t)‖ +
              ‖prawitzCorrectionPreimage (-t)‖) := by
          gcongr
          exact norm_add_le _ _
        _ ≤ 1 +
            ((if t ≤ (1 : ℝ) / 2 then 1 / (2 * t) else 1 / 2) + 1) := by
          gcongr
      ring_nf
      exact le_rfl
    _ ≤ 2 / t := by
      by_cases hhalf : t ≤ (1 : ℝ) / 2
      · rw [if_pos hhalf]
        field_simp [ht0.ne']
        nlinarith
      · rw [if_neg hhalf]
        have htLe : t ≤ 1 := ht1.le
        apply (le_div_iff₀ ht0).2
        nlinarith

/-- The complementary half of the positive-frequency kernel is its complex
conjugate. -/
theorem prawitzTentC_sub_kernel_eq_conj {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    prawitzTentC t - prawitzKernel t = conj (prawitzKernel t) := by
  have htNe : t ≠ 1 := ht1.ne
  have htent : StatLean.HypothesisTesting.tent t = 1 - t :=
    StatLean.HypothesisTesting.tent_of_mem_Icc_zero_one ⟨ht0.le, ht1.le⟩
  rw [prawitzTentC, htent, prawitzKernel, if_neg htNe]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Pairing positive and negative frequencies turns the limiting complex
integrand into twice a real part. -/
theorem charFun_kernel_pair_eq_two_re
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    charFun mu (2 * Real.pi * t) * prawitzKernel t +
        charFun mu (-(2 * Real.pi * t)) *
          (prawitzTentC t - prawitzKernel t) =
      ((2 * (charFun mu (2 * Real.pi * t) * prawitzKernel t).re : ℝ) : ℂ) := by
  rw [charFun_neg, prawitzTentC_sub_kernel_eq_conj ht0 ht1]
  rw [← map_mul]
  exact Complex.add_conj _

theorem prawitzAbelUpperPreimage_eq_zero_of_notMem {r t : ℝ}
    (ht : t ∉ Set.Icc (-1 : ℝ) 1) :
    prawitzAbelUpperPreimage r t = 0 := by
  have hpos : t ∉ Set.Ioc (0 : ℝ) 1 := by
    intro h
    exact ht ⟨by linarith [h.1], h.2⟩
  have hneg : t ∉ Set.Ioc (-1 : ℝ) 0 := by
    intro h
    exact ht ⟨h.1.le, by linarith [h.2]⟩
  rw [prawitzAbelUpperPreimage, prawitzAbelHPreimage,
    prawitzAbelShiftPreimage, prawitzTentC,
    StatLean.HypothesisTesting.tent_eq_zero_of_notMem ht]
  simp [prawitzCorrectionPreimage, hpos, hneg]

theorem measurable_prawitzS : Measurable prawitzS := by
  unfold prawitzS
  fun_prop

theorem measurable_prawitzJ : Measurable prawitzJ := by
  unfold prawitzJ
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (measurable_prawitzS.div (measurable_id.pow_const 2))

theorem measurable_prawitzLeftShiftSeries :
    Measurable prawitzLeftShiftSeries := by
  unfold prawitzLeftShiftSeries
  refine measurable_of_tendsto_metrizable
    (f := fun (n : ℕ) (x : ℝ) => ∑ m ∈ Finset.range n,
      prawitzJ (x - ((m : ℝ) + 1))) ?_ ?_
  · intro n
    apply Finset.measurable_sum
    intro m hm
    exact measurable_prawitzJ.comp (by fun_prop)
  · rw [tendsto_pi_nhds]
    intro x
    exact (summable_prawitzLeftShiftSeries x).hasSum.tendsto_sum_nat

theorem measurable_prawitzRightShiftSeries :
    Measurable prawitzRightShiftSeries := by
  unfold prawitzRightShiftSeries
  refine measurable_of_tendsto_metrizable
    (f := fun (n : ℕ) (x : ℝ) => ∑ m ∈ Finset.range n,
      prawitzJ (x + ((m : ℝ) + 1))) ?_ ?_
  · intro n
    apply Finset.measurable_sum
    intro m hm
    exact measurable_prawitzJ.comp (by fun_prop)
  · rw [tendsto_pi_nhds]
    intro x
    exact (summable_prawitzRightShiftSeries x).hasSum.tendsto_sum_nat

theorem measurable_prawitzH : Measurable prawitzH := by
  rw [← funext prawitzShiftH_eq_prawitzH]
  unfold prawitzShiftH
  exact ((measurable_prawitzLeftShiftSeries.sub
    measurable_prawitzRightShiftSeries).add
      ((measurable_const.mul measurable_prawitzS).div measurable_id))

theorem measurable_prawitzUpperNonconstant :
    Measurable prawitzUpperNonconstant := by
  unfold prawitzUpperNonconstant
  exact (measurable_prawitzJ.sub measurable_prawitzH).div measurable_const

theorem measurable_prawitzLowerNonconstant :
    Measurable prawitzLowerNonconstant := by
  unfold prawitzLowerNonconstant
  exact (measurable_prawitzH.neg.sub measurable_prawitzJ).div measurable_const

theorem abs_prawitzUpperNonconstant_le_two (z : ℝ) :
    |prawitzUpperNonconstant z| ≤ 2 := by
  unfold prawitzUpperNonconstant
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    |prawitzJ z - prawitzH z| / 2 ≤
        (|prawitzJ z| + |prawitzH z|) / 2 := by
      gcongr
      exact abs_sub _ _
    _ ≤ (1 + 2) / 2 := by
      gcongr
      · rw [abs_of_nonneg (prawitzJ_nonneg z)]
        exact prawitzJ_le_one z
      · exact abs_prawitzH_le_two z
    _ ≤ 2 := by norm_num

theorem abs_prawitzLowerNonconstant_le_two (z : ℝ) :
    |prawitzLowerNonconstant z| ≤ 2 := by
  unfold prawitzLowerNonconstant
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    |-prawitzH z - prawitzJ z| / 2 ≤
        (|prawitzH z| + |prawitzJ z|) / 2 := by
      gcongr
      simpa only [abs_neg] using abs_sub (-prawitzH z) (prawitzJ z)
    _ ≤ (2 + 1) / 2 := by
      gcongr
      · exact abs_prawitzH_le_two z
      · rw [abs_of_nonneg (prawitzJ_nonneg z)]
        exact prawitzJ_le_one z
    _ ≤ 2 := by norm_num

theorem integrable_prawitzUpperNonconstant_comp
    (mu : Measure ℝ) [IsFiniteMeasure mu] (a x : ℝ) :
    Integrable (fun y : ℝ => prawitzUpperNonconstant (a * (y - x))) mu := by
  refine (integrable_const (2 : ℝ)).mono'
    ((measurable_prawitzUpperNonconstant.comp (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  exact abs_prawitzUpperNonconstant_le_two _

theorem integrable_prawitzLowerNonconstant_comp
    (mu : Measure ℝ) [IsFiniteMeasure mu] (a x : ℝ) :
    Integrable (fun y : ℝ => prawitzLowerNonconstant (a * (y - x))) mu := by
  refine (integrable_const (2 : ℝ)).mono'
    ((measurable_prawitzLowerNonconstant.comp (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  exact abs_prawitzLowerNonconstant_le_two _

/-- The positive rescaling used in Prawitz's convention. -/
def prawitzAffineScale (T : ℝ) : ℝ :=
  T / (2 * Real.pi)

/-- The law of `T (Y-x) / (2π)`. -/
def prawitzAffineLaw (mu : Measure ℝ) (T x : ℝ) : Measure ℝ :=
  mu.map (fun y : ℝ => prawitzAffineScale T * (y - x))

instance instIsProbabilityMeasurePrawitzAffineLaw
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (T x : ℝ) :
    IsProbabilityMeasure (prawitzAffineLaw mu T x) := by
  unfold prawitzAffineLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem lawCDF_prawitzAffineLaw_zero
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    lawCDF (prawitzAffineLaw mu T x) 0 = lawCDF mu x := by
  have hscale : 0 < prawitzAffineScale T := by
    unfold prawitzAffineScale
    positivity
  unfold lawCDF prawitzAffineLaw
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext y
  simp only [Set.mem_preimage, Set.mem_Iic]
  constructor <;> intro hy
  · have : y - x ≤ 0 := by nlinarith
    exact sub_nonpos.mp this
  · have : y - x ≤ 0 := sub_nonpos.mpr hy
    nlinarith

/-- Characteristic function of the translated and rescaled law used in the
Prawitz Fourier convention. -/
theorem charFun_prawitzAffineLaw
    (mu : Measure ℝ) [IsFiniteMeasure mu] (T x u : ℝ) :
    charFun (prawitzAffineLaw mu T x) u =
      charFun mu (prawitzAffineScale T * u) *
        Complex.exp
          (-((prawitzAffineScale T * x * u : ℝ) : ℂ) * Complex.I) := by
  rw [charFun_apply_real, charFun_apply_real, prawitzAffineLaw,
    integral_map (by fun_prop) (by fun_prop)]
  calc
    ∫ y : ℝ,
        Complex.exp
          (((u : ℂ) * (prawitzAffineScale T * (y - x) : ℝ)) *
            Complex.I) ∂mu =
      ∫ y : ℝ,
        Complex.exp
            ((((prawitzAffineScale T * u : ℝ) : ℂ) * (y : ℂ)) *
              Complex.I) *
          Complex.exp
            (-((prawitzAffineScale T * x * u : ℝ) : ℂ) *
              Complex.I) ∂mu := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
    _ = _ := MeasureTheory.integral_mul_const _ _

/-- A finite first absolute moment makes the characteristic function
Lipschitz at the origin.  This is the cancellation that controls the
`1 / t` part of Prawitz's kernel after positive/negative frequencies are
paired. -/
theorem norm_charFun_sub_one_le_firstMoment
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hint : Integrable (id : ℝ → ℝ) mu) (u : ℝ) :
    ‖charFun mu u - 1‖ ≤ |u| * ∫ y : ℝ, |y| ∂mu := by
  have hExp : Integrable
      (fun y : ℝ => Complex.exp ((u : ℂ) * (y : ℂ) * Complex.I)) mu := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop)
      (Filter.Eventually.of_forall fun y => ?_)
    have heq : (u : ℂ) * (y : ℂ) * Complex.I =
        (((u * y : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [heq, Complex.norm_exp_ofReal_mul_I]
  have hOne : ∫ _y : ℝ, (1 : ℂ) ∂mu = 1 := by
    rw [MeasureTheory.integral_const, probReal_univ, one_smul]
  have hAbs : Integrable (fun y : ℝ => |y|) mu := by
    simpa only [Real.norm_eq_abs, id_eq] using hint.norm
  rw [charFun_apply_real, ← hOne,
    ← MeasureTheory.integral_sub hExp (integrable_const 1)]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  calc
    ∫ y : ℝ,
        ‖Complex.exp ((u : ℂ) * (y : ℂ) * Complex.I) - 1‖ ∂mu ≤
      ∫ y : ℝ, |u| * |y| ∂mu := by
        apply MeasureTheory.integral_mono
        · exact (hExp.sub (integrable_const 1)).norm
        · exact hAbs.const_mul |u|
        intro y
        have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := u * y)
        have heq : (u : ℂ) * (y : ℂ) * Complex.I =
            Complex.I * ((u * y : ℝ) : ℂ) := by
          push_cast
          ring
        calc
          ‖Complex.exp ((u : ℂ) * (y : ℂ) * Complex.I) - 1‖ =
              ‖Complex.exp (Complex.I * ((u * y : ℝ) : ℂ)) - 1‖ := by
                rw [heq]
          _ ≤ ‖u * y‖ := h
          _ = |u| * |y| := by rw [Real.norm_eq_abs, abs_mul]
    _ = |u| * ∫ y : ℝ, |y| ∂mu :=
      MeasureTheory.integral_const_mul _ _

/-- Integrating Vaaler's upper majorant gives a one-sided CDF bound. -/
theorem lawCDF_zero_le_half_add_integral_prawitzUpperNonconstant
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    lawCDF mu 0 ≤
      1 / 2 + ∫ z : ℝ, prawitzUpperNonconstant z ∂mu := by
  let ind : ℝ → ℝ := Set.indicator (Set.Iic 0) (fun _ : ℝ => (1 : ℝ))
  have hind : Integrable ind mu := by
    dsimp [ind]
    exact (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  have huNC : Integrable prawitzUpperNonconstant mu := by
    simpa using integrable_prawitzUpperNonconstant_comp mu 1 0
  have hu : Integrable (fun z : ℝ => 1 / 2 + prawitzUpperNonconstant z) mu := by
    exact (integrable_const (1 / 2 : ℝ)).add huNC
  have hle : ∫ z : ℝ, ind z ∂mu ≤
      ∫ z : ℝ, (1 / 2 + prawitzUpperNonconstant z) ∂mu := by
    apply integral_mono hind hu
    intro z
    have hz := (prawitz_halfLine_sandwich z).2
    dsimp [ind]
    unfold prawitzUpperNonconstant
    linarith
  have hind_eq : ∫ z : ℝ, ind z ∂mu = lawCDF mu 0 := by
    dsimp [ind]
    simpa [lawCDF, measureReal_def] using
      (integral_indicator_const (mu := mu) (1 : ℝ) measurableSet_Iic)
  have hu_eq :
      ∫ z : ℝ, (1 / 2 + prawitzUpperNonconstant z) ∂mu =
        1 / 2 + ∫ z : ℝ, prawitzUpperNonconstant z ∂mu := by
    rw [MeasureTheory.integral_add (integrable_const (1 / 2 : ℝ)) huNC,
      MeasureTheory.integral_const, probReal_univ, one_smul]
  rwa [hind_eq, hu_eq] at hle

/-- Integrating Vaaler's lower minorant gives the matching one-sided CDF bound. -/
theorem half_add_integral_prawitzLowerNonconstant_le_lawCDF_zero
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    1 / 2 + ∫ z : ℝ, prawitzLowerNonconstant z ∂mu ≤
      lawCDF mu 0 := by
  let ind : ℝ → ℝ := Set.indicator (Set.Iic 0) (fun _ : ℝ => (1 : ℝ))
  have hind : Integrable ind mu := by
    dsimp [ind]
    exact (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  have hlNC : Integrable prawitzLowerNonconstant mu := by
    simpa using integrable_prawitzLowerNonconstant_comp mu 1 0
  have hl : Integrable (fun z : ℝ => 1 / 2 + prawitzLowerNonconstant z) mu := by
    exact (integrable_const (1 / 2 : ℝ)).add hlNC
  have hle : ∫ z : ℝ, (1 / 2 + prawitzLowerNonconstant z) ∂mu ≤
      ∫ z : ℝ, ind z ∂mu := by
    apply integral_mono hl hind
    intro z
    have hz := (prawitz_halfLine_sandwich z).1
    dsimp [ind]
    unfold prawitzLowerNonconstant
    linarith
  have hind_eq : ∫ z : ℝ, ind z ∂mu = lawCDF mu 0 := by
    dsimp [ind]
    simpa [lawCDF, measureReal_def] using
      (integral_indicator_const (mu := mu) (1 : ℝ) measurableSet_Iic)
  have hl_eq :
      ∫ z : ℝ, (1 / 2 + prawitzLowerNonconstant z) ∂mu =
        1 / 2 + ∫ z : ℝ, prawitzLowerNonconstant z ∂mu := by
    rw [MeasureTheory.integral_add (integrable_const (1 / 2 : ℝ)) hlNC,
      MeasureTheory.integral_const, probReal_univ, one_smul]
  rwa [hl_eq, hind_eq] at hle

/-- Parseval's identity for the Abel-regularized upper majorant. -/
theorem integral_fourier_prawitzAbelUpperPreimage_eq_charFun
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ z : ℝ, FourierTransform.fourier
        (prawitzAbelUpperPreimage r) z ∂mu =
      ∫ xi : ℝ, charFun mu (-(2 * Real.pi * xi)) *
        prawitzAbelUpperPreimage r xi := by
  exact integral_fourier_measure
    (integrable_prawitzAbelUpperPreimage hr0 hr1)

/-- Parseval's identity for the Abel-regularized lower minorant. -/
theorem integral_fourier_prawitzAbelLowerPreimage_eq_charFun
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ z : ℝ, FourierTransform.fourier
        (prawitzAbelLowerPreimage r) z ∂mu =
      ∫ xi : ℝ, charFun mu (-(2 * Real.pi * xi)) *
        prawitzAbelLowerPreimage r xi := by
  exact integral_fourier_measure
    (integrable_prawitzAbelLowerPreimage hr0 hr1)

/-- The exact positive-frequency pairing of the upper Abel representative. -/
def prawitzAbelUpperPair (mu : Measure ℝ) (r t : ℝ) : ℂ :=
  charFun mu (2 * Real.pi * t) * prawitzAbelUpperPreimage r (-t) +
    charFun mu (-(2 * Real.pi * t)) * prawitzAbelUpperPreimage r t

/-- The full Parseval integral is exactly the paired integral over the open
positive frequency band. -/
theorem integral_charFun_mul_prawitzAbelUpperPreimage_eq_pair
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ xi : ℝ, charFun mu (-(2 * Real.pi * xi)) *
        prawitzAbelUpperPreimage r xi) =
      ∫ t in (0 : ℝ)..1, prawitzAbelUpperPair mu r t := by
  let f : ℝ → ℂ := fun xi => charFun mu (-(2 * Real.pi * xi)) *
    prawitzAbelUpperPreimage r xi
  have harg : Measurable fun xi : ℝ => -(2 * Real.pi * xi) := by fun_prop
  have hf : Integrable f :=
    (integrable_prawitzAbelUpperPreimage hr0 hr1).bdd_mul
      (measurable_charFun.comp harg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun xi => norm_charFun_le_one _)
  have hfneg : Integrable (fun t : ℝ => f (-t)) := hf.comp_neg
  calc
    (∫ xi : ℝ, charFun mu (-(2 * Real.pi * xi)) *
        prawitzAbelUpperPreimage r xi) = ∫ xi : ℝ, f xi := by rfl
    _ = (∫ xi in Set.Iic (0 : ℝ), f xi) +
        ∫ xi in Set.Ioi (0 : ℝ), f xi := by
      exact (integral_Iic_add_Ioi hf.integrableOn hf.integrableOn).symm
    _ = (∫ t in Set.Ioi (0 : ℝ), f (-t)) +
        ∫ t in Set.Ioi (0 : ℝ), f t := by
      rw [integral_comp_neg_Ioi]
      simp
    _ = ∫ t in Set.Ioi (0 : ℝ), (f (-t) + f t) := by
      exact (integral_add hfneg.integrableOn hf.integrableOn).symm
    _ = ∫ t in Set.Ioi (0 : ℝ), prawitzAbelUpperPair mu r t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only [f, prawitzAbelUpperPair]
      congr 1 <;> ring_nf
    _ = ∫ t in Set.Ioc (0 : ℝ) 1, prawitzAbelUpperPair mu r t := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
      exact integral_union_eq_left_of_forall measurableSet_Ioi fun t ht => by
        have htPos : 1 < t := ht
        have htOut : t ∉ Set.Icc (-1 : ℝ) 1 := by
          intro h
          linarith [h.2]
        have hnegOut : -t ∉ Set.Icc (-1 : ℝ) 1 := by
          intro h
          linarith [h.1]
        simp [prawitzAbelUpperPair,
          prawitzAbelUpperPreimage_eq_zero_of_notMem htOut,
          prawitzAbelUpperPreimage_eq_zero_of_notMem hnegOut]
    _ = ∫ t in (0 : ℝ)..1, prawitzAbelUpperPair mu r t := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- The paired Abel integrand written so that its zero-frequency
cancellation is explicit. -/
theorem prawitzAbelUpperPair_eq_cancellation
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (r : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    prawitzAbelUpperPair mu r t =
      charFun mu (-(2 * Real.pi * t)) * prawitzTentC t +
        (charFun mu (2 * Real.pi * t) -
          charFun mu (-(2 * Real.pi * t))) *
            prawitzAbelUpperPreimage r (-t) := by
  rw [prawitzAbelUpperPair,
    prawitzAbelUpperPreimage_eq_tent_sub_neg r ht0 ht1]
  ring

theorem norm_charFun_pos_sub_neg_le_firstMoment
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hint : Integrable (id : ℝ → ℝ) mu) {t : ℝ} (ht0 : 0 < t) :
    ‖charFun mu (2 * Real.pi * t) -
        charFun mu (-(2 * Real.pi * t))‖ ≤
      4 * Real.pi * t * ∫ y : ℝ, |y| ∂mu := by
  have hpos := norm_charFun_sub_one_le_firstMoment mu hint (2 * Real.pi * t)
  have hneg := norm_charFun_sub_one_le_firstMoment mu hint (-(2 * Real.pi * t))
  have huAbs : |2 * Real.pi * t| = 2 * Real.pi * t := by
    rw [abs_of_pos (mul_pos (mul_pos two_pos Real.pi_pos) ht0)]
  rw [huAbs] at hpos
  have hnegAbs : |-(2 * Real.pi * t)| = 2 * Real.pi * t := by
    rw [abs_neg, huAbs]
  rw [hnegAbs] at hneg
  calc
    ‖charFun mu (2 * Real.pi * t) -
        charFun mu (-(2 * Real.pi * t))‖ =
      ‖(charFun mu (2 * Real.pi * t) - 1) -
        (charFun mu (-(2 * Real.pi * t)) - 1)‖ := by ring_nf
    _ ≤ ‖charFun mu (2 * Real.pi * t) - 1‖ +
        ‖charFun mu (-(2 * Real.pi * t)) - 1‖ := norm_sub_le _ _
    _ ≤ (2 * Real.pi * t) * (∫ y : ℝ, |y| ∂mu) +
        (2 * Real.pi * t) * (∫ y : ℝ, |y| ∂mu) :=
      add_le_add hpos hneg
    _ = 4 * Real.pi * t * ∫ y : ℝ, |y| ∂mu := by ring

/-- After positive/negative frequency pairing, the Abel family has an
integrable bound independent of the Abel parameter. -/
theorem norm_prawitzAbelUpperPair_le_firstMoment
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hint : Integrable (id : ℝ → ℝ) mu)
    {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ht0 : 0 < t) (ht1 : t < 1) :
    ‖prawitzAbelUpperPair mu r t‖ ≤
      1 + 8 * Real.pi * ∫ y : ℝ, |y| ∂mu := by
  let M : ℝ := ∫ y : ℝ, |y| ∂mu
  have hM : 0 ≤ M := integral_nonneg fun y => abs_nonneg y
  have htent : ‖prawitzTentC t‖ ≤ 1 := by
    have htentEq : StatLean.HypothesisTesting.tent t = 1 - t :=
      StatLean.HypothesisTesting.tent_of_mem_Icc_zero_one ⟨ht0.le, ht1.le⟩
    rw [prawitzTentC, htentEq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr ht1)]
    linarith
  rw [prawitzAbelUpperPair_eq_cancellation mu r ht0 ht1]
  calc
    ‖charFun mu (-(2 * Real.pi * t)) * prawitzTentC t +
        (charFun mu (2 * Real.pi * t) -
          charFun mu (-(2 * Real.pi * t))) *
            prawitzAbelUpperPreimage r (-t)‖ ≤
      ‖charFun mu (-(2 * Real.pi * t)) * prawitzTentC t‖ +
        ‖(charFun mu (2 * Real.pi * t) -
          charFun mu (-(2 * Real.pi * t))) *
            prawitzAbelUpperPreimage r (-t)‖ := norm_add_le _ _
    _ = ‖charFun mu (-(2 * Real.pi * t))‖ * ‖prawitzTentC t‖ +
        ‖charFun mu (2 * Real.pi * t) -
          charFun mu (-(2 * Real.pi * t))‖ *
            ‖prawitzAbelUpperPreimage r (-t)‖ := by rw [norm_mul, norm_mul]
    _ ≤ 1 * 1 + (4 * Real.pi * t * M) * (2 / t) := by
      gcongr
      · exact norm_charFun_le_one _
      · exact norm_charFun_pos_sub_neg_le_firstMoment mu hint ht0
      · exact norm_prawitzAbelUpperPreimage_neg_le_two_div hr0 hr1 ht0 ht1
    _ = 1 + 8 * Real.pi * M := by field_simp [ht0.ne']; ring

/-- On positive frequencies, the negative-frequency side of the Abel upper
representative converges to Prawitz's kernel.  This fixes the sign convention
needed after pairing the two halves of the Fourier integral. -/
theorem tendsto_prawitzAbelUpperPreimage_neg_eq_kernel
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Tendsto (fun r : ℝ => prawitzAbelUpperPreimage r (-t))
      (nhds 1) (nhds (prawitzKernel t)) := by
  have htent : StatLean.HypothesisTesting.tent t = 1 - t :=
    StatLean.HypothesisTesting.tent_of_mem_Icc_zero_one ⟨ht0.le, ht1.le⟩
  have htentNeg : StatLean.HypothesisTesting.tent (-t) = 1 - t := by
    rw [StatLean.HypothesisTesting.tent_neg, htent]
  have hcorrNeg :
      prawitzCorrectionPreimage (-t) = -Complex.I / (Real.pi : ℂ) := by
    have hnotPos : -t ∉ Set.Ioc (0 : ℝ) 1 := by simp [ht0.le]
    have hneg : -t ∈ Set.Ioc (-1 : ℝ) 0 := by constructor <;> linarith
    simp [prawitzCorrectionPreimage, hnotPos, hneg]
  have hshift :
      Tendsto (fun r : ℝ => prawitzAbelShiftPreimage r (-t))
        (nhds 1)
        (nhds (-Complex.I * (((1 - t : ℝ) : ℂ)) *
          Complex.cot ((Real.pi : ℂ) * (t : ℂ)))) := by
    convert tendsto_prawitzAbelPhase_mul_tent ht0 ht1 using 1
    funext r
    unfold prawitzAbelShiftPreimage
    rw [neg_neg, StatLean.HypothesisTesting.tent_neg]
    ring
  have hdiff :
      Tendsto
        (fun r : ℝ => prawitzTentC (-t) -
          (prawitzAbelShiftPreimage r (-t) +
            prawitzCorrectionPreimage (-t)))
        (nhds 1)
        (nhds (prawitzTentC (-t) -
          (-Complex.I * (((1 - t : ℝ) : ℂ)) *
              Complex.cot ((Real.pi : ℂ) * (t : ℂ)) +
            prawitzCorrectionPreimage (-t)))) :=
    tendsto_const_nhds.sub
      (hshift.add_const (prawitzCorrectionPreimage (-t)))
  have hraw :
      Tendsto
        (fun r : ℝ => (1 / 2 : ℂ) *
          (prawitzTentC (-t) -
            (prawitzAbelShiftPreimage r (-t) +
              prawitzCorrectionPreimage (-t))))
        (nhds 1)
        (nhds ((1 / 2 : ℂ) *
          (prawitzTentC (-t) -
            (-Complex.I * (((1 - t : ℝ) : ℂ)) *
                Complex.cot ((Real.pi : ℂ) * (t : ℂ)) +
              prawitzCorrectionPreimage (-t))))) :=
    tendsto_const_nhds.mul hdiff
  have hlimit :
      (1 / 2 : ℂ) *
          (prawitzTentC (-t) -
            (-Complex.I * (((1 - t : ℝ) : ℂ)) *
                Complex.cot ((Real.pi : ℂ) * (t : ℂ)) +
              prawitzCorrectionPreimage (-t))) =
        prawitzKernel t := by
    have htNe : t ≠ 1 := ht1.ne
    have hcot :
        Complex.cot ((Real.pi : ℂ) * (t : ℂ)) =
          ((Real.cot (Real.pi * t) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_cot]
    rw [prawitzTentC, htentNeg, hcorrNeg, hcot,
      prawitzKernel, if_neg htNe]
    push_cast
    ring
  rw [hlimit] at hraw
  simpa only [prawitzAbelUpperPreimage, prawitzAbelHPreimage] using hraw

theorem tendsto_prawitzAbelUpperPair
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Tendsto (fun r : ℝ => prawitzAbelUpperPair mu r t) (nhds 1)
      (nhds (((2 *
        (charFun mu (2 * Real.pi * t) * prawitzKernel t).re : ℝ) : ℂ))) := by
  have hneg := tendsto_prawitzAbelUpperPreimage_neg_eq_kernel ht0 ht1
  have hpos :
      Tendsto (fun r : ℝ => prawitzAbelUpperPreimage r t) (nhds 1)
        (nhds (prawitzTentC t - prawitzKernel t)) := by
    have hconst : Tendsto (fun _r : ℝ => prawitzTentC t) (nhds 1)
        (nhds (prawitzTentC t)) := tendsto_const_nhds
    have h := hconst.sub hneg
    convert h using 1
    funext r
    exact prawitzAbelUpperPreimage_eq_tent_sub_neg r ht0 ht1
  have hφpos : Tendsto
      (fun _r : ℝ => charFun mu (2 * Real.pi * t)) (nhds 1)
      (nhds (charFun mu (2 * Real.pi * t))) := tendsto_const_nhds
  have hφneg : Tendsto
      (fun _r : ℝ => charFun mu (-(2 * Real.pi * t))) (nhds 1)
      (nhds (charFun mu (-(2 * Real.pi * t)))) := tendsto_const_nhds
  have hpair := (hφpos.mul hneg).add (hφneg.mul hpos)
  rw [← charFun_kernel_pair_eq_two_re mu ht0 ht1] at ⊢
  exact hpair

/-- Dominated convergence for the paired frequency integral.  The finite
first moment is used exactly once, to cancel the `1/t` Abel envelope. -/
theorem tendsto_integral_prawitzAbelUpperPair
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hint : Integrable (id : ℝ → ℝ) mu) :
    Tendsto
      (fun r : ℝ => ∫ t in (0 : ℝ)..1, prawitzAbelUpperPair mu r t)
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ t in (0 : ℝ)..1,
        ((2 * (charFun mu (2 * Real.pi * t) * prawitzKernel t).re : ℝ) : ℂ))) := by
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [nhdsWithin_le_nhds
        (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      self_mem_nhdsWithin] with r hr0 hr1
    let f : ℝ → ℂ := fun xi => charFun mu (-(2 * Real.pi * xi)) *
      prawitzAbelUpperPreimage r xi
    have harg : Measurable fun xi : ℝ => -(2 * Real.pi * xi) := by fun_prop
    have hf : Integrable f :=
      (integrable_prawitzAbelUpperPreimage hr0 hr1).bdd_mul
        (measurable_charFun.comp harg).aestronglyMeasurable
        (Filter.Eventually.of_forall fun xi => norm_charFun_le_one _)
    have hsum : Integrable (fun t : ℝ => f (-t) + f t) :=
      hf.comp_neg.add hf
    have heq : (fun t : ℝ => prawitzAbelUpperPair mu r t) =
        (fun t : ℝ => f (-t) + f t) := by
      funext t
      dsimp only [prawitzAbelUpperPair, f]
      congr 1 <;> ring_nf
    change AEStronglyMeasurable (fun t : ℝ => prawitzAbelUpperPair mu r t)
      (volume.restrict (Set.Ioc (0 : ℝ) 1))
    rw [heq]
    exact hsum.aestronglyMeasurable.restrict
  · refine ⟨1 + 8 * Real.pi * ∫ y : ℝ, |y| ∂mu, ?_⟩
    filter_upwards [nhdsWithin_le_nhds
        (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      self_mem_nhdsWithin] with r hr0 hr1
    have hneVol : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by
      simpa only [ae_iff, not_ne_iff, Set.setOf_eq_eq_singleton] using
        (measure_singleton (μ := volume) (1 : ℝ))
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hneVol] with t ht hne
    exact norm_prawitzAbelUpperPair_le_firstMoment mu hint hr0 hr1 ht.1
      (lt_of_le_of_ne ht.2 hne)
  · have hneVol : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by
      simpa only [ae_iff, not_ne_iff, Set.setOf_eq_eq_singleton] using
        (measure_singleton (μ := volume) (1 : ℝ))
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hneVol] with t ht hne
    exact (tendsto_prawitzAbelUpperPair mu ht.1
      (lt_of_le_of_ne ht.2 hne)).mono_left inf_le_left

/-- The positive-frequency side of the lower Abel representative converges
to the negative Prawitz kernel. -/
theorem tendsto_prawitzAbelLowerPreimage_eq_neg_kernel
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Tendsto (fun r : ℝ => prawitzAbelLowerPreimage r t)
      (nhds 1) (nhds (-prawitzKernel t)) := by
  have htent : StatLean.HypothesisTesting.tent t = 1 - t :=
    StatLean.HypothesisTesting.tent_of_mem_Icc_zero_one ⟨ht0.le, ht1.le⟩
  have hcorr :
      prawitzCorrectionPreimage t = Complex.I / (Real.pi : ℂ) := by
    have hpos : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht0, ht1.le⟩
    have hnotNeg : t ∉ Set.Ioc (-1 : ℝ) 0 := by
      intro h
      exact (not_le_of_gt ht0) h.2
    simp [prawitzCorrectionPreimage, hpos, hnotNeg]
  have hshift :
      Tendsto (fun r : ℝ => prawitzAbelShiftPreimage r t)
        (nhds 1)
        (nhds (Complex.I * (((1 - t : ℝ) : ℂ)) *
          Complex.cot ((Real.pi : ℂ) * (t : ℂ)))) := by
    have hbase := (tendsto_prawitzAbelPhase_mul_tent ht0 ht1).neg
    convert hbase using 1
    · funext r
      unfold prawitzAbelShiftPreimage
      rw [prawitzAbelPhase_neg]
      ring
    · ring
  have hdiff :
      Tendsto
        (fun r : ℝ =>
          -(prawitzAbelShiftPreimage r t + prawitzCorrectionPreimage t) -
            prawitzTentC t)
        (nhds 1)
        (nhds (-(Complex.I * (((1 - t : ℝ) : ℂ)) *
              Complex.cot ((Real.pi : ℂ) * (t : ℂ)) +
            prawitzCorrectionPreimage t) - prawitzTentC t)) :=
    (hshift.add_const (prawitzCorrectionPreimage t)).neg.sub
      tendsto_const_nhds
  have hraw :
      Tendsto
        (fun r : ℝ => (1 / 2 : ℂ) *
          (-(prawitzAbelShiftPreimage r t + prawitzCorrectionPreimage t) -
            prawitzTentC t))
        (nhds 1)
        (nhds ((1 / 2 : ℂ) *
          (-(Complex.I * (((1 - t : ℝ) : ℂ)) *
                Complex.cot ((Real.pi : ℂ) * (t : ℂ)) +
              prawitzCorrectionPreimage t) - prawitzTentC t))) :=
    tendsto_const_nhds.mul hdiff
  have hlimit :
      (1 / 2 : ℂ) *
          (-(Complex.I * (((1 - t : ℝ) : ℂ)) *
                Complex.cot ((Real.pi : ℂ) * (t : ℂ)) +
              prawitzCorrectionPreimage t) - prawitzTentC t) =
        -prawitzKernel t := by
    have htNe : t ≠ 1 := ht1.ne
    have hcot :
        Complex.cot ((Real.pi : ℂ) * (t : ℂ)) =
          ((Real.cot (Real.pi * t) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_cot]
    rw [prawitzTentC, htent, hcorr, hcot,
      prawitzKernel, if_neg htNe]
    push_cast
    ring
  rw [hlimit] at hraw
  simpa only [prawitzAbelLowerPreimage, prawitzAbelHPreimage] using hraw

private theorem continuous_fourier_of_integrable
    {g : ℝ → ℂ} (hg : Integrable g) :
    Continuous (FourierTransform.fourier g) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    continuous_inner hg

/-- Dominated convergence moves the Abel limit through the upper-majorant
expectation. -/
theorem tendsto_integral_fourier_prawitzAbelUpperPreimage
    (mu : Measure ℝ) [IsFiniteMeasure mu] :
    Tendsto
      (fun r : ℝ => ∫ z : ℝ,
        FourierTransform.fourier (prawitzAbelUpperPreimage r) z ∂mu)
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ z : ℝ, ((prawitzUpperNonconstant z : ℝ) : ℂ) ∂mu)) := by
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [nhdsWithin_le_nhds
        (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      self_mem_nhdsWithin] with r hr0 hr1
    exact (continuous_fourier_of_integrable
      (integrable_prawitzAbelUpperPreimage hr0 hr1)).aestronglyMeasurable
  · refine ⟨3, ?_⟩
    filter_upwards [nhdsWithin_le_nhds
        (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      self_mem_nhdsWithin] with r hr0 hr1
    exact Filter.Eventually.of_forall fun z =>
      norm_fourier_prawitzAbelUpperPreimage_le_three hr0 hr1 z
  · exact Filter.Eventually.of_forall fun z => by
      convert tendsto_fourier_prawitzAbelUpperPreimage z using 1
      unfold prawitzUpperNonconstant prawitzJC
      push_cast
      ring

/-- Exact positive-frequency representation of the integrated Vaaler upper
majorant.  It is obtained by identifying the physical-space and paired
frequency-space limits of the same Abel family. -/
theorem integral_prawitzUpperNonconstant_eq_kernel
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hint : Integrable (id : ℝ → ℝ) mu) :
    (∫ z : ℝ, ((prawitzUpperNonconstant z : ℝ) : ℂ) ∂mu) =
      ∫ t in (0 : ℝ)..1,
        ((2 * (charFun mu (2 * Real.pi * t) * prawitzKernel t).re : ℝ) : ℂ) := by
  have hpair := tendsto_integral_prawitzAbelUpperPair mu hint
  have hpairAsPhysical : Tendsto
      (fun r : ℝ => ∫ z : ℝ,
        FourierTransform.fourier (prawitzAbelUpperPreimage r) z ∂mu)
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ t in (0 : ℝ)..1,
        ((2 * (charFun mu (2 * Real.pi * t) * prawitzKernel t).re : ℝ) : ℂ))) := by
    refine Tendsto.congr' ?_ hpair
    filter_upwards [nhdsWithin_le_nhds
        (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      self_mem_nhdsWithin] with r hr0 hr1
    rw [integral_fourier_prawitzAbelUpperPreimage_eq_charFun mu hr0 hr1,
      integral_charFun_mul_prawitzAbelUpperPreimage_eq_pair mu hr0 hr1]
  exact tendsto_nhds_unique
    (tendsto_integral_fourier_prawitzAbelUpperPreimage mu) hpairAsPhysical

theorem integral_prawitzUpperNonconstant_eq_two_mul_integral_re
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hint : Integrable (id : ℝ → ℝ) mu) :
    (∫ z : ℝ, prawitzUpperNonconstant z ∂mu) =
      2 * ∫ t in (0 : ℝ)..1,
        (charFun mu (2 * Real.pi * t) * prawitzKernel t).re := by
  have h := integral_prawitzUpperNonconstant_eq_kernel mu hint
  rw [integral_complex_ofReal, intervalIntegral.integral_ofReal] at h
  have h' : (∫ z : ℝ, prawitzUpperNonconstant z ∂mu) =
      ∫ t in (0 : ℝ)..1,
        2 * (charFun mu (2 * Real.pi * t) * prawitzKernel t).re := by
    exact_mod_cast h
  rw [intervalIntegral.integral_const_mul] at h'
  exact h'

theorem integrable_id_prawitzAffineLaw
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hint : Integrable (id : ℝ → ℝ) mu) (T x : ℝ) :
    Integrable (id : ℝ → ℝ) (prawitzAffineLaw mu T x) := by
  rw [prawitzAffineLaw]
  refine (integrable_map_measure (by fun_prop) (by fun_prop)).2 ?_
  change Integrable (fun y : ℝ => prawitzAffineScale T * (y - x)) mu
  exact (hint.sub (integrable_const x)).const_mul _

/-- The usable upper half of Prawitz's one-sided smoothing bound, at an
arbitrary spatial point and positive Fourier scale. -/
theorem lawCDF_le_half_add_prawitzKernelIntegral
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hint : Integrable (id : ℝ → ℝ) mu)
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    lawCDF mu x ≤ 1 / 2 +
      2 * ∫ t in (0 : ℝ)..1,
        (prawitzKernel t *
          Complex.exp (-(((T * t * x : ℝ) : ℂ) * Complex.I)) *
          charFun mu (T * t)).re := by
  let nu := prawitzAffineLaw mu T x
  have hnu := lawCDF_zero_le_half_add_integral_prawitzUpperNonconstant nu
  have hCDF : lawCDF nu 0 = lawCDF mu x :=
    lawCDF_prawitzAffineLaw_zero mu hT x
  have hrep := integral_prawitzUpperNonconstant_eq_two_mul_integral_re nu
    (integrable_id_prawitzAffineLaw mu hint T x)
  rw [hCDF, hrep] at hnu
  convert hnu using 1
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  have hchar : charFun nu (2 * Real.pi * t) =
      charFun mu (T * t) *
        Complex.exp (-(((T * t * x : ℝ) : ℂ) * Complex.I)) := by
    dsimp only [nu]
    rw [charFun_prawitzAffineLaw]
    unfold prawitzAffineScale
    congr 2
    · field_simp [Real.pi_ne_zero]
    · congr 1
      push_cast
      field_simp [Real.pi_ne_zero]
  dsimp only
  rw [hchar]
  ring

/-- The unit-modulus spatial oscillation in Prawitz's scaled formula. -/
def prawitzOscillation (T x t : ℝ) : ℂ :=
  Complex.exp (-(((T * t * x : ℝ) : ℂ) * Complex.I))

/-- The standard-normal characteristic function at frequency `T t`. -/
def prawitzGaussianFactor (T t : ℝ) : ℂ :=
  Complex.exp (-((T * t : ℂ) ^ 2) / 2)

/-- The singular kernel in Gaussian Fourier inversion. -/
def prawitzSingularKernel (t : ℝ) : ℂ :=
  Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)

theorem norm_prawitzOscillation (T x t : ℝ) :
    ‖prawitzOscillation T x t‖ = 1 := by
  rw [prawitzOscillation, show
      -(((T * t * x : ℝ) : ℂ) * Complex.I) =
        (((-(T * t * x) : ℝ) : ℂ) * Complex.I) by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem prawitzGaussianFactor_eq_ofReal (T t : ℝ) :
    prawitzGaussianFactor T t =
      ((Real.exp (-(T ^ 2 * t ^ 2) / 2) : ℝ) : ℂ) := by
  rw [prawitzGaussianFactor, show
      -((T * t : ℂ) ^ 2) / 2 =
        (((-(T ^ 2 * t ^ 2) / 2 : ℝ) : ℂ)) by push_cast; ring,
    ← Complex.ofReal_exp]

theorem norm_prawitzGaussianFactor (T t : ℝ) :
    ‖prawitzGaussianFactor T t‖ =
      Real.exp (-(T ^ 2 * t ^ 2) / 2) := by
  rw [prawitzGaussianFactor_eq_ofReal, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem norm_prawitzGaussianFactor_sub_one_le (T t : ℝ) :
    ‖prawitzGaussianFactor T t - 1‖ ≤ T ^ 2 * t ^ 2 / 2 := by
  have ha : 0 ≤ T ^ 2 * t ^ 2 / 2 := by positivity
  have hexp : Real.exp (-(T ^ 2 * t ^ 2) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg (sq_nonneg T) (sq_nonneg t)])
  have hlinear := Real.one_sub_le_exp_neg (T ^ 2 * t ^ 2 / 2)
  rw [show -(T ^ 2 * t ^ 2 / 2) = -(T ^ 2 * t ^ 2) / 2 by ring] at hlinear
  rw [prawitzGaussianFactor_eq_ofReal, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hexp)]
  linarith

theorem norm_prawitzSingularKernel {t : ℝ} (ht : 0 < t) :
    ‖prawitzSingularKernel t‖ = 1 / (2 * Real.pi * t) := by
  rw [prawitzSingularKernel, norm_div, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_pos (mul_pos (mul_pos two_pos Real.pi_pos) ht), one_div]

theorem prawitzKernel_sub_singularKernel_eq_correction
    {t : ℝ} (ht : t ≠ 0) :
    prawitzKernel t - prawitzSingularKernel t =
      prawitzKernelCorrection t := by
  rw [prawitzKernelCorrection, if_neg ht, prawitzSingularKernel]

/-- The characteristic-function difference in the low-frequency term is
linear at zero under a finite first absolute moment. -/
theorem norm_charFun_sub_gaussian_le
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hint : Integrable (id : ℝ → ℝ) mu)
    {T t : ℝ} (ht : 0 ≤ t) :
    ‖charFun mu (T * t) - prawitzGaussianFactor T t‖ ≤
      |T| * t * (∫ y : ℝ, |y| ∂mu) + T ^ 2 * t ^ 2 / 2 := by
  have hchar := norm_charFun_sub_one_le_firstMoment mu hint (T * t)
  have habs : |T * t| = |T| * t := by
    rw [abs_mul, abs_of_nonneg ht]
  rw [habs] at hchar
  calc
    ‖charFun mu (T * t) - prawitzGaussianFactor T t‖ =
        ‖(charFun mu (T * t) - 1) -
          (prawitzGaussianFactor T t - 1)‖ := by ring_nf
    _ ≤ ‖charFun mu (T * t) - 1‖ +
        ‖prawitzGaussianFactor T t - 1‖ := norm_sub_le _ _
    _ ≤ |T| * t * (∫ y : ℝ, |y| ∂mu) + T ^ 2 * t ^ 2 / 2 :=
      add_le_add hchar (norm_prawitzGaussianFactor_sub_one_le T t)

/-- The first norm term in the Prawitz functional is interval-integrable;
the linear characteristic-function cancellation removes the kernel's
`1 / t` singularity. -/
theorem intervalIntegrable_prawitzLowDifference
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hint : Integrable (id : ℝ → ℝ) mu)
    (T : ℝ) {t0 : ℝ} (ht00 : 0 ≤ t0) (ht01 : t0 ≤ 1) :
    IntervalIntegrable
      (fun t : ℝ => ‖prawitzKernel t‖ *
        ‖charFun mu (T * t) - prawitzGaussianFactor T t‖)
      volume 0 t0 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht00]
  let M : ℝ := ∫ y : ℝ, |y| ∂mu
  have hM : 0 ≤ M := integral_nonneg fun y => abs_nonneg y
  refine Measure.integrableOn_of_bounded
    (M := 2 * (|T| * M + T ^ 2 / 2)) measure_Ioc_lt_top.ne ?_ ?_
  · have hgauss : Measurable (fun t : ℝ => prawitzGaussianFactor T t) := by
      unfold prawitzGaussianFactor
      fun_prop
    have harg : Measurable (fun t : ℝ => T * t) :=
      measurable_const.mul measurable_id
    exact ((measurable_prawitzKernel.norm).mul
      ((((measurable_charFun (μ := mu)).comp harg).sub hgauss).norm)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    have ht1 : t ≤ 1 := ht.2.trans ht01
    have hdiff := norm_charFun_sub_gaussian_le mu hint (T := T) ht.1.le
    have hdiff' :
        ‖charFun mu (T * t) - prawitzGaussianFactor T t‖ ≤
          t * (|T| * M + T ^ 2 / 2) := by
      dsimp only [M] at hdiff ⊢
      have htSq : t ^ 2 ≤ t := by
        nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht1)]
      have hT2 : 0 ≤ T ^ 2 := sq_nonneg T
      nlinarith
    calc
      ‖prawitzKernel t‖ *
          ‖charFun mu (T * t) - prawitzGaussianFactor T t‖ ≤
        (2 / t) * (t * (|T| * M + T ^ 2 / 2)) := by
          exact mul_le_mul
            (norm_prawitzKernel_le_two_div_of_mem_Ioc ht.1 ht1) hdiff'
            (norm_nonneg _) (div_nonneg (by norm_num) ht.1.le)
      _ = 2 * (|T| * M + T ^ 2 / 2) := by
        field_simp [ht.1.ne']

/-- Away from zero, the second norm term in the Prawitz functional is
bounded and interval-integrable. -/
theorem intervalIntegrable_prawitzHighModulus
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {t0 : ℝ} (ht00 : 0 < t0) (ht01 : t0 ≤ 1) (T : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => ‖prawitzKernel t‖ * ‖charFun mu (T * t)‖)
      volume t0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht01]
  apply Measure.integrableOn_of_bounded (M := 2 / t0) measure_Ioc_lt_top.ne
  · exact ((measurable_prawitzKernel.norm).mul
      (((measurable_charFun (μ := mu)).comp (by fun_prop)).norm)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    have htpos : 0 < t := ht00.trans ht.1
    calc
      ‖prawitzKernel t‖ * ‖charFun mu (T * t)‖ ≤
          (2 / t) * 1 := by
        gcongr
        · exact norm_prawitzKernel_le_two_div_of_mem_Ioc htpos ht.2
        · exact norm_charFun_le_one _
      _ ≤ 2 / t0 := by
        rw [mul_one]
        exact div_le_div_of_nonneg_left (by norm_num) ht00 ht.1.le

/-- The removable kernel correction supplies the third integrable norm term. -/
theorem intervalIntegrable_prawitzCorrectionGaussian
    (T : ℝ) {t0 : ℝ} (ht00 : 0 ≤ t0) (ht01 : t0 ≤ 1) :
    IntervalIntegrable
      (fun t : ℝ => ‖prawitzKernelCorrection t‖ *
        Real.exp (-(T ^ 2 * t ^ 2) / 2))
      volume 0 t0 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht00]
  apply Measure.integrableOn_of_bounded (M := 10) measure_Ioc_lt_top.ne
  · exact ((measurable_prawitzKernelCorrection.norm).mul (by fun_prop)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
    calc
      ‖prawitzKernelCorrection t‖ *
          Real.exp (-(T ^ 2 * t ^ 2) / 2) ≤ 10 * 1 := by
        gcongr
        · exact norm_prawitzKernelCorrection_le_ten ht.1.le (ht.2.trans ht01)
        · exact Real.exp_le_one_iff.mpr
            (by nlinarith [mul_nonneg (sq_nonneg T) (sq_nonneg t)])
      _ = 10 := by ring

/-- Gaussian decay makes the final `1 / t` tail absolutely integrable once
the lower endpoint is positive. -/
theorem integrableOn_prawitzGaussianTail
    {T t0 : ℝ} (hT : 0 < T) (ht0 : 0 < t0) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(T ^ 2 * t ^ 2) / 2) / t)
      (Set.Ici t0) := by
  have hb : 0 < T ^ 2 / 2 := by positivity
  have hgauss : Integrable
      (fun t : ℝ => (1 / t0) * Real.exp (-(T ^ 2 / 2) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul (1 / t0)
  refine hgauss.integrableOn.mono'
    (((by fun_prop : Measurable fun t : ℝ =>
      Real.exp (-(T ^ 2 * t ^ 2) / 2)).div measurable_id).aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  rw [Real.norm_eq_abs, abs_div,
    abs_of_pos (Real.exp_pos _), abs_of_pos (ht0.trans_le ht)]
  have hinv : 1 / t ≤ 1 / t0 := one_div_le_one_div_of_le ht0 ht
  calc
    Real.exp (-(T ^ 2 * t ^ 2) / 2) / t =
        (1 / t) * Real.exp (-(T ^ 2 / 2) * t ^ 2) := by ring
    _ ≤ (1 / t0) * Real.exp (-(T ^ 2 / 2) * t ^ 2) := by gcongr

theorem re_prawitzSingularKernel_mul_oscillation_mul_gaussian
    (T x t : ℝ) :
    (prawitzSingularKernel t * prawitzOscillation T x t *
      prawitzGaussianFactor T t).re =
    Real.exp (-(T * t) ^ 2 / 2) * Real.sin (T * t * x) /
      (2 * Real.pi * t) := by
  rw [prawitzSingularKernel, prawitzOscillation, prawitzGaussianFactor]
  rw [show -((T * t : ℂ) ^ 2) / 2 =
      (((-(T * t) ^ 2 / 2 : ℝ) : ℂ)) by push_cast; ring,
    ← Complex.ofReal_exp]
  rw [show -(((T * t * x : ℝ) : ℂ) * Complex.I) =
      (((-(T * t * x) : ℝ) : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg]
  by_cases ht : 2 * Real.pi * t = 0
  · rw [ht]
    simp
  · have htne : t ≠ 0 := by
      intro h
      apply ht
      rw [h]
      ring
    have hdiv : Complex.I / ((2 * Real.pi * t : ℝ) : ℂ) =
        (((1 / (2 * Real.pi * t) : ℝ) : ℂ)) * Complex.I := by
      apply (div_eq_iff (Complex.ofReal_ne_zero.mpr ht)).2
      push_cast
      field_simp [ht, htne, Real.pi_ne_zero]
    rw [hdiv]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, zero_sub, add_zero, sub_zero]
    field_simp [ht, htne, Real.pi_ne_zero]
    ring

/-- Gaussian sine inversion in the exact complex-kernel normalization used
by the Prawitz upper bound. -/
theorem lawCDF_standardNormal_eq_half_add_singularIntegral
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    lawCDF standardNormalLaw x = 1 / 2 +
      2 * ∫ t in Set.Ioi (0 : ℝ),
        (prawitzSingularKernel t * prawitzOscillation T x t *
          prawitzGaussianFactor T t).re := by
  have h := integral_Ioi_exp_neg_scaled_sq_mul_sin_div hT x
  have hpoint : ∀ t : ℝ,
      (prawitzSingularKernel t * prawitzOscillation T x t *
        prawitzGaussianFactor T t).re =
      (1 / (2 * Real.pi)) *
        (Real.exp (-(T * t) ^ 2 / 2) * Real.sin (T * t * x) / t) := by
    intro t
    rw [re_prawitzSingularKernel_mul_oscillation_mul_gaussian]
    by_cases ht : t = 0
    · subst t
      simp
    · field_simp [Real.pi_ne_zero, ht]
  rw [show (fun t : ℝ =>
      (prawitzSingularKernel t * prawitzOscillation T x t *
        prawitzGaussianFactor T t).re) =
      (fun t : ℝ => (1 / (2 * Real.pi)) *
        (Real.exp (-(T * t) ^ 2 / 2) * Real.sin (T * t * x) / t)) by
      funext t; exact hpoint t,
    MeasureTheory.integral_const_mul, h]
  field_simp [Real.pi_ne_zero]
  ring

/-- Dominated convergence moves the Abel limit through the lower-minorant
expectation. -/
theorem tendsto_integral_fourier_prawitzAbelLowerPreimage
    (mu : Measure ℝ) [IsFiniteMeasure mu] :
    Tendsto
      (fun r : ℝ => ∫ z : ℝ,
        FourierTransform.fourier (prawitzAbelLowerPreimage r) z ∂mu)
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ z : ℝ, ((prawitzLowerNonconstant z : ℝ) : ℂ) ∂mu)) := by
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [nhdsWithin_le_nhds
        (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      self_mem_nhdsWithin] with r hr0 hr1
    exact (continuous_fourier_of_integrable
      (integrable_prawitzAbelLowerPreimage hr0 hr1)).aestronglyMeasurable
  · refine ⟨3, ?_⟩
    filter_upwards [nhdsWithin_le_nhds
        (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      self_mem_nhdsWithin] with r hr0 hr1
    exact Filter.Eventually.of_forall fun z =>
      norm_fourier_prawitzAbelLowerPreimage_le_three hr0 hr1 z
  · exact Filter.Eventually.of_forall fun z => by
      convert tendsto_fourier_prawitzAbelLowerPreimage z using 1
      unfold prawitzLowerNonconstant prawitzJC
      push_cast
      ring

end

end BerryEsseen
