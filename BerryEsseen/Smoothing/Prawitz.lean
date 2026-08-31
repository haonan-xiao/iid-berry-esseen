import BerryEsseen.CharacteristicFunction.OneStepDisk
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The finite-first-moment Prawitz smoothing boundary

This module fixes the exact kernel and four-term functional in Route B (4.1)--
(4.2).  `PrawitzSmoothingBound` is an explicit proposition, not an axiom: the
subsequent source-to-scalar reduction may consume it while the Fourier
majorant construction is proved in this module.
-/

open MeasureTheory ProbabilityTheory intervalIntegral
open scoped ENNReal NNReal Real

namespace BerryEsseen

noncomputable section

/-- The positive-frequency Prawitz kernel (4.1), with the removable value at
`t = 1` filled by its limit.  The formula at `t = 0` is irrelevant to the
Lebesgue integrals; the singular cancellation is represented separately by
`prawitzKernelCorrection`. -/
def prawitzKernel (t : ℝ) : ℂ :=
  if t = 1 then 0
  else ((1 - t) / 2 : ℝ) +
    (((1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi) / 2 : ℝ) * Complex.I

/-- The kernel after subtracting the normal-inversion singularity.  Its value
at zero is the removable limit `1/2`. -/
def prawitzKernelCorrection (t : ℝ) : ℂ :=
  if t = 0 then (1 / 2 : ℝ)
  else prawitzKernel t - Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)

theorem prawitzKernel_one : prawitzKernel 1 = 0 := by
  simp [prawitzKernel]

theorem prawitzKernelCorrection_zero :
    prawitzKernelCorrection 0 = (1 / 2 : ℝ) := by
  simp [prawitzKernelCorrection]

theorem measurable_prawitzKernel : Measurable prawitzKernel := by
  unfold prawitzKernel
  refine Measurable.ite (measurableSet_singleton 1) measurable_const ?_
  simp only [Real.cot_eq_cos_div_sin]
  fun_prop

theorem measurable_prawitzKernelCorrection :
    Measurable prawitzKernelCorrection := by
  unfold prawitzKernelCorrection
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  exact measurable_prawitzKernel.sub (by fun_prop)

theorem abs_cot_pi_le_inv_two_mul {t : ℝ}
    (ht : 0 < t) (hhalf : t ≤ (1 : ℝ) / 2) :
    |Real.cot (Real.pi * t)| ≤ 1 / (2 * t) := by
  have hx0 : 0 ≤ Real.pi * t := mul_nonneg Real.pi_pos.le ht.le
  have hxhalf : Real.pi * t ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hsinLower : 2 * t ≤ Real.sin (Real.pi * t) := by
    have h := Real.mul_le_sin hx0 hxhalf
    convert h using 1 <;> field_simp [Real.pi_ne_zero]
  have hsinPos : 0 < Real.sin (Real.pi * t) :=
    lt_of_lt_of_le (mul_pos two_pos ht) hsinLower
  rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsinPos]
  calc
    |Real.cos (Real.pi * t)| / Real.sin (Real.pi * t) ≤
        1 / Real.sin (Real.pi * t) := by
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hsinPos.le
    _ ≤ 1 / (2 * t) := by
      exact one_div_le_one_div_of_le (mul_pos two_pos ht) hsinLower

/-- A deliberately coarse bound exposing the `1/t` singularity at zero. -/
theorem norm_prawitzKernel_le_two_div {t : ℝ}
    (ht : 0 < t) (hhalf : t ≤ (1 : ℝ) / 2) :
    ‖prawitzKernel t‖ ≤ 2 / t := by
  have ht1 : t ≠ 1 := by linarith
  have honeSub : 0 ≤ 1 - t := by linarith
  have honeSubLe : 1 - t ≤ 1 := by linarith
  have hcot := abs_cot_pi_le_inv_two_mul ht hhalf
  have hpiInv : 0 ≤ 1 / Real.pi := by positivity
  have htInv : 0 ≤ 1 / t := by positivity
  rw [prawitzKernel, if_neg ht1]
  calc
    ‖((1 - t) / 2 : ℝ) +
        ((((1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi) / 2 : ℝ) *
          Complex.I)‖ ≤
        ‖(((1 - t) / 2 : ℝ) : ℂ)‖ +
          ‖((((1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi) / 2 : ℝ) : ℂ) *
            Complex.I‖ := norm_add_le _ _
    _ = |(1 - t) / 2| +
          |((1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi) / 2| := by
      have hrealNorm :
          ‖(((1 - t) / 2 : ℝ) : ℂ)‖ = |(1 - t) / 2| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      have himagNorm :
          ‖((((1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi) / 2 : ℝ) : ℂ) *
              Complex.I‖ =
            |((1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi) / 2| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
      rw [hrealNorm, himagNorm]
    _ ≤ ((1 : ℝ) / 2) + ((1 / (2 * t) + 1 / Real.pi) / 2) := by
      have hreal : |(1 - t) / 2| ≤ (1 : ℝ) / 2 := by
        rw [abs_of_nonneg (div_nonneg honeSub (by norm_num))]
        gcongr
      have himag :
          |((1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi) / 2| ≤
            (1 / (2 * t) + 1 / Real.pi) / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        refine (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 ?_
        calc
          |(1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi| ≤
              |(1 - t) * Real.cot (Real.pi * t)| + |1 / Real.pi| := abs_add_le _ _
          _ = (1 - t) * |Real.cot (Real.pi * t)| + 1 / Real.pi := by
            rw [abs_mul, abs_of_nonneg honeSub, abs_of_nonneg hpiInv]
          _ ≤ 1 * (1 / (2 * t)) + 1 / Real.pi := by gcongr
          _ = 1 / (2 * t) + 1 / Real.pi := by ring
      exact add_le_add hreal himag
    _ ≤ 2 / t := by
      have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hpiTerm : 1 / Real.pi ≤ 1 := by
        exact (one_div_le_one_div_of_le one_pos (by linarith)).trans_eq (one_div_one)
      have htLeOne : t ≤ 1 := hhalf.trans (by norm_num)
      have honeLeInv : (1 : ℝ) ≤ 1 / t := (le_div_iff₀ ht).2 (by simpa using htLeOne)
      calc
        (1 : ℝ) / 2 + (1 / (2 * t) + 1 / Real.pi) / 2 ≤
            1 / 2 + (1 / (2 * t) + 1) / 2 := by gcongr
        _ ≤ 2 / t := by
          field_simp [ht.ne']
          nlinarith [hhalf]

theorem abs_cot_pi_eq_one_sub (t : ℝ) :
    |Real.cot (Real.pi * t)| = |Real.cot (Real.pi * (1 - t))| := by
  have harg : Real.pi * t = Real.pi - Real.pi * (1 - t) := by ring
  rw [harg, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
    Real.cos_pi_sub, Real.sin_pi_sub, abs_div, abs_div, abs_neg]

/-- The apparent singularity at `t = 1` is cancelled by the factor `1-t`. -/
theorem norm_prawitzKernel_le_two_of_half_le {t : ℝ}
    (hhalf : (1 : ℝ) / 2 ≤ t) (ht : t ≤ 1) :
    ‖prawitzKernel t‖ ≤ 2 := by
  obtain rfl | ht1 := ht.eq_or_lt
  · simp [prawitzKernel]
  have hsPos : 0 < 1 - t := sub_pos.2 ht1
  have hsHalf : 1 - t ≤ (1 : ℝ) / 2 := by linarith
  have htNe : t ≠ 1 := ht1.ne
  have hcotS := abs_cot_pi_le_inv_two_mul hsPos hsHalf
  have hcot : |Real.cot (Real.pi * t)| ≤ 1 / (2 * (1 - t)) := by
    rw [abs_cot_pi_eq_one_sub]
    exact hcotS
  have hprod : (1 - t) * |Real.cot (Real.pi * t)| ≤ (1 : ℝ) / 2 := by
    calc
      (1 - t) * |Real.cot (Real.pi * t)| ≤
          (1 - t) * (1 / (2 * (1 - t))) :=
        mul_le_mul_of_nonneg_left hcot hsPos.le
      _ = (1 : ℝ) / 2 := by field_simp [hsPos.ne']
  have hpiTerm : 1 / Real.pi ≤ 1 := by
    exact (one_div_le_one_div_of_le one_pos (by linarith [Real.pi_gt_three])).trans_eq
      (one_div_one)
  rw [prawitzKernel, if_neg htNe]
  calc
    ‖((1 - t) / 2 : ℝ) +
        ((((1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi) / 2 : ℝ) *
          Complex.I)‖ ≤
        ‖(((1 - t) / 2 : ℝ) : ℂ)‖ +
          ‖((((1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi) / 2 : ℝ) : ℂ) *
            Complex.I‖ := norm_add_le _ _
    _ = |(1 - t) / 2| +
          |((1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi) / 2| := by
      rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_I, mul_one]
    _ ≤ ((1 : ℝ) / 2) + (((1 : ℝ) / 2 + 1) / 2) := by
      have hreal : |(1 - t) / 2| ≤ (1 : ℝ) / 2 := by
        rw [abs_of_nonneg (div_nonneg hsPos.le (by norm_num))]
        gcongr
        linarith
      have himag :
          |((1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi) / 2| ≤
            ((1 : ℝ) / 2 + 1) / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        refine (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 ?_
        calc
          |(1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi| ≤
              |(1 - t) * Real.cot (Real.pi * t)| + |1 / Real.pi| := abs_add_le _ _
          _ = (1 - t) * |Real.cot (Real.pi * t)| + 1 / Real.pi := by
            rw [abs_mul, abs_of_pos hsPos, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.pi)]
          _ ≤ (1 : ℝ) / 2 + 1 := add_le_add hprod hpiTerm
      exact add_le_add hreal himag
    _ ≤ 2 := by norm_num

/-- A single `2 / t` envelope valid across the whole open positive
frequency band. -/
theorem norm_prawitzKernel_le_two_div_of_mem_Ioc {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖prawitzKernel t‖ ≤ 2 / t := by
  by_cases hhalf : t ≤ (1 : ℝ) / 2
  · exact norm_prawitzKernel_le_two_div ht0 hhalf
  · have hhalf' : (1 : ℝ) / 2 ≤ t := le_of_not_ge hhalf
    calc
      ‖prawitzKernel t‖ ≤ 2 :=
        norm_prawitzKernel_le_two_of_half_le hhalf' ht1
      _ ≤ 2 / t := by
        exact (le_div_iff₀ ht0).2 (by nlinarith)

/-- Near zero, the singular terms in `cot (π t)` and `1 / (π t)` cancel
uniformly.  The deliberately coarse constant is enough to establish
integrability of the kernel correction. -/
theorem abs_cot_pi_sub_inv_le_two {t : ℝ}
    (ht0 : 0 < t) (htq : t ≤ (1 : ℝ) / 4) :
    |Real.cot (Real.pi * t) - 1 / (Real.pi * t)| ≤ 2 := by
  let x := Real.pi * t
  have hx0 : 0 < x := mul_pos Real.pi_pos ht0
  have hxq : x ≤ Real.pi / 4 := by dsimp [x]; nlinarith [Real.pi_pos]
  have hxhalf : x ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hx1 : x ≤ 1 := by
    dsimp [x]
    nlinarith [Real.pi_le_four]
  have hxabs : |x| ≤ 1 := by rw [abs_of_pos hx0]; exact hx1
  have hsinPos : 0 < Real.sin x :=
    lt_of_lt_of_le (mul_pos (div_pos two_pos Real.pi_pos) hx0)
      (Real.mul_le_sin hx0.le hxhalf)
  have hsinLower : 2 / Real.pi * x ≤ Real.sin x :=
    Real.mul_le_sin hx0.le hxhalf
  have hcosAbs : |Real.cos x - 1| ≤ x ^ 2 / 2 := by
    rw [abs_of_nonpos (by linarith [Real.cos_le_one x])]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hsinTaylor := Real.sin_bound hxabs
  have hsinAbs : |x - Real.sin x| ≤ x ^ 3 / 4 := by
    calc
      |x - Real.sin x| =
          |(x ^ 3 / 6) - (Real.sin x - (x - x ^ 3 / 6))| := by
            congr 1
            ring
      _ ≤ |x ^ 3 / 6| +
          |Real.sin x - (x - x ^ 3 / 6)| := abs_sub _ _
      _ ≤ x ^ 3 / 6 + x ^ 4 * (5 / 96) := by
        rw [abs_of_nonneg (by positivity : 0 ≤ x ^ 3 / 6)]
        gcongr
        simpa [abs_of_pos hx0] using hsinTaylor
      _ ≤ x ^ 3 / 4 := by
        have hx3 : 0 ≤ x ^ 3 := by positivity
        have hx4le : x ^ 4 ≤ x ^ 3 := by
          rw [pow_succ]
          exact mul_le_of_le_one_right hx3 hx1
        nlinarith
  have hnum : |x * Real.cos x - Real.sin x| ≤ 3 * x ^ 3 / 4 := by
    calc
      |x * Real.cos x - Real.sin x| =
          |x * (Real.cos x - 1) + (x - Real.sin x)| := by
            congr 1
            ring
      _ ≤ |x * (Real.cos x - 1)| + |x - Real.sin x| := abs_add_le _ _
      _ = x * |Real.cos x - 1| + |x - Real.sin x| := by
        rw [abs_mul, abs_of_pos hx0]
      _ ≤ x * (x ^ 2 / 2) + x ^ 3 / 4 := by gcongr
      _ = 3 * x ^ 3 / 4 := by ring
  have hden : 2 / Real.pi * x ^ 2 ≤ x * Real.sin x := by
    calc
      2 / Real.pi * x ^ 2 = x * (2 / Real.pi * x) := by ring
      _ ≤ x * Real.sin x := mul_le_mul_of_nonneg_left hsinLower hx0.le
  have hdenPos : 0 < x * Real.sin x := mul_pos hx0 hsinPos
  rw [Real.cot_eq_cos_div_sin]
  have heq : Real.cos x / Real.sin x - 1 / x =
      (x * Real.cos x - Real.sin x) / (x * Real.sin x) := by
    field_simp [hx0.ne', hsinPos.ne']
  rw [heq, abs_div, abs_of_pos hdenPos]
  calc
    |x * Real.cos x - Real.sin x| / (x * Real.sin x) ≤
        (3 * x ^ 3 / 4) / (2 / Real.pi * x ^ 2) := by
      exact div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 3 * Real.pi * x / 8 := by
      field_simp [hx0.ne', Real.pi_ne_zero]
      ring
    _ ≤ 2 := by
      nlinarith [Real.pi_le_four, Real.pi_pos]

/-- The subtraction in `prawitzKernelCorrection` removes the `1 / t`
singularity.  Thus the correction is uniformly bounded on the closed
positive frequency band. -/
theorem norm_prawitzKernelCorrection_le_ten {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖prawitzKernelCorrection t‖ ≤ 10 := by
  obtain rfl | htpos := ht0.eq_or_lt
  · simp [prawitzKernelCorrection]
    norm_num
  by_cases htq : t ≤ (1 : ℝ) / 4
  · have htne : t ≠ 1 := by linarith
    have hcot := abs_cot_pi_sub_inv_le_two htpos htq
    rw [prawitzKernelCorrection, if_neg htpos.ne', prawitzKernel, if_neg htne]
    have hsing :
        Complex.I / ((2 * Real.pi * t : ℝ) : ℂ) =
          (((1 / (2 * Real.pi * t) : ℝ) : ℂ)) * Complex.I := by
      have hden : 2 * Real.pi * t ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) htpos.ne'
      apply (div_eq_iff (Complex.ofReal_ne_zero.mpr hden)).2
      push_cast
      field_simp [Real.pi_ne_zero, htpos.ne']
    have heq :
        ((((1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi) / 2 : ℝ) : ℂ) *
              Complex.I -
            Complex.I / ((2 * Real.pi * t : ℝ) : ℂ) =
          (((((1 - t) *
              (Real.cot (Real.pi * t) - 1 / (Real.pi * t))) / 2 : ℝ) : ℂ)) *
            Complex.I := by
      rw [hsing]
      push_cast
      field_simp [Real.pi_ne_zero, htpos.ne']
      ring
    have hassoc :
        (((1 - t) / 2 : ℝ) : ℂ) +
            ((((1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi) / 2 : ℝ) : ℂ) *
              Complex.I -
            Complex.I / ((2 * Real.pi * t : ℝ) : ℂ) =
          (((1 - t) / 2 : ℝ) : ℂ) +
            (((((1 - t) * Real.cot (Real.pi * t) + 1 / Real.pi) / 2 : ℝ) : ℂ) *
              Complex.I - Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)) := by
      ring
    rw [hassoc, heq]
    calc
      ‖(((1 - t) / 2 : ℝ) : ℂ) +
          (((((1 - t) *
            (Real.cot (Real.pi * t) - 1 / (Real.pi * t))) / 2 : ℝ) : ℂ)) *
            Complex.I‖ ≤
          ‖(((1 - t) / 2 : ℝ) : ℂ)‖ +
            ‖(((((1 - t) *
              (Real.cot (Real.pi * t) - 1 / (Real.pi * t))) / 2 : ℝ) : ℂ)) *
              Complex.I‖ := norm_add_le _ _
      _ = |(1 - t) / 2| +
          |((1 - t) *
              (Real.cot (Real.pi * t) - 1 / (Real.pi * t))) / 2| := by
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, Complex.norm_I, mul_one]
      _ ≤ 1 / 2 + 1 := by
        have hone : 0 ≤ 1 - t := sub_nonneg.mpr ht1
        apply add_le_add
        · rw [abs_of_nonneg (div_nonneg hone (by norm_num))]
          linarith
        · rw [abs_div, abs_mul, abs_of_nonneg hone,
            abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          calc
            (1 - t) * |Real.cot (Real.pi * t) - 1 / (Real.pi * t)| / 2 ≤
                1 * 2 / 2 := by
              gcongr
              all_goals linarith
            _ = 1 := by norm_num
      _ ≤ 10 := by norm_num
  · have htq' : (1 : ℝ) / 4 ≤ t := le_of_not_ge htq
    rw [prawitzKernelCorrection, if_neg htpos.ne']
    calc
      ‖prawitzKernel t - Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ ≤
          ‖prawitzKernel t‖ +
            ‖Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 / t + 1 := by
        gcongr
        · exact norm_prawitzKernel_le_two_div_of_mem_Ioc htpos ht1
        · rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (mul_pos (mul_pos two_pos Real.pi_pos) htpos)]
          have hden : 1 ≤ 2 * Real.pi * t := by
            nlinarith [Real.pi_gt_three]
          exact (div_le_one (by positivity)).2 hden
      _ ≤ 10 := by
        have : 2 / t ≤ 8 := (div_le_iff₀ htpos).2 (by nlinarith)
        linarith

theorem norm_prawitzKernel_le_on_split {t : ℝ}
    (hleft : prawitzSplit ≤ t) (hright : t ≤ 1) :
    ‖prawitzKernel t‖ ≤ 2 / prawitzSplit := by
  have hsplitPos : 0 < prawitzSplit := by norm_num [prawitzSplit]
  by_cases hhalf : t ≤ (1 : ℝ) / 2
  · have htPos : 0 < t := hsplitPos.trans_le hleft
    calc
      ‖prawitzKernel t‖ ≤ 2 / t := norm_prawitzKernel_le_two_div htPos hhalf
      _ ≤ 2 / prawitzSplit := by
        exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
          hsplitPos hleft
  · have hhalf' : (1 : ℝ) / 2 ≤ t := le_of_not_ge hhalf
    calc
      ‖prawitzKernel t‖ ≤ 2 := norm_prawitzKernel_le_two_of_half_le hhalf' hright
      _ ≤ 2 / prawitzSplit := by
        exact (le_div_iff₀ hsplitPos).2 (by norm_num [prawitzSplit])

/-- The four terms on the right side of the Prawitz inequality (4.2). -/
def prawitzFunctional (mu : Measure ℝ) (T t0 : ℝ) : ℝ :=
  2 * (∫ t in (0 : ℝ)..t0,
    ‖prawitzKernel t‖ *
      ‖charFun mu (T * t) - Complex.exp (-(T * t : ℂ) ^ 2 / 2)‖) +
  2 * (∫ t in t0..(1 : ℝ),
    ‖prawitzKernel t‖ * ‖charFun mu (T * t)‖) +
  2 * (∫ t in (0 : ℝ)..t0,
    ‖prawitzKernelCorrection t‖ * Real.exp (-(T ^ 2 * t ^ 2) / 2)) +
  (1 / Real.pi) *
    ∫ t in Set.Ici t0, Real.exp (-(T ^ 2 * t ^ 2) / 2) / t

/-- Exact analytic boundary for the finite-first-moment form of Route B's
Prawitz smoothing inequality.  This proposition will be discharged by the
band-limited majorant proof; declaring it introduces no axiom. -/
def PrawitzSmoothingBound : Prop :=
  ∀ (mu : Measure ℝ) [IsProbabilityMeasure mu],
    Integrable (id : ℝ → ℝ) mu →
    ∀ (T t0 : ℝ), 0 < T → 0 < t0 → t0 < 1 →
      kolmogorovDistance mu standardNormalLaw ≤ prawitzFunctional mu T t0

end

end BerryEsseen
