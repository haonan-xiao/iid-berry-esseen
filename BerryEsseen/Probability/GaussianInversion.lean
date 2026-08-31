import BerryEsseen.CharacteristicFunction.OneStepDisk
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exact Gaussian inversion on a half-line

This module proves the Gaussian instance of the inversion identity used in
the Prawitz smoothing argument.  Keeping it separate isolates the only
improper-integral/Fubini calculation in the proof.
-/

open Filter MeasureTheory ProbabilityTheory Set intervalIntegral
open scoped ENNReal NNReal Real Topology

namespace BerryEsseen

noncomputable section

open StatLean.HypothesisTesting

/-- The elementary antiderivative identity that removes the apparent
singularity in the Gaussian sine kernel. -/
theorem sin_mul_div_eq_integral_cos {t : ℝ} (ht : t ≠ 0) (x : ℝ) :
    Real.sin (t * x) / t = ∫ s in (0 : ℝ)..x, Real.cos (t * s) := by
  have hlinear (s : ℝ) : HasDerivAt (fun y : ℝ => t * y) t s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul t
  have hderiv (s : ℝ) :
      HasDerivAt (fun y : ℝ => Real.sin (t * y) / t) (Real.cos (t * s)) s := by
    have hsin := (Real.hasDerivAt_sin (t * s)).comp s (hlinear s)
    convert hsin.div_const t using 1
    field_simp [ht]
  symm
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s) (Real.continuous_cos.comp (by fun_prop) |>.intervalIntegrable 0 x)

/-- The Gaussian sine kernel is absolutely integrable on the positive
half-line; cancellation at zero follows from `|sin u| ≤ |u|`. -/
theorem integrableOn_exp_neg_sq_mul_sin_div (x : ℝ) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-t ^ 2 / 2) * Real.sin (t * x) / t)
      (Set.Ioi 0) := by
  have hgauss : IntegrableOn (fun t : ℝ => |x| * Real.exp (-(1 / 2 : ℝ) * t ^ 2))
      (Set.Ioi 0) :=
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul |x|).integrableOn
  refine hgauss.mono' ?_ ?_
  · exact (((by fun_prop : Measurable fun t : ℝ =>
        Real.exp (-t ^ 2 / 2) * Real.sin (t * x)).aemeasurable.div
          measurable_id.aemeasurable).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hsin := Real.abs_sin_le_abs (x := t * x)
  have ht0 : 0 < |t| := abs_pos.mpr ht.ne'
  calc
    Real.exp (-t ^ 2 / 2) * |Real.sin (t * x)| / |t|
        ≤ Real.exp (-t ^ 2 / 2) * |t * x| / |t| := by gcongr
    _ = |x| * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
      rw [abs_mul]
      field_simp [ht0.ne']

/-- The cosine transform of the standard-normal density. -/
theorem integral_gaussianPDFReal_mul_cos (s : ℝ) :
    (∫ t : ℝ, gaussianPDFReal 0 1 t * Real.cos (s * t)) =
      Real.exp (-s ^ 2 / 2) := by
  have h := charFun_re_eq_integral_cos standardNormalLaw s
  rw [standardNormalLaw, integral_gaussianReal_eq_integral_smul
    (E := ℝ) (f := fun t : ℝ => Real.cos (s * t)) one_ne_zero] at h
  simp only [charFun_gaussianReal, smul_eq_mul] at h
  norm_num at h
  have hcast : -((s : ℂ) ^ 2 / 2) = ((-s ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.exp_ofReal_re] at h
  exact h.symm

/-- Evenness halves the normalized Gaussian cosine transform on `Ioi 0`. -/
theorem integral_Ioi_gaussianPDFReal_mul_cos (s : ℝ) :
    (∫ t : ℝ in Set.Ioi 0, gaussianPDFReal 0 1 t * Real.cos (s * t)) =
      Real.exp (-s ^ 2 / 2) / 2 := by
  let f : ℝ → ℝ := fun t => gaussianPDFReal 0 1 t * Real.cos (s * t)
  have heven (t : ℝ) : f |t| = f t := by
    rcases le_total 0 t with ht | ht
    · simp [f, abs_of_nonneg ht]
    · simp [f, abs_of_nonpos ht, gaussianPDFReal, Real.cos_neg]
  have habs : (fun t : ℝ => f |t|) = f := funext heven
  have h := integral_comp_abs (f := f)
  rw [habs] at h
  have hfull : (∫ t : ℝ, f t) = Real.exp (-s ^ 2 / 2) := by
    simpa [f] using integral_gaussianPDFReal_mul_cos s
  rw [hfull] at h
  linarith

/-- On an ordered interval, a standard-normal CDF increment is the integral
of its density. -/
theorem standardNormalCDF_sub_eq_setIntegral {a b : ℝ} (hab : a ≤ b) :
    lawCDF standardNormalLaw b - lawCDF standardNormalLaw a =
      ∫ s : ℝ in Set.Ioc a b, gaussianPDFReal 0 1 s := by
  have hdisj : standardNormalLaw (Set.Iic b) =
      standardNormalLaw (Set.Iic a) + standardNormalLaw (Set.Ioc a b) := by
    rw [← measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic hab]
  have hnn : 0 ≤ ∫ s : ℝ in Set.Ioc a b, gaussianPDFReal 0 1 s :=
    integral_nonneg fun s => gaussianPDFReal_nonneg 0 1 s
  unfold lawCDF
  calc
    (standardNormalLaw (Set.Iic b)).toReal -
          (standardNormalLaw (Set.Iic a)).toReal =
        (standardNormalLaw (Set.Ioc a b)).toReal := by
      rw [hdisj, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      ring
    _ = ∫ s : ℝ in Set.Ioc a b, gaussianPDFReal 0 1 s := by
      unfold standardNormalLaw
      rw [gaussianReal_apply_eq_integral 0 one_ne_zero (Set.Ioc a b),
        ENNReal.toReal_ofReal hnn]

/-- The signed interval integral of the standard-normal density equals the
corresponding CDF increment, with no ordering assumption on the endpoints. -/
theorem integral_gaussianPDFReal_eq_standardNormalCDF_sub (a b : ℝ) :
    (∫ s : ℝ in a..b, gaussianPDFReal 0 1 s) =
      lawCDF standardNormalLaw b - lawCDF standardNormalLaw a := by
  rcases le_total a b with hab | hba
  · rw [intervalIntegral.integral_of_le hab]
    exact (standardNormalCDF_sub_eq_setIntegral hab).symm
  · rw [intervalIntegral.integral_of_ge hba,
      ← standardNormalCDF_sub_eq_setIntegral hba]
    ring

/-- The two-variable normalized Gaussian cosine kernel is integrable on a
bounded signed interval times the positive half-line. -/
theorem integrable_gaussianPDFReal_mul_cos_prod (x : ℝ) :
    Integrable
      (Function.uncurry fun s t : ℝ =>
        gaussianPDFReal 0 1 t * Real.cos (t * s))
      ((volume.restrict (Set.uIoc 0 x)).prod
        (volume.restrict (Set.Ioi 0))) := by
  have hs : Integrable (fun _s : ℝ => (1 : ℝ))
      (volume.restrict (Set.uIoc 0 x)) := by
    exact intervalIntegrable_iff.mp (continuous_const.intervalIntegrable 0 x)
  have ht : Integrable (gaussianPDFReal 0 1)
      (volume.restrict (Set.Ioi 0)) :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  refine (hs.mul_prod ht).mono' (by fun_prop) ?_
  filter_upwards with p
  change |gaussianPDFReal 0 1 p.2 * Real.cos (p.2 * p.1)| ≤
    1 * gaussianPDFReal 0 1 p.2
  rw [abs_mul,
    abs_of_nonneg (gaussianPDFReal_nonneg 0 1 p.2), one_mul]
  exact mul_le_of_le_one_right (gaussianPDFReal_nonneg 0 1 p.2) (Real.abs_cos_le_one _)

/-- Normalized Gaussian sine inversion.  This is the Fubini core of the
standard-normal CDF inversion formula. -/
theorem integral_Ioi_gaussianPDFReal_mul_sin_div (x : ℝ) :
    (∫ t : ℝ in Set.Ioi 0,
        gaussianPDFReal 0 1 t * Real.sin (t * x) / t) =
      Real.sqrt (2 * Real.pi) / 2 *
        (lawCDF standardNormalLaw x - 1 / 2) := by
  have hswap := intervalIntegral_integral_swap
    (f := fun s t : ℝ => gaussianPDFReal 0 1 t * Real.cos (t * s))
    (integrable_gaussianPDFReal_mul_cos_prod x)
  calc
    (∫ t : ℝ in Set.Ioi 0,
        gaussianPDFReal 0 1 t * Real.sin (t * x) / t) =
        ∫ t : ℝ in Set.Ioi 0,
          ∫ s : ℝ in (0 : ℝ)..x,
            gaussianPDFReal 0 1 t * Real.cos (t * s) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [intervalIntegral.integral_const_mul,
        ← sin_mul_div_eq_integral_cos ht.ne' x]
      ring
    _ = ∫ s : ℝ in (0 : ℝ)..x,
          ∫ t : ℝ in Set.Ioi 0,
            gaussianPDFReal 0 1 t * Real.cos (t * s) := by
      simpa only using hswap.symm
    _ = ∫ s : ℝ in (0 : ℝ)..x,
          Real.exp (-s ^ 2 / 2) / 2 := by
      apply intervalIntegral.integral_congr
      intro s hs
      simpa only [mul_comm] using integral_Ioi_gaussianPDFReal_mul_cos s
    _ = ∫ s : ℝ in (0 : ℝ)..x,
          Real.sqrt (2 * Real.pi) / 2 * gaussianPDFReal 0 1 s := by
      apply intervalIntegral.integral_congr
      intro s hs
      unfold gaussianPDFReal
      norm_num
      have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
      field_simp [hsqrt]
    _ = Real.sqrt (2 * Real.pi) / 2 *
          (∫ s : ℝ in (0 : ℝ)..x, gaussianPDFReal 0 1 s) := by
      rw [intervalIntegral.integral_const_mul]
    _ = Real.sqrt (2 * Real.pi) / 2 *
          (lawCDF standardNormalLaw x - 1 / 2) := by
      rw [integral_gaussianPDFReal_eq_standardNormalCDF_sub,
        standardNormalCDF_zero]

/-- Unnormalized Gaussian sine inversion. -/
theorem integral_Ioi_exp_neg_sq_mul_sin_div (x : ℝ) :
    (∫ t : ℝ in Set.Ioi 0,
        Real.exp (-t ^ 2 / 2) * Real.sin (t * x) / t) =
      Real.pi * (lawCDF standardNormalLaw x - 1 / 2) := by
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  calc
    (∫ t : ℝ in Set.Ioi 0,
        Real.exp (-t ^ 2 / 2) * Real.sin (t * x) / t) =
        ∫ t : ℝ in Set.Ioi 0,
          Real.sqrt (2 * Real.pi) *
            (gaussianPDFReal 0 1 t * Real.sin (t * x) / t) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      unfold gaussianPDFReal
      norm_num
      field_simp [hsqrt]
    _ = Real.sqrt (2 * Real.pi) *
          (∫ t : ℝ in Set.Ioi 0,
            gaussianPDFReal 0 1 t * Real.sin (t * x) / t) := by
      rw [MeasureTheory.integral_const_mul]
    _ = Real.sqrt (2 * Real.pi) *
          (Real.sqrt (2 * Real.pi) / 2 *
            (lawCDF standardNormalLaw x - 1 / 2)) := by
      rw [integral_Ioi_gaussianPDFReal_mul_sin_div]
    _ = Real.pi * (lawCDF standardNormalLaw x - 1 / 2) := by
      have hsquare : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
        Real.sq_sqrt (by positivity)
      calc
        Real.sqrt (2 * Real.pi) *
              (Real.sqrt (2 * Real.pi) / 2 *
                (lawCDF standardNormalLaw x - 1 / 2)) =
            Real.sqrt (2 * Real.pi) ^ 2 / 2 *
              (lawCDF standardNormalLaw x - 1 / 2) := by ring
        _ = Real.pi * (lawCDF standardNormalLaw x - 1 / 2) := by
          rw [hsquare]
          ring

/-- Scale-invariant form of Gaussian sine inversion.  The positivity of `T`
is exactly what preserves the positive half-line under `u = T t`. -/
theorem integral_Ioi_exp_neg_scaled_sq_mul_sin_div
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    (∫ t : ℝ in Set.Ioi 0,
        Real.exp (-(T * t) ^ 2 / 2) * Real.sin (T * t * x) / t) =
      Real.pi * (lawCDF standardNormalLaw x - 1 / 2) := by
  let g : ℝ → ℝ := fun u =>
    Real.exp (-u ^ 2 / 2) * Real.sin (u * x) / u
  have hchange := integral_comp_mul_left_Ioi g 0 hT
  calc
    (∫ t : ℝ in Set.Ioi 0,
        Real.exp (-(T * t) ^ 2 / 2) * Real.sin (T * t * x) / t) =
        ∫ t : ℝ in Set.Ioi 0, T * g (T * t) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      change 0 < t at ht
      dsimp [g]
      field_simp [hT.ne', ht.ne']
    _ = T * (∫ t : ℝ in Set.Ioi 0, g (T * t)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = T * (T⁻¹ * ∫ u : ℝ in Set.Ioi 0, g u) := by
      simpa only [mul_zero] using congr_arg (fun z : ℝ => T * z) hchange
    _ = ∫ u : ℝ in Set.Ioi 0, g u := by
      field_simp [hT.ne']
    _ = Real.pi * (lawCDF standardNormalLaw x - 1 / 2) := by
      simpa [g] using integral_Ioi_exp_neg_sq_mul_sin_div x

end

end BerryEsseen
