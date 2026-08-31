import BerryEsseen.Smoothing.PrawitzSmoothing
/-!
# The closed Prawitz smoothing inequality

This module performs the four-term subtraction between the band-limited
Prawitz majorant and Gaussian inversion.  All integral decompositions below
are made only after the corresponding absolute-integrability obligations have
been discharged in `PrawitzSmoothing`.
-/

open Filter MeasureTheory ProbabilityTheory Set intervalIntegral
open scoped ComplexConjugate ENNReal FourierTransform NNReal Real Topology

namespace BerryEsseen

noncomputable section

/-- The real Gaussian inversion integrand is absolutely integrable on the
positive half-line.  This packages the cancellation of `sin (T t x) / t` at
zero for use in the four-term decomposition. -/
theorem integrableOn_prawitzGaussianInversion
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    IntegrableOn
      (fun t : ℝ =>
        (prawitzSingularKernel t * prawitzOscillation T x t *
          prawitzGaussianFactor T t).re)
      (Set.Ioi 0) := by
  have hb : 0 < T ^ 2 / 2 := by positivity
  let C : ℝ := |T * x| / (2 * Real.pi)
  have hdom : Integrable
      (fun t : ℝ => C * Real.exp (-(T ^ 2 / 2) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul C
  refine hdom.integrableOn.mono' ?_ ?_
  · have hsing : Measurable (fun t : ℝ => prawitzSingularKernel t) := by
      unfold prawitzSingularKernel
      exact measurable_const.div (by fun_prop)
    have hosc : Measurable (fun t : ℝ => prawitzOscillation T x t) := by
      unfold prawitzOscillation
      fun_prop
    have hgauss : Measurable (fun t : ℝ => prawitzGaussianFactor T t) := by
      unfold prawitzGaussianFactor
      fun_prop
    exact (Complex.measurable_re.comp
      ((hsing.mul hosc).mul hgauss)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    rw [Real.norm_eq_abs, re_prawitzSingularKernel_mul_oscillation_mul_gaussian,
      abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (mul_pos (mul_pos two_pos Real.pi_pos) ht0)]
    have hsin := Real.abs_sin_le_abs (x := T * t * x)
    calc
      Real.exp (-(T * t) ^ 2 / 2) * |Real.sin (T * t * x)| /
          (2 * Real.pi * t) ≤
        Real.exp (-(T * t) ^ 2 / 2) * |T * t * x| /
          (2 * Real.pi * t) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsin (Real.exp_pos _).le)
          (mul_pos (mul_pos two_pos Real.pi_pos) ht0).le
      _ = C * Real.exp (-(T ^ 2 / 2) * t ^ 2) := by
        dsimp [C]
        rw [show |T * t * x| = |T * x| * t by
          rw [show T * t * x = (T * x) * t by ring, abs_mul, abs_of_pos ht0]]
        field_simp [ht0.ne', Real.pi_ne_zero]

/-- Upper one-sided CDF error obtained from the Prawitz majorant.  The proof
is the exact four-term decomposition defining `prawitzFunctional`. -/
theorem lawCDF_sub_standardNormal_le_prawitzFunctional
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hint : Integrable (id : ℝ → ℝ) mu)
    {T t0 : ℝ} (hT : 0 < T) (ht00 : 0 < t0) (ht01 : t0 < 1)
    (x : ℝ) :
    lawCDF mu x - lawCDF standardNormalLaw x ≤
      prawitzFunctional mu T t0 := by
  let E : ℝ → ℂ := fun t => prawitzOscillation T x t
  let G : ℝ → ℂ := fun t => prawitzGaussianFactor T t
  let U : ℝ → ℝ := fun t =>
    (prawitzKernel t * E t * charFun mu (T * t)).re
  let A : ℝ → ℝ := fun t =>
    (prawitzKernel t * E t * (charFun mu (T * t) - G t)).re
  let C : ℝ → ℝ := fun t =>
    ((prawitzKernel t - prawitzSingularKernel t) * E t * G t).re
  let D : ℝ → ℝ := fun t =>
    (prawitzSingularKernel t * E t * G t).re
  let a : ℝ → ℝ := fun t =>
    ‖prawitzKernel t‖ * ‖charFun mu (T * t) - G t‖
  let b : ℝ → ℝ := fun t =>
    ‖prawitzKernel t‖ * ‖charFun mu (T * t)‖
  let c : ℝ → ℝ := fun t =>
    ‖prawitzKernelCorrection t‖ * Real.exp (-(T ^ 2 * t ^ 2) / 2)
  let q : ℝ → ℝ := fun t => Real.exp (-(T ^ 2 * t ^ 2) / 2) / t
  have hLow : IntervalIntegrable a volume 0 t0 := by
    simpa only [a, G] using
      intervalIntegrable_prawitzLowDifference mu hint T ht00.le ht01.le
  have hHigh : IntervalIntegrable b volume t0 1 := by
    simpa only [b] using
      intervalIntegrable_prawitzHighModulus mu ht00 ht01.le T
  have hCorr : IntervalIntegrable c volume 0 t0 := by
    simpa only [c] using
      intervalIntegrable_prawitzCorrectionGaussian T ht00.le ht01.le
  have hTail : IntegrableOn q (Set.Ici t0) := by
    simpa only [q] using integrableOn_prawitzGaussianTail hT ht00
  have hDglobal : IntegrableOn D (Set.Ioi 0) := by
    simpa only [D, E, G] using integrableOn_prawitzGaussianInversion hT x
  have hDlowOn : IntegrableOn D (Set.Ioc 0 t0) :=
    hDglobal.mono_set Set.Ioc_subset_Ioi_self
  have hDlow : IntervalIntegrable D volume 0 t0 := by
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le ht00.le]
  have hDtailIoi : IntegrableOn D (Set.Ioi t0) :=
    hDglobal.mono_set (Set.Ioi_subset_Ioi ht00.le)
  have hDtail : IntegrableOn D (Set.Ici t0) :=
    hDglobal.mono_set (fun t ht => ht00.trans_le ht)
  have hA : IntervalIntegrable A volume 0 t0 := by
    refine hLow.mono_fun' ?_ ?_
    · have hE : Measurable E := by
        dsimp only [E]
        unfold prawitzOscillation
        fun_prop
      have hG : Measurable G := by
        dsimp only [G]
        unfold prawitzGaussianFactor
        fun_prop
      have hphi : Measurable (fun t : ℝ => charFun mu (T * t)) :=
        (measurable_charFun (μ := mu)).comp (by fun_prop)
      exact (Complex.measurable_re.comp
        ((measurable_prawitzKernel.mul hE).mul (hphi.sub hG))).aestronglyMeasurable.restrict
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards with t ht
      rw [Real.norm_eq_abs]
      calc
        |A t| ≤ ‖prawitzKernel t * E t *
            (charFun mu (T * t) - G t)‖ := Complex.abs_re_le_norm _
        _ = a t := by
          dsimp only [A, a]
          rw [norm_mul, norm_mul, norm_prawitzOscillation]
          ring
  have hB : IntervalIntegrable U volume t0 1 := by
    refine hHigh.mono_fun' ?_ ?_
    · have hE : Measurable E := by
        dsimp only [E]
        unfold prawitzOscillation
        fun_prop
      have hphi : Measurable (fun t : ℝ => charFun mu (T * t)) :=
        (measurable_charFun (μ := mu)).comp (by fun_prop)
      exact (Complex.measurable_re.comp
        ((measurable_prawitzKernel.mul hE).mul hphi)).aestronglyMeasurable.restrict
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards with t ht
      rw [Real.norm_eq_abs]
      calc
        |U t| ≤ ‖prawitzKernel t * E t * charFun mu (T * t)‖ :=
          Complex.abs_re_le_norm _
        _ = b t := by
          dsimp only [U, b]
          rw [norm_mul, norm_mul, norm_prawitzOscillation]
          ring
  have hC : IntervalIntegrable C volume 0 t0 := by
    refine hCorr.mono_fun' ?_ ?_
    · have hE : Measurable E := by
        dsimp only [E]
        unfold prawitzOscillation
        fun_prop
      have hG : Measurable G := by
        dsimp only [G]
        unfold prawitzGaussianFactor
        fun_prop
      have hS : Measurable (fun t : ℝ => prawitzSingularKernel t) := by
        unfold prawitzSingularKernel
        exact measurable_const.div (by fun_prop)
      exact (Complex.measurable_re.comp
        (((measurable_prawitzKernel.sub hS).mul hE).mul hG)).aestronglyMeasurable.restrict
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards with t ht
      rw [Real.norm_eq_abs]
      have htMem : t ∈ Set.uIoc (0 : ℝ) t0 := ht
      rw [Set.uIoc_of_le ht00.le] at htMem
      have htpos : 0 < t := htMem.1
      calc
        |C t| ≤ ‖(prawitzKernel t - prawitzSingularKernel t) * E t * G t‖ :=
          Complex.abs_re_le_norm _
        _ = c t := by
          dsimp only [C, c]
          rw [prawitzKernel_sub_singularKernel_eq_correction htpos.ne',
            norm_mul, norm_mul, norm_prawitzOscillation,
            norm_prawitzGaussianFactor]
          ring
  have hPoint (t : ℝ) : U t = A t + (C t + D t) := by
    dsimp only [U, A, C, D]
    rw [← Complex.add_re, ← Complex.add_re]
    congr 1
    ring
  have hUlow : IntervalIntegrable U volume 0 t0 := by
    exact (hA.add (hC.add hDlow)).congr fun t ht => (hPoint t).symm
  have hUint :
      (∫ t in (0 : ℝ)..1, U t) =
        (∫ t in (0 : ℝ)..t0, A t) +
          (∫ t in (0 : ℝ)..t0, C t) +
          (∫ t in (0 : ℝ)..t0, D t) +
          (∫ t in t0..(1 : ℝ), U t) := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hUlow hB
    have hlow :
        (∫ t in (0 : ℝ)..t0, U t) =
          (∫ t in (0 : ℝ)..t0, A t) +
            (∫ t in (0 : ℝ)..t0, C t) +
            (∫ t in (0 : ℝ)..t0, D t) := by
      calc
        (∫ t in (0 : ℝ)..t0, U t) =
            ∫ t in (0 : ℝ)..t0, A t + (C t + D t) := by
              apply intervalIntegral.integral_congr
              intro t ht
              exact hPoint t
        _ = (∫ t in (0 : ℝ)..t0, A t) +
            ∫ t in (0 : ℝ)..t0, C t + D t :=
              intervalIntegral.integral_add hA (hC.add hDlow)
        _ = (∫ t in (0 : ℝ)..t0, A t) +
            (∫ t in (0 : ℝ)..t0, C t) +
            (∫ t in (0 : ℝ)..t0, D t) := by
              rw [intervalIntegral.integral_add hC hDlow]
              ring
    linarith
  have hDsplit :
      (∫ t in Set.Ioi (0 : ℝ), D t) =
        (∫ t in (0 : ℝ)..t0, D t) +
          ∫ t in Set.Ici t0, D t := by
    rw [intervalIntegral.integral_of_le ht00.le,
      integral_Ici_eq_integral_Ioi]
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      hDlowOn hDtailIoi, Ioc_union_Ioi_eq_Ioi ht00.le]
  have hmu := lawCDF_le_half_add_prawitzKernelIntegral mu hint hT x
  change lawCDF mu x ≤ 1 / 2 + 2 * ∫ t in (0 : ℝ)..1, U t at hmu
  have hnormal := lawCDF_standardNormal_eq_half_add_singularIntegral hT x
  change lawCDF standardNormalLaw x =
    1 / 2 + 2 * ∫ t in Set.Ioi (0 : ℝ), D t at hnormal
  have hbase :
      lawCDF mu x - lawCDF standardNormalLaw x ≤
        2 * (∫ t in (0 : ℝ)..t0, A t) +
        2 * (∫ t in t0..(1 : ℝ), U t) +
        2 * (∫ t in (0 : ℝ)..t0, C t) -
        2 * (∫ t in Set.Ici t0, D t) := by
    rw [hnormal, hDsplit]
    rw [hUint] at hmu
    linarith
  have hAint : (∫ t in (0 : ℝ)..t0, A t) ≤
      ∫ t in (0 : ℝ)..t0, a t := by
    apply intervalIntegral.integral_mono_on ht00.le hA hLow
    intro t ht
    calc
      A t ≤ |A t| := le_abs_self _
      _ ≤ ‖prawitzKernel t * E t *
          (charFun mu (T * t) - G t)‖ := Complex.abs_re_le_norm _
      _ = a t := by
        dsimp only [A, a]
        rw [norm_mul, norm_mul, norm_prawitzOscillation]
        ring
  have hBint : (∫ t in t0..(1 : ℝ), U t) ≤
      ∫ t in t0..(1 : ℝ), b t := by
    apply intervalIntegral.integral_mono_on ht01.le hB hHigh
    intro t ht
    calc
      U t ≤ |U t| := le_abs_self _
      _ ≤ ‖prawitzKernel t * E t * charFun mu (T * t)‖ :=
        Complex.abs_re_le_norm _
      _ = b t := by
        dsimp only [U, b]
        rw [norm_mul, norm_mul, norm_prawitzOscillation]
        ring
  have hCint : (∫ t in (0 : ℝ)..t0, C t) ≤
      ∫ t in (0 : ℝ)..t0, c t := by
    apply intervalIntegral.integral_mono_on ht00.le hC hCorr
    intro t ht
    by_cases htzero : t = 0
    · subst t
      simp [C, c, E, G, prawitzKernel, prawitzSingularKernel,
        prawitzKernelCorrection, prawitzOscillation, prawitzGaussianFactor,
        Real.cot_eq_cos_div_sin]
    · calc
        C t ≤ |C t| := le_abs_self _
        _ ≤ ‖(prawitzKernel t - prawitzSingularKernel t) * E t * G t‖ :=
          Complex.abs_re_le_norm _
        _ = c t := by
          dsimp only [C, c]
          rw [prawitzKernel_sub_singularKernel_eq_correction htzero,
            norm_mul, norm_mul, norm_prawitzOscillation,
            norm_prawitzGaussianFactor]
          ring
  have hTailInt :
      -2 * (∫ t in Set.Ici t0, D t) ≤
        (1 / Real.pi) * ∫ t in Set.Ici t0, q t := by
    have hmono :
        (∫ t in Set.Ici t0, -D t) ≤
          ∫ t in Set.Ici t0, (1 / (2 * Real.pi)) * q t := by
      apply integral_mono_ae hDtail.neg (hTail.const_mul (1 / (2 * Real.pi)))
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      have htpos : 0 < t := ht00.trans_le ht
      calc
        -D t ≤ |D t| := neg_le_abs _
        _ = |Real.exp (-(T * t) ^ 2 / 2) * Real.sin (T * t * x) /
            (2 * Real.pi * t)| := by
              dsimp only [D, E, G]
              rw [re_prawitzSingularKernel_mul_oscillation_mul_gaussian]
        _ ≤ Real.exp (-(T ^ 2 * t ^ 2) / 2) /
            (2 * Real.pi * t) := by
              rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
                abs_of_pos (mul_pos (mul_pos two_pos Real.pi_pos) htpos)]
              have hsin : |Real.sin (T * t * x)| ≤ 1 := Real.abs_sin_le_one _
              have hexpEq : -(T * t) ^ 2 / 2 = -(T ^ 2 * t ^ 2) / 2 := by ring
              rw [hexpEq]
              exact div_le_div_of_nonneg_right
                (by simpa only [mul_one] using
                  mul_le_mul_of_nonneg_left hsin (Real.exp_pos _).le)
                (mul_pos (mul_pos two_pos Real.pi_pos) htpos).le
        _ = (1 / (2 * Real.pi)) * q t := by
              dsimp [q]
              field_simp [htpos.ne', Real.pi_ne_zero]
    rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul] at hmono
    calc
      -2 * (∫ t in Set.Ici t0, D t) =
          2 * (-(∫ t in Set.Ici t0, D t)) := by ring
      _ ≤ 2 * ((1 / (2 * Real.pi)) * ∫ t in Set.Ici t0, q t) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
      _ = (1 / Real.pi) * ∫ t in Set.Ici t0, q t := by
        field_simp [Real.pi_ne_zero]
  unfold prawitzFunctional
  change lawCDF mu x - lawCDF standardNormalLaw x ≤
    2 * (∫ t in (0 : ℝ)..t0, a t) +
    2 * (∫ t in t0..(1 : ℝ), b t) +
    2 * (∫ t in (0 : ℝ)..t0, c t) +
    (1 / Real.pi) * ∫ t in Set.Ici t0, q t
  have hAint2 := mul_le_mul_of_nonneg_left hAint (by norm_num : (0 : ℝ) ≤ 2)
  have hBint2 := mul_le_mul_of_nonneg_left hBint (by norm_num : (0 : ℝ) ≤ 2)
  have hCint2 := mul_le_mul_of_nonneg_left hCint (by norm_num : (0 : ℝ) ≤ 2)
  linarith

/-- Reflection negates the Fourier frequency in the characteristic function. -/
theorem charFun_map_neg
    (mu : Measure ℝ) [IsFiniteMeasure mu] (u : ℝ) :
    charFun (mu.map fun y : ℝ => -y) u = charFun mu (-u) := by
  rw [charFun_apply_real, charFun_apply_real,
    integral_map (by fun_prop) (by fun_prop)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  congr 1
  push_cast
  ring

/-- For an arbitrary law, the two closed half-lines used by a CDF and its
reflection cover the real line.  The possible atom at `x` makes this an
inequality in the direction needed for the lower CDF error. -/
theorem one_le_lawCDF_add_reflected_neg
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (x : ℝ) :
    1 ≤ lawCDF mu x + lawCDF (mu.map fun y : ℝ => -y) (-x) := by
  have hreflect :
      lawCDF (mu.map fun y : ℝ => -y) (-x) = mu.real (Set.Ici x) := by
    unfold lawCDF
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
    rw [← measureReal_def]
    congr 1
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
    constructor <;> intro hy <;> linarith
  rw [hreflect]
  rw [lawCDF, ← measureReal_def]
  have hcomp := probReal_compl_eq_one_sub (μ := mu) (s := Set.Iic x) measurableSet_Iic
  rw [Set.compl_Iic] at hcomp
  have hmono : mu.real (Set.Ioi x) ≤ mu.real (Set.Ici x) :=
    measureReal_mono Set.Ioi_subset_Ici_self
  linarith

/-- The four-term functional is invariant under reflection of the law. -/
theorem prawitzFunctional_map_neg
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (T t0 : ℝ) :
    prawitzFunctional (mu.map fun y : ℝ => -y) T t0 =
      prawitzFunctional mu T t0 := by
  have hcf (u : ℝ) :
      charFun (mu.map fun y : ℝ => -y) u = charFun mu (-u) :=
    charFun_map_neg mu u
  have hGstar (t : ℝ) :
      (starRingEnd ℂ) (prawitzGaussianFactor T t) =
        prawitzGaussianFactor T t := by
    rw [prawitzGaussianFactor_eq_ofReal]
    exact Complex.conj_ofReal _
  have hdiff (t : ℝ) :
      ‖charFun (mu.map fun y : ℝ => -y) (T * t) -
          Complex.exp (-(T * t : ℂ) ^ 2 / 2)‖ =
        ‖charFun mu (T * t) - Complex.exp (-(T * t : ℂ) ^ 2 / 2)‖ := by
    rw [hcf, charFun_neg]
    change ‖(starRingEnd ℂ) (charFun mu (T * t)) - prawitzGaussianFactor T t‖ =
      ‖charFun mu (T * t) - prawitzGaussianFactor T t‖
    have heq :
        (starRingEnd ℂ) (charFun mu (T * t) - prawitzGaussianFactor T t) =
          (starRingEnd ℂ) (charFun mu (T * t)) - prawitzGaussianFactor T t := by
      rw [map_sub, hGstar]
    rw [← heq, Complex.norm_conj]
  have hmod (t : ℝ) :
      ‖charFun (mu.map fun y : ℝ => -y) (T * t)‖ =
        ‖charFun mu (T * t)‖ := by
    rw [hcf, charFun_neg, Complex.norm_conj]
  unfold prawitzFunctional
  simp_rw [hdiff, hmod]

/-- Symmetry of the standard normal CDF, derived from the already verified
Gaussian inversion formula. -/
theorem standardNormalCDF_neg (x : ℝ) :
    lawCDF standardNormalLaw (-x) = 1 - lawCDF standardNormalLaw x := by
  have hpos := lawCDF_standardNormal_eq_half_add_singularIntegral
    (T := (1 : ℝ)) (by norm_num) x
  have hneg := lawCDF_standardNormal_eq_half_add_singularIntegral
    (T := (1 : ℝ)) (by norm_num) (-x)
  have hpoint (t : ℝ) :
      (prawitzSingularKernel t * prawitzOscillation 1 (-x) t *
          prawitzGaussianFactor 1 t).re =
        -(prawitzSingularKernel t * prawitzOscillation 1 x t *
          prawitzGaussianFactor 1 t).re := by
    rw [re_prawitzSingularKernel_mul_oscillation_mul_gaussian,
      re_prawitzSingularKernel_mul_oscillation_mul_gaussian]
    rw [show (1 : ℝ) * t * (-x) = -(1 * t * x) by ring, Real.sin_neg]
    ring
  rw [show (fun t : ℝ =>
      (prawitzSingularKernel t * prawitzOscillation 1 (-x) t *
        prawitzGaussianFactor 1 t).re) =
      (fun t : ℝ => -(prawitzSingularKernel t * prawitzOscillation 1 x t *
        prawitzGaussianFactor 1 t).re) by
      funext t
      exact hpoint t,
    MeasureTheory.integral_neg] at hneg
  linarith

theorem integrable_id_map_neg
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hint : Integrable (id : ℝ → ℝ) mu) :
    Integrable (id : ℝ → ℝ) (mu.map fun y : ℝ => -y) := by
  refine (integrable_map_measure (by fun_prop) (by fun_prop)).2 ?_
  simpa only [Function.comp_apply, id_eq] using hint.neg

/-- The lower one-sided CDF error follows by applying the upper theorem to
the reflected law.  This remains valid for laws with atoms. -/
theorem standardNormal_sub_lawCDF_le_prawitzFunctional
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hint : Integrable (id : ℝ → ℝ) mu)
    {T t0 : ℝ} (hT : 0 < T) (ht00 : 0 < t0) (ht01 : t0 < 1)
    (x : ℝ) :
    lawCDF standardNormalLaw x - lawCDF mu x ≤
      prawitzFunctional mu T t0 := by
  let nu : Measure ℝ := mu.map fun y : ℝ => -y
  letI : IsProbabilityMeasure nu :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hnuInt : Integrable (id : ℝ → ℝ) nu := by
    dsimp only [nu]
    exact integrable_id_map_neg mu hint
  have hupp := lawCDF_sub_standardNormal_le_prawitzFunctional
    nu hnuInt hT ht00 ht01 (-x)
  have hfunc : prawitzFunctional nu T t0 = prawitzFunctional mu T t0 := by
    dsimp only [nu]
    exact prawitzFunctional_map_neg mu T t0
  rw [hfunc] at hupp
  have hreflect := one_le_lawCDF_add_reflected_neg mu x
  change 1 ≤ lawCDF mu x + lawCDF nu (-x) at hreflect
  have hnormal := standardNormalCDF_neg x
  linarith

/-- The analytic boundary declared in `Prawitz` is now discharged without
axioms: both CDF directions are controlled by the same four-term functional. -/
theorem prawitzSmoothingBound : PrawitzSmoothingBound := by
  intro mu _ hint T t0 hT ht00 ht01
  apply (kolmogorovDistance_le_iff_pointwise
    mu standardNormalLaw (prawitzFunctional mu T t0)).2
  intro x
  have hupp := lawCDF_sub_standardNormal_le_prawitzFunctional
    mu hint hT ht00 ht01 x
  have hlow := standardNormal_sub_lawCDF_le_prawitzFunctional
    mu hint hT ht00 ht01 x
  exact abs_le.mpr ⟨by linarith, hupp⟩

end

end BerryEsseen
