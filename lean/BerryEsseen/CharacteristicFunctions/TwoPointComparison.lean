import BerryEsseen.CharacteristicFunctions.MomentDisk
import BerryEsseen.Moments.ThirdMomentRatio
import Mathlib.Analysis.Calculus.Taylor

/-!
# Characteristic Functions / Two Point Comparison
-/

namespace BerryEsseen

open Finset Set MeasureTheory

noncomputable section

lemma taylorWithinEval_cos_one_eq
    {a b : ℝ} (hab : a < b) :
    taylorWithinEval Real.cos 1 (Icc a b) a b =
      Real.cos a - Real.sin a * (b - a) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  rw [taylor_within_apply]
  simp_rw [Real.iteratedDerivWithin_cos_Icc _ hab ha]
  norm_num [Finset.sum_range_succ, Real.iteratedDeriv_add_one_cos,
    Real.iteratedDeriv_add_one_sin]
  ring

lemma taylorWithinEval_sin_one_eq
    {a b : ℝ} (hab : a < b) :
    taylorWithinEval Real.sin 1 (Icc a b) a b =
      Real.sin a + Real.cos a * (b - a) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  rw [taylor_within_apply]
  simp_rw [Real.iteratedDerivWithin_sin_Icc _ hab ha]
  norm_num [Finset.sum_range_succ, Real.iteratedDeriv_add_one_cos,
    Real.iteratedDeriv_add_one_sin]
  ring

lemma cos_taylor_remainder_of_lt
    {a b : ℝ} (hab : a < b) :
    |Real.cos b - Real.cos a + Real.sin a * (b - a)| ≤
      (b - a) ^ 2 / 2 := by
  obtain ⟨y, _hy, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.cos) (n := 1) hab Real.contDiff_cos.contDiffOn
  rw [taylorWithinEval_cos_one_eq hab] at hrem
  have hderiv := Real.abs_iteratedDeriv_cos_le_one 2 y
  have hsq : 0 ≤ (b - a) ^ 2 := sq_nonneg (b - a)
  rw [show Real.cos b - Real.cos a + Real.sin a * (b - a) =
      Real.cos b - (Real.cos a - Real.sin a * (b - a)) by ring,
    hrem]
  norm_num only [Nat.reduceAdd, Nat.factorial, abs_div, abs_mul, abs_pow]
  rw [sq_abs]
  have hmul : |iteratedDeriv 2 Real.cos y| * (b - a) ^ 2 ≤
      (b - a) ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hderiv hsq
  exact div_le_div_of_nonneg_right hmul (by norm_num)

lemma sin_taylor_remainder_of_lt
    {a b : ℝ} (hab : a < b) :
    |Real.sin b - Real.sin a - Real.cos a * (b - a)| ≤
      (b - a) ^ 2 / 2 := by
  obtain ⟨y, _hy, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.sin) (n := 1) hab Real.contDiff_sin.contDiffOn
  rw [taylorWithinEval_sin_one_eq hab] at hrem
  have hderiv := Real.abs_iteratedDeriv_sin_le_one 2 y
  have hsq : 0 ≤ (b - a) ^ 2 := sq_nonneg (b - a)
  rw [show Real.sin b - Real.sin a - Real.cos a * (b - a) =
      Real.sin b - (Real.sin a + Real.cos a * (b - a)) by ring,
    hrem]
  norm_num only [Nat.reduceAdd, Nat.factorial, abs_div, abs_mul, abs_pow]
  rw [sq_abs]
  have hmul : |iteratedDeriv 2 Real.sin y| * (b - a) ^ 2 ≤
      (b - a) ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hderiv hsq
  exact div_le_div_of_nonneg_right hmul (by norm_num)

/-- Global two-sided second-order Taylor bound for cosine. -/
theorem abs_cos_sub_linearization_le
    (a b : ℝ) :
    |Real.cos b - Real.cos a + Real.sin a * (b - a)| ≤
      (b - a) ^ 2 / 2 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact cos_taylor_remainder_of_lt hab
  · subst b
    norm_num
  · have hneg : -a < -b := neg_lt_neg hab
    have h := cos_taylor_remainder_of_lt hneg
    rw [Real.cos_neg, Real.cos_neg, Real.sin_neg] at h
    convert h using 1 <;> ring

/-- Global two-sided second-order Taylor bound for sine. -/
theorem abs_sin_sub_linearization_le
    (a b : ℝ) :
    |Real.sin b - Real.sin a - Real.cos a * (b - a)| ≤
      (b - a) ^ 2 / 2 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact sin_taylor_remainder_of_lt hab
  · subst b
    norm_num
  · have hneg : -a < -b := neg_lt_neg hab
    have h := sin_taylor_remainder_of_lt hneg
    rw [Real.sin_neg, Real.sin_neg, Real.cos_neg] at h
    have hins :
        -Real.sin b - -Real.sin a - Real.cos a * (-b - -a) =
          -(Real.sin b - Real.sin a - Real.cos a * (b - a)) := by
      ring
    rw [hins, abs_neg] at h
    convert h using 1 <;> ring

/-- The variance-one identity behind both new radial bounds. -/
theorem integral_abs_sub_one_sq
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    (∫ x : ℝ, (|x| - 1) ^ 2 ∂mu) =
      2 * (1 - ∫ x : ℝ, |x| ∂mu) := by
  have hsq : Integrable (fun x : ℝ => x ^ 2) mu :=
    (hX.mono_exponent (by norm_num)).integrable_sq
  have habs : Integrable (fun x : ℝ => |x|) mu := by
    simpa only [id_eq, Real.norm_eq_abs] using
      hX.norm.integrable (by norm_num)
  have htwoAbs : Integrable (fun x : ℝ => 2 * |x|) mu :=
    habs.const_mul 2
  have hconst : Integrable (fun _x : ℝ => (1 : ℝ)) mu :=
    integrable_const 1
  have hexpand : (fun x : ℝ => (|x| - 1) ^ 2) =
      fun x : ℝ => x ^ 2 - 2 * |x| + 1 := by
    funext x
    calc
      (|x| - 1) ^ 2 = |x| ^ 2 - 2 * |x| + 1 := by ring
      _ = x ^ 2 - 2 * |x| + 1 := by rw [sq_abs]
  rw [hexpand]
  have hadd := integral_add (hsq.sub htwoAbs) hconst
  have hsub := integral_sub hsq htwoAbs
  calc
    (∫ x : ℝ, x ^ 2 - 2 * |x| + 1 ∂mu) =
        (∫ x : ℝ, x ^ 2 - 2 * |x| ∂mu) + ∫ _x : ℝ, 1 ∂mu := by
      simpa only [Pi.add_apply] using hadd
    _ = ((∫ x : ℝ, x ^ 2 ∂mu) - ∫ x : ℝ, 2 * |x| ∂mu) +
        ∫ _x : ℝ, 1 ∂mu := by rw [hsub]
    _ = 2 * (1 - ∫ x : ℝ, |x| ∂mu) := by
      rw [integral_const_mul, integral_const, probReal_univ, hsecond]
      simp only [one_smul]
      ring

def radialCosRemainder (u x : ℝ) : ℝ :=
  Real.cos (u * |x|) - Real.cos u +
    Real.sin u * (u * |x| - u)

def sign (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 else -1

lemma sign_measurable : Measurable sign := by
  unfold sign
  exact Measurable.piecewise measurableSet_Ici measurable_const measurable_const

lemma sign_mul_abs (x : ℝ) : sign x * |x| = x := by
  by_cases hx : 0 ≤ x
  · rw [sign, if_pos hx, one_mul, abs_of_nonneg hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [sign, if_neg hx, neg_one_mul, abs_of_nonpos hx', neg_neg]

lemma sign_abs (x : ℝ) : |sign x| = 1 := by
  by_cases hx : 0 ≤ x <;> simp [sign, hx]

lemma sign_sq (x : ℝ) : sign x ^ 2 = 1 := by
  rw [← sq_abs, sign_abs]
  norm_num

def radialSinRemainder (u x : ℝ) : ℝ :=
  sign x *
    (Real.sin (u * |x|) - Real.sin u -
      Real.cos u * (u * |x| - u))

lemma radialSinRemainder_pointwise (u x : ℝ) :
    |radialSinRemainder u x| ≤
      u ^ 2 * (|x| - 1) ^ 2 / 2 := by
  have h := abs_sin_sub_linearization_le u (u * |x|)
  unfold radialSinRemainder
  rw [abs_mul, sign_abs, one_mul]
  convert h using 1 <;> ring

theorem sign_memLp_two
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    MemLp sign 2 mu := by
  exact memLp_of_bounded (a := (-1 : ℝ)) (b := (1 : ℝ))
    (ae_of_all mu fun x => by
      constructor <;> unfold sign <;> split_ifs <;> norm_num)
    sign_measurable.aestronglyMeasurable 2

theorem integral_radialSinRemainder_abs_le
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (u : ℝ) :
    |∫ x : ℝ, radialSinRemainder u x ∂mu| ≤
      u ^ 2 * (1 - ∫ x : ℝ, |x| ∂mu) := by
  have hsq : Integrable (fun x : ℝ => x ^ 2) mu :=
    (hX.mono_exponent (by norm_num)).integrable_sq
  have habs : Integrable (fun x : ℝ => |x|) mu := by
    simpa only [id_eq, Real.norm_eq_abs] using
      hX.norm.integrable (by norm_num)
  have hconst : Integrable (fun _x : ℝ => (1 : ℝ)) mu :=
    integrable_const 1
  have htwoAbs : Integrable (fun x : ℝ => 2 * |x|) mu :=
    habs.const_mul 2
  have hdefectSq : Integrable (fun x : ℝ => (|x| - 1) ^ 2) mu := by
    have hpoly := (hsq.sub htwoAbs).add hconst
    apply hpoly.congr
    exact ae_of_all mu fun x => by
      calc
        x ^ 2 - 2 * |x| + 1 = |x| ^ 2 - 2 * |x| + 1 := by rw [sq_abs]
        _ = (|x| - 1) ^ 2 := by ring
  have hbound : Integrable
      (fun x : ℝ => u ^ 2 * (|x| - 1) ^ 2 / 2) mu := by
    have hscaled := hdefectSq.const_mul (u ^ 2 / 2)
    apply hscaled.congr
    exact ae_of_all mu fun x => by ring
  have hrem : Integrable (radialSinRemainder u) mu := by
    refine hbound.mono' ?_ ?_
    · have hinner : Measurable (fun x : ℝ =>
          Real.sin (u * |x|) - Real.sin u -
            Real.cos u * (u * |x| - u)) := by
        fun_prop
      exact (sign_measurable.mul hinner).aestronglyMeasurable
    · exact ae_of_all mu fun x => by
        simpa only [Real.norm_eq_abs] using
          radialSinRemainder_pointwise u x
  have hnorm :
      |∫ x : ℝ, radialSinRemainder u x ∂mu| ≤
        ∫ x : ℝ, |radialSinRemainder u x| ∂mu := by
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm
        (radialSinRemainder u)
  have hmono :
      (∫ x : ℝ, |radialSinRemainder u x| ∂mu) ≤
        ∫ x : ℝ, u ^ 2 * (|x| - 1) ^ 2 / 2 ∂mu := by
    exact integral_mono_ae hrem.norm hbound
      (ae_of_all mu fun x => radialSinRemainder_pointwise u x)
  calc
    |∫ x : ℝ, radialSinRemainder u x ∂mu| ≤
        ∫ x : ℝ, |radialSinRemainder u x| ∂mu := hnorm
    _ ≤ ∫ x : ℝ, u ^ 2 * (|x| - 1) ^ 2 / 2 ∂mu := hmono
    _ = u ^ 2 * (1 - ∫ x : ℝ, |x| ∂mu) := by
      have hmoment := integral_abs_sub_one_sq mu hX hsecond
      rw [show (∫ x : ℝ, u ^ 2 * (|x| - 1) ^ 2 / 2 ∂mu) =
          (u ^ 2 / 2) * ∫ x : ℝ, (|x| - 1) ^ 2 ∂mu by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all mu fun x => by ring,
        hmoment]
      ring

theorem abs_integral_sign_le_sqrt_defect
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    |∫ x : ℝ, sign x ∂mu| ≤
      Real.sqrt (2 * (1 - ∫ x : ℝ, |x| ∂mu)) := by
  have hX2 : MemLp (id : ℝ → ℝ) 2 mu :=
    hX.mono_exponent (by norm_num)
  have habs2 : MemLp (fun x : ℝ => |x|) 2 mu := by
    simpa only [id_eq, Real.norm_eq_abs] using hX2.norm
  have hone2 : MemLp (fun _x : ℝ => (1 : ℝ)) 2 mu :=
    memLp_const 1
  have hdefect2 : MemLp (fun x : ℝ => 1 - |x|) 2 mu :=
    hone2.sub habs2
  have hcs :=
    AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq
      mu (sign_memLp_two mu) hdefect2
  have hsignInt : Integrable sign mu :=
    (sign_memLp_two mu).integrable (by norm_num)
  have hsignAbsInt : Integrable (fun x : ℝ => sign x * |x|) mu := by
    apply (hX.integrable (by norm_num)).congr
    exact ae_of_all mu fun x => by
      simpa only [id_eq] using (sign_mul_abs x).symm
  have hsignDefectInt :
      (∫ x : ℝ, sign x * (1 - |x|) ∂mu) =
        ∫ x : ℝ, sign x ∂mu := by
    calc
      (∫ x : ℝ, sign x * (1 - |x|) ∂mu) =
          ∫ x : ℝ, sign x - sign x * |x| ∂mu := by
        apply integral_congr_ae
        exact ae_of_all mu fun x => by ring
      _ = (∫ x : ℝ, sign x ∂mu) -
          ∫ x : ℝ, sign x * |x| ∂mu :=
        integral_sub hsignInt hsignAbsInt
      _ = ∫ x : ℝ, sign x ∂mu := by
        have hsignAbsMean :
            (∫ x : ℝ, sign x * |x| ∂mu) = 0 := by
          calc
            (∫ x : ℝ, sign x * |x| ∂mu) =
                ∫ x : ℝ, x ∂mu := by
              apply integral_congr_ae
              exact ae_of_all mu fun x => sign_mul_abs x
            _ = 0 := hmean
        rw [hsignAbsMean]
        ring
  have hsignSq :
      (∫ x : ℝ, sign x ^ 2 ∂mu) = 1 := by
    calc
      (∫ x : ℝ, sign x ^ 2 ∂mu) =
          ∫ _x : ℝ, 1 ∂mu := by
        apply integral_congr_ae
        exact ae_of_all mu fun x => sign_sq x
      _ = 1 := by
        rw [integral_const, probReal_univ]
        simp only [one_smul]
  have hdefectSq :
      (∫ x : ℝ, (1 - |x|) ^ 2 ∂mu) =
        2 * (1 - ∫ x : ℝ, |x| ∂mu) := by
    calc
      (∫ x : ℝ, (1 - |x|) ^ 2 ∂mu) =
          ∫ x : ℝ, (|x| - 1) ^ 2 ∂mu := by
        apply integral_congr_ae
        exact ae_of_all mu fun x => by ring
      _ = 2 * (1 - ∫ x : ℝ, |x| ∂mu) :=
        integral_abs_sub_one_sq mu hX hsecond
  rw [hsignDefectInt, hsignSq, hdefectSq, Real.sqrt_one, one_mul] at hcs
  exact hcs

lemma sign_mul_sin_abs (u x : ℝ) :
    sign x * Real.sin (u * |x|) = Real.sin (u * x) := by
  by_cases hx : 0 ≤ x
  · rw [sign, if_pos hx, one_mul, abs_of_nonneg hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [sign, if_neg hx, abs_of_nonpos hx']
    rw [show u * -x = -(u * x) by ring, Real.sin_neg, neg_one_mul, neg_neg]

lemma radialSinRemainder_identity (u x : ℝ) :
    radialSinRemainder u x =
      (Real.sin (u * x) - (u * Real.cos u) * x) -
        (Real.sin u - u * Real.cos u) * sign x := by
  have hlinear :
      sign x * (u * |x| - u) =
        u * x - u * sign x := by
    calc
      sign x * (u * |x| - u) =
          u * (sign x * |x|) - u * sign x := by ring
      _ = u * x - u * sign x := by rw [sign_mul_abs]
  unfold radialSinRemainder
  calc
    sign x *
        (Real.sin (u * |x|) - Real.sin u -
          Real.cos u * (u * |x| - u)) =
        sign x * Real.sin (u * |x|) -
          sign x * Real.sin u -
          Real.cos u * (sign x * (u * |x| - u)) := by ring
    _ = Real.sin (u * x) - sign x * Real.sin u -
          Real.cos u * (u * x - u * sign x) := by
      rw [sign_mul_sin_abs, hlinear]
    _ = (Real.sin (u * x) - (u * Real.cos u) * x) -
        (Real.sin u - u * Real.cos u) * sign x := by ring

theorem integral_radialSinRemainder_eq
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (u : ℝ) :
    (∫ x : ℝ, radialSinRemainder u x ∂mu) =
      (charFun mu u).im -
        (Real.sin u - u * Real.cos u) *
          ∫ x : ℝ, sign x ∂mu := by
  have hxInt : Integrable (fun x : ℝ => x) mu := by
    simpa only [id_eq] using hX.integrable (by norm_num)
  have hsinInt : Integrable (fun x : ℝ => Real.sin (u * x)) mu := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    exact ae_of_all mu fun x => by
      simpa only [Real.norm_eq_abs, norm_one] using
        Real.abs_sin_le_one (u * x)
  have hsignInt : Integrable sign mu :=
    (sign_memLp_two mu).integrable (by norm_num)
  have hxScaled : Integrable (fun x : ℝ => (u * Real.cos u) * x) mu :=
    hxInt.const_mul (u * Real.cos u)
  have hsignScaled : Integrable
      (fun x : ℝ => (Real.sin u - u * Real.cos u) * sign x) mu :=
    hsignInt.const_mul (Real.sin u - u * Real.cos u)
  calc
    (∫ x : ℝ, radialSinRemainder u x ∂mu) =
        ∫ x : ℝ,
          (Real.sin (u * x) - (u * Real.cos u) * x) -
            (Real.sin u - u * Real.cos u) * sign x ∂mu := by
      apply integral_congr_ae
      exact ae_of_all mu fun x => radialSinRemainder_identity u x
    _ = (∫ x : ℝ, Real.sin (u * x) -
          (u * Real.cos u) * x ∂mu) -
          ∫ x : ℝ, (Real.sin u - u * Real.cos u) * sign x ∂mu :=
      integral_sub (hsinInt.sub hxScaled) hsignScaled
    _ = ((∫ x : ℝ, Real.sin (u * x) ∂mu) -
          ∫ x : ℝ, (u * Real.cos u) * x ∂mu) -
          ∫ x : ℝ, (Real.sin u - u * Real.cos u) * sign x ∂mu := by
      rw [integral_sub hsinInt hxScaled]
    _ = (charFun mu u).im -
        (Real.sin u - u * Real.cos u) *
          ∫ x : ℝ, sign x ∂mu := by
      rw [← charFun_im_eq_integral_sin mu u,
        integral_const_mul, integral_const_mul, hmean]
      ring

lemma radialCosRemainder_pointwise (u x : ℝ) :
    |radialCosRemainder u x| ≤
      u ^ 2 * (|x| - 1) ^ 2 / 2 := by
  have h := abs_cos_sub_linearization_le u (u * |x|)
  unfold radialCosRemainder
  convert h using 1 <;> ring

theorem integral_radialCosRemainder_abs_le
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (u : ℝ) :
    |∫ x : ℝ, radialCosRemainder u x ∂mu| ≤
      u ^ 2 * (1 - ∫ x : ℝ, |x| ∂mu) := by
  have hsq : Integrable (fun x : ℝ => x ^ 2) mu :=
    (hX.mono_exponent (by norm_num)).integrable_sq
  have habs : Integrable (fun x : ℝ => |x|) mu := by
    simpa only [id_eq, Real.norm_eq_abs] using
      hX.norm.integrable (by norm_num)
  have hconst : Integrable (fun _x : ℝ => (1 : ℝ)) mu :=
    integrable_const 1
  have htwoAbs : Integrable (fun x : ℝ => 2 * |x|) mu :=
    habs.const_mul 2
  have hdefectSq : Integrable (fun x : ℝ => (|x| - 1) ^ 2) mu := by
    have hpoly := (hsq.sub htwoAbs).add hconst
    apply hpoly.congr
    exact ae_of_all mu fun x => by
      calc
        x ^ 2 - 2 * |x| + 1 = |x| ^ 2 - 2 * |x| + 1 := by rw [sq_abs]
        _ = (|x| - 1) ^ 2 := by ring
  have hbound : Integrable
      (fun x : ℝ => u ^ 2 * (|x| - 1) ^ 2 / 2) mu := by
    have hscaled := hdefectSq.const_mul (u ^ 2 / 2)
    apply hscaled.congr
    exact ae_of_all mu fun x => by ring
  have hcos : Integrable (fun x : ℝ => Real.cos (u * |x|)) mu := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    exact ae_of_all mu fun x => by
      simpa only [Real.norm_eq_abs, norm_one] using
        Real.abs_cos_le_one (u * |x|)
  have hcosConst : Integrable (fun _x : ℝ => Real.cos u) mu :=
    integrable_const (Real.cos u)
  have hlinear : Integrable
      (fun x : ℝ => Real.sin u * (u * |x| - u)) mu := by
    have hscaled := (habs.sub hconst).const_mul (u * Real.sin u)
    apply hscaled.congr
    exact ae_of_all mu fun x => by
      simp only [Pi.sub_apply]
      ring
  have hrem : Integrable (radialCosRemainder u) mu := by
    simpa only [radialCosRemainder] using
      (hcos.sub hcosConst).add hlinear
  have hnorm :
      |∫ x : ℝ, radialCosRemainder u x ∂mu| ≤
        ∫ x : ℝ, |radialCosRemainder u x| ∂mu := by
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm
        (radialCosRemainder u)
  have hmono :
      (∫ x : ℝ, |radialCosRemainder u x| ∂mu) ≤
        ∫ x : ℝ, u ^ 2 * (|x| - 1) ^ 2 / 2 ∂mu := by
    exact integral_mono_ae hrem.norm hbound
      (ae_of_all mu fun x => radialCosRemainder_pointwise u x)
  calc
    |∫ x : ℝ, radialCosRemainder u x ∂mu| ≤
        ∫ x : ℝ, |radialCosRemainder u x| ∂mu := hnorm
    _ ≤ ∫ x : ℝ, u ^ 2 * (|x| - 1) ^ 2 / 2 ∂mu := hmono
    _ = u ^ 2 * (1 - ∫ x : ℝ, |x| ∂mu) := by
      have hmoment := integral_abs_sub_one_sq mu hX hsecond
      rw [show (∫ x : ℝ, u ^ 2 * (|x| - 1) ^ 2 / 2 ∂mu) =
          (u ^ 2 / 2) * ∫ x : ℝ, (|x| - 1) ^ 2 ∂mu by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all mu fun x => by ring,
        hmoment]
      ring

lemma cos_mul_abs (u x : ℝ) :
    Real.cos (u * |x|) = Real.cos (u * x) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx']
    rw [show u * -x = -(u * x) by ring, Real.cos_neg]

theorem integral_radialCosRemainder_eq
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) (u : ℝ) :
    (∫ x : ℝ, radialCosRemainder u x ∂mu) =
      (charFun mu u).re - Real.cos u +
        (u * Real.sin u) * ((∫ x : ℝ, |x| ∂mu) - 1) := by
  have habs : Integrable (fun x : ℝ => |x|) mu := by
    simpa only [id_eq, Real.norm_eq_abs] using
      hX.norm.integrable (by norm_num)
  have hconstOne : Integrable (fun _x : ℝ => (1 : ℝ)) mu :=
    integrable_const 1
  have hcos : Integrable (fun x : ℝ => Real.cos (u * |x|)) mu := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    exact ae_of_all mu fun x => by
      simpa only [Real.norm_eq_abs, norm_one] using
        Real.abs_cos_le_one (u * |x|)
  have hcosConst : Integrable (fun _x : ℝ => Real.cos u) mu :=
    integrable_const (Real.cos u)
  have hlinear : Integrable
      (fun x : ℝ => Real.sin u * (u * |x| - u)) mu := by
    have hscaled := (habs.sub hconstOne).const_mul (u * Real.sin u)
    apply hscaled.congr
    exact ae_of_all mu fun x => by
      simp only [Pi.sub_apply]
      ring
  have hcosIntegral :
      (∫ x : ℝ, Real.cos (u * |x|) ∂mu) = (charFun mu u).re := by
    rw [charFun_re_eq_integral_cos]
    apply integral_congr_ae
    exact ae_of_all mu fun x => cos_mul_abs u x
  have hlinearIntegral :
      (∫ x : ℝ, Real.sin u * (u * |x| - u) ∂mu) =
        (u * Real.sin u) * ((∫ x : ℝ, |x| ∂mu) - 1) := by
    calc
      (∫ x : ℝ, Real.sin u * (u * |x| - u) ∂mu) =
          ∫ x : ℝ, (u * Real.sin u) * (|x| - 1) ∂mu := by
        apply integral_congr_ae
        exact ae_of_all mu fun x => by ring
      _ = (u * Real.sin u) * ∫ x : ℝ, (|x| - 1) ∂mu :=
        integral_const_mul _ _
      _ = (u * Real.sin u) * ((∫ x : ℝ, |x| ∂mu) - 1) := by
        rw [integral_sub habs hconstOne, integral_const, probReal_univ]
        simp only [one_smul]
  have hadd := integral_add (hcos.sub hcosConst) hlinear
  calc
    (∫ x : ℝ, radialCosRemainder u x ∂mu) =
        (∫ x : ℝ, Real.cos (u * |x|) - Real.cos u ∂mu) +
          ∫ x : ℝ, Real.sin u * (u * |x| - u) ∂mu := by
      simpa only [radialCosRemainder, Pi.add_apply, Pi.sub_apply] using hadd
    _ = ((∫ x : ℝ, Real.cos (u * |x|) ∂mu) -
          ∫ _x : ℝ, Real.cos u ∂mu) +
          ∫ x : ℝ, Real.sin u * (u * |x| - u) ∂mu := by
      rw [integral_sub hcos hcosConst]
    _ = (charFun mu u).re - Real.cos u +
        (u * Real.sin u) * ((∫ x : ℝ, |x| ∂mu) - 1) := by
      rw [hcosIntegral, hlinearIntegral, integral_const, probReal_univ]
      simp only [one_smul]

/-- The new real-part characteristic-function comparison, under exactly the
classical variance-one third-moment assumptions. -/
theorem charFun_real_radial_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (u : ℝ) :
    |(charFun mu u).re - Real.cos u| ≤
      (1 - ∫ x : ℝ, |x| ∂mu) *
        (|u * Real.sin u| + u ^ 2) := by
  let s := ∫ x : ℝ, |x| ∂mu
  let d := 1 - s
  let R := ∫ x : ℝ, radialCosRemainder u x ∂mu
  have hs : s ≤ 1 := by
    simpa only [s] using first_absolute_moment_le_one mu hX hsecond
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hRBound : |R| ≤ u ^ 2 * d := by
    simpa only [R, d, s] using
      integral_radialCosRemainder_abs_le mu hX hsecond u
  have hReq := integral_radialCosRemainder_eq mu hX u
  have hidentity :
      (charFun mu u).re - Real.cos u = (u * Real.sin u) * d + R := by
    dsimp only [R, d, s]
    linarith
  calc
    |(charFun mu u).re - Real.cos u| =
        |(u * Real.sin u) * d + R| := by rw [hidentity]
    _ ≤ |(u * Real.sin u) * d| + |R| := abs_add_le _ _
    _ = |u * Real.sin u| * d + |R| := by rw [abs_mul, abs_of_nonneg hd]
    _ ≤ |u * Real.sin u| * d + u ^ 2 * d :=
      add_le_add le_rfl hRBound
    _ = (1 - ∫ x : ℝ, |x| ∂mu) *
        (|u * Real.sin u| + u ^ 2) := by
      dsimp only [d, s]
      ring

/-- The new imaginary-part characteristic-function comparison, under exactly
the classical centered variance-one third-moment assumptions. -/
theorem charFun_imag_radial_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (u : ℝ) :
    |(charFun mu u).im| ≤
      Real.sqrt (2 * (1 - ∫ x : ℝ, |x| ∂mu)) *
          |Real.sin u - u * Real.cos u| +
        u ^ 2 * (1 - ∫ x : ℝ, |x| ∂mu) := by
  let s := ∫ x : ℝ, |x| ∂mu
  let d := 1 - s
  let a := Real.sin u - u * Real.cos u
  let e := ∫ x : ℝ, sign x ∂mu
  let R := ∫ x : ℝ, radialSinRemainder u x ∂mu
  have he : |e| ≤ Real.sqrt (2 * d) := by
    simpa only [e, d, s] using
      abs_integral_sign_le_sqrt_defect mu hX hmean hsecond
  have hR : |R| ≤ u ^ 2 * d := by
    simpa only [R, d, s] using
      integral_radialSinRemainder_abs_le mu hX hsecond u
  have hReq := integral_radialSinRemainder_eq mu hX hmean u
  have him : (charFun mu u).im = a * e + R := by
    dsimp only [R, a, e] at hReq ⊢
    linarith
  have hproduct :
      |a| * |e| ≤ |a| * Real.sqrt (2 * d) :=
    mul_le_mul_of_nonneg_left he (abs_nonneg a)
  calc
    |(charFun mu u).im| = |a * e + R| := by rw [him]
    _ ≤ |a * e| + |R| := abs_add_le _ _
    _ = |a| * |e| + |R| := by rw [abs_mul]
    _ ≤ |a| * Real.sqrt (2 * d) + u ^ 2 * d :=
      add_le_add hproduct hR
    _ = Real.sqrt (2 * (1 - ∫ x : ℝ, |x| ∂mu)) *
          |Real.sin u - u * Real.cos u| +
        u ^ 2 * (1 - ∫ x : ℝ, |x| ∂mu) := by
      dsimp only [a, d, s]
      ring

end

end BerryEsseen
