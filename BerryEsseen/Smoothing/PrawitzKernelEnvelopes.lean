import BerryEsseen.Smoothing.PrawitzCotangentBounds
/-!
# Explicit envelopes for the Prawitz kernel

This module derives the three analytic kernel envelopes used by the Route B exact checker.
The identities correspond to formulas (5)--(7) of the supplied numerical-lemma proof, while
the final inequalities are the real-valued specifications implemented by `k0up`, `kd2up`, and
`kh2up` in the checker.
-/

open scoped Real

namespace BerryEsseen

noncomputable section

/-- The squared-norm identity behind the checker's `k0up` expression. -/
lemma prawitzKernel_norm_sq_identity {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (2 * Real.pi * t * ‖prawitzKernel t‖) ^ 2 =
      1 + (Real.pi * t * (1 - t)) ^ 2 *
          (1 + (1 / (Real.pi * t) - Real.cot (Real.pi * t)) ^ 2) -
        2 * (Real.pi * t * (1 - t)) *
          (1 / (Real.pi * t) - Real.cot (Real.pi * t)) := by
  have htne : t ≠ 0 := ht0.ne'
  have htone : t ≠ 1 := by linarith
  rw [mul_pow, Complex.sq_norm, Complex.normSq_apply]
  simp only [prawitzKernel, if_neg htone, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, Complex.add_im,
    Complex.ofReal_im, zero_add, Complex.mul_im, mul_one]
  field_simp [Real.pi_ne_zero, htne]
  ring

/-- The squared-norm identity for the singularity-corrected kernel. -/
lemma prawitzKernelCorrection_norm_sq_identity {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ‖prawitzKernelCorrection t‖ ^ 2 =
      (1 - t) ^ 2 / 4 *
        (1 + (1 / (Real.pi * t) - Real.cot (Real.pi * t)) ^ 2) := by
  have htne : t ≠ 0 := ht0.ne'
  have htone : t ≠ 1 := by linarith
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [prawitzKernelCorrection, if_neg htne, prawitzKernel, if_neg htone,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, Complex.add_im,
    Complex.ofReal_im, zero_add, Complex.mul_im, mul_one, Complex.div_re,
    Complex.div_im, Complex.normSq_ofReal]
  field_simp [Real.pi_ne_zero, htne]
  ring

/-- Formula (6): exact norm of the singularity-corrected kernel. -/
lemma two_mul_norm_prawitzKernelCorrection {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    2 * ‖prawitzKernelCorrection t‖ =
      (1 - t) * Real.sqrt
        (1 + (1 / (Real.pi * t) - Real.cot (Real.pi * t)) ^ 2) := by
  let d := 1 / (Real.pi * t) - Real.cot (Real.pi * t)
  have hsq := prawitzKernelCorrection_norm_sq_identity ht0 ht1
  have hrad : 0 ≤ 1 + d ^ 2 := by positivity
  have heq :
      (2 * ‖prawitzKernelCorrection t‖) ^ 2 =
        ((1 - t) * Real.sqrt (1 + d ^ 2)) ^ 2 := by
    rw [mul_pow, hsq, mul_pow, Real.sq_sqrt hrad]
    dsimp only [d]
    ring
  have hlhs : 0 ≤ 2 * ‖prawitzKernelCorrection t‖ := by positivity
  have hrhs : 0 ≤ (1 - t) * Real.sqrt (1 + d ^ 2) :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  dsimp only [d] at heq ⊢
  nlinarith

lemma cot_pi_mul_eq_neg_cot_pi_one_sub (t : ℝ) :
    Real.cot (Real.pi * t) = -Real.cot (Real.pi * (1 - t)) := by
  have harg : Real.pi * t = Real.pi - Real.pi * (1 - t) := by ring
  simp only [Real.cot_eq_cos_div_sin]
  rw [harg, Real.cos_pi_sub, Real.sin_pi_sub]
  ring

/-- The squared-norm identity behind the high-frequency expression. -/
lemma prawitzKernel_norm_sq_one_sub_identity {t : ℝ} (ht1 : t < 1) :
    ‖prawitzKernel t‖ ^ 2 =
      (1 - t) ^ 2 / 4 *
        (1 + (1 / (Real.pi * (1 - t)) -
          Real.cot (Real.pi * (1 - t))) ^ 2) := by
  have htone : t ≠ 1 := by linarith
  have hsne : 1 - t ≠ 0 := by linarith
  rw [Complex.sq_norm, Complex.normSq_apply]
  rw [prawitzKernel, if_neg htone, cot_pi_mul_eq_neg_cot_pi_one_sub]
  simp only [Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, Complex.add_im,
    Complex.ofReal_im, zero_add, Complex.mul_im, mul_one]
  field_simp [Real.pi_ne_zero, hsne]
  ring

/-- Formula (7): exact norm of the Prawitz kernel in terms of `1 - t`. -/
lemma two_mul_norm_prawitzKernel_one_sub {t : ℝ} (ht1 : t < 1) :
    2 * ‖prawitzKernel t‖ =
      (1 - t) * Real.sqrt
        (1 + (1 / (Real.pi * (1 - t)) -
          Real.cot (Real.pi * (1 - t))) ^ 2) := by
  let d := 1 / (Real.pi * (1 - t)) - Real.cot (Real.pi * (1 - t))
  have hsq := prawitzKernel_norm_sq_one_sub_identity ht1
  have hrad : 0 ≤ 1 + d ^ 2 := by positivity
  have heq :
      (2 * ‖prawitzKernel t‖) ^ 2 =
        ((1 - t) * Real.sqrt (1 + d ^ 2)) ^ 2 := by
    rw [mul_pow, hsq, mul_pow, Real.sq_sqrt hrad]
    dsimp only [d]
    ring
  have hlhs : 0 ≤ 2 * ‖prawitzKernel t‖ := by positivity
  have hrhs : 0 ≤ (1 - t) * Real.sqrt (1 + d ^ 2) :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  dsimp only [d] at heq ⊢
  nlinarith

/-- The cotangent gap is nonnegative on the checker domain. -/
lemma prawitzCotGap_nonneg {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    0 ≤ 1 / (Real.pi * s) - Real.cot (Real.pi * s) := by
  apply (show 0 ≤ prawitzCotGapLower (Real.pi * s) by
    unfold prawitzCotGapLower
    positivity).trans
  exact prawitzCotGapLower_le hs0 hs1

/-- Real-valued specification of the checker's `k0up` expression. -/
def prawitzK0Envelope (t : ℝ) : ℝ :=
  let x := Real.pi * t
  let a := x * (1 - t)
  let dl := prawitzCotGapLower x
  let du := prawitzCotGapUpperAt t
  Real.sqrt (max (1 + a ^ 2 * (1 + du ^ 2) - 2 * a * dl) 0) /
    (2 * Real.pi)

/-- The `k0up` expression bounds `t * ‖K(t)‖`. -/
lemma t_mul_norm_prawitzKernel_le_K0Envelope {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t * ‖prawitzKernel t‖ ≤ prawitzK0Envelope t := by
  by_cases ht : t = 0
  · subst t
    norm_num [prawitzK0Envelope, prawitzCotGapLower, prawitzCotGapUpperAt]
    positivity
  · have htPos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    let d := 1 / (Real.pi * t) - Real.cot (Real.pi * t)
    let dl := prawitzCotGapLower (Real.pi * t)
    let du := prawitzCotGapUpperAt t
    let a := Real.pi * t * (1 - t)
    let actual := 1 + a ^ 2 * (1 + d ^ 2) - 2 * a * d
    let upper := 1 + a ^ 2 * (1 + du ^ 2) - 2 * a * dl
    have hdl : dl ≤ d := prawitzCotGapLower_le ht0 ht1
    have hdu : d ≤ du := prawitzCotGap_le_upper ht0 ht1
    have hd0 : 0 ≤ d := prawitzCotGap_nonneg ht0 ht1
    have ha0 : 0 ≤ a := by
      dsimp only [a]
      exact mul_nonneg (mul_nonneg Real.pi_pos.le ht0) (sub_nonneg.mpr ht1.le)
    have hsqdu : d ^ 2 ≤ du ^ 2 := pow_le_pow_left₀ hd0 hdu 2
    have hterm1 : 0 ≤ a ^ 2 * (du ^ 2 - d ^ 2) :=
      mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hsqdu)
    have hterm2 : 0 ≤ 2 * a * (d - dl) :=
      mul_nonneg (mul_nonneg (by norm_num) ha0) (sub_nonneg.mpr hdl)
    have hactualEq :
        (2 * Real.pi * t * ‖prawitzKernel t‖) ^ 2 = actual := by
      simpa [actual, a, d] using prawitzKernel_norm_sq_identity htPos ht1
    have hactual0 : 0 ≤ actual := by rw [← hactualEq]; positivity
    have hle : actual ≤ upper := by
      dsimp only [actual, upper]
      nlinarith
    have hupper0 : 0 ≤ upper := hactual0.trans hle
    have hsqrt := Real.sqrt_le_sqrt hle
    have hscale0 : 0 ≤ 2 * Real.pi * t * ‖prawitzKernel t‖ := by positivity
    have hsqrtActual : Real.sqrt actual = 2 * Real.pi * t * ‖prawitzKernel t‖ := by
      rw [← hactualEq, Real.sqrt_sq_eq_abs, abs_of_nonneg hscale0]
    have hscaled : 2 * Real.pi * t * ‖prawitzKernel t‖ ≤ Real.sqrt upper := by
      rw [← hsqrtActual]
      exact hsqrt
    unfold prawitzK0Envelope
    dsimp only
    rw [max_eq_left hupper0]
    apply (le_div_iff₀ (mul_pos two_pos Real.pi_pos)).2
    nlinarith

lemma sqrt_one_add_sq_le_one_add_half_sq (x : ℝ) :
    Real.sqrt (1 + x ^ 2) ≤ 1 + x ^ 2 / 2 := by
  have hrad : 0 ≤ 1 + x ^ 2 := by positivity
  have hsqrt0 := Real.sqrt_nonneg (1 + x ^ 2)
  have hrhs0 : 0 ≤ 1 + x ^ 2 / 2 := by positivity
  have hsq := Real.sq_sqrt hrad
  nlinarith [sq_nonneg (x ^ 2)]

/-- Real-valued specification of the checker's `kd2up` expression. -/
def prawitzKD2Envelope (t : ℝ) : ℝ :=
  (1 - t) * (1 + prawitzCotGapUpperAt t ^ 2 / 2)

/-- The `kd2up` expression bounds twice the corrected-kernel norm. -/
lemma two_mul_norm_prawitzKernelCorrection_le_KD2Envelope
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    2 * ‖prawitzKernelCorrection t‖ ≤ prawitzKD2Envelope t := by
  by_cases ht : t = 0
  · subst t
    norm_num [prawitzKernelCorrection_zero, prawitzKD2Envelope,
      prawitzCotGapUpperAt, prawitzCotGapLower]
  · have htPos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    let d := 1 / (Real.pi * t) - Real.cot (Real.pi * t)
    let du := prawitzCotGapUpperAt t
    have hd0 : 0 ≤ d := prawitzCotGap_nonneg ht0 ht1
    have hdu : d ≤ du := prawitzCotGap_le_upper ht0 ht1
    have hsqdu : d ^ 2 ≤ du ^ 2 := pow_le_pow_left₀ hd0 hdu 2
    have hsqrtMono : Real.sqrt (1 + d ^ 2) ≤ Real.sqrt (1 + du ^ 2) := by
      exact Real.sqrt_le_sqrt (by linarith)
    have hsqrtBound : Real.sqrt (1 + d ^ 2) ≤ 1 + du ^ 2 / 2 :=
      hsqrtMono.trans (sqrt_one_add_sq_le_one_add_half_sq du)
    rw [two_mul_norm_prawitzKernelCorrection htPos ht1]
    unfold prawitzKD2Envelope
    exact mul_le_mul_of_nonneg_left hsqrtBound (sub_nonneg.mpr ht1.le)

/-- Real-valued specification of the checker's `kh2up` expression. -/
def prawitzKH2Envelope (t : ℝ) : ℝ :=
  let s := 1 - t
  s * Real.sqrt (1 + prawitzCotGapUpperAt s ^ 2)

/-- The `kh2up` expression bounds twice the high-frequency kernel norm. -/
lemma two_mul_norm_prawitzKernel_le_KH2Envelope
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    2 * ‖prawitzKernel t‖ ≤ prawitzKH2Envelope t := by
  by_cases hone : t = 1
  · subst t
    simp [prawitzKernel_one, prawitzKH2Envelope]
  · have htLt : t < 1 := lt_of_le_of_ne ht1 hone
    let s := 1 - t
    let d := 1 / (Real.pi * s) - Real.cot (Real.pi * s)
    let du := prawitzCotGapUpperAt s
    have hs0 : 0 ≤ s := by dsimp only [s]; linarith
    have hs1 : s < 1 := by dsimp only [s]; linarith
    have hd0 : 0 ≤ d := prawitzCotGap_nonneg hs0 hs1
    have hdu : d ≤ du := prawitzCotGap_le_upper hs0 hs1
    have hsqdu : d ^ 2 ≤ du ^ 2 := pow_le_pow_left₀ hd0 hdu 2
    have hsqrt : Real.sqrt (1 + d ^ 2) ≤ Real.sqrt (1 + du ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    rw [two_mul_norm_prawitzKernel_one_sub htLt]
    unfold prawitzKH2Envelope
    exact mul_le_mul_of_nonneg_left hsqrt hs0

end

end BerryEsseen
