import BerryEsseen.CharacteristicFunction.ConvexMinorant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Route B one-step complex disk

This module formalizes equations (3.6)--(3.8).  It first isolates the compact
planar maximization from the probability argument, then derives the real,
imaginary, and full-complex constraints on the normalized characteristic-
function remainder.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

namespace BerryEsseen

noncomputable section

/-- The real Taylor remainder `cos v - 1 + v²/2`. -/
def routeBCosineRemainder (v : ℝ) : ℝ :=
  Real.cos v - 1 + v ^ 2 / 2

/-- The vertical half-width in the sine-remainder constraint. -/
def routeBBeta (r : ℝ) : ℝ :=
  (1 : ℝ) / 6 * Real.sqrt (1 - (r - 1) ^ 2)

/-- The full-complex Taylor disk radius. -/
def routeBD0 : ℝ := (1 : ℝ) / 6

/-- Route B equation (3.6), including its removable value at zero. -/
def routeBEpsilon (rho c : ℝ) : ℝ :=
  if c = 0 then 0
  else rho ^ 2 / c ^ 3 *
    (Real.exp (-(c ^ 2) / (2 * rho ^ 2)) - 1 + c ^ 2 / (2 * rho ^ 2))

/-- The circle/strip transition point in the compact disk. -/
def routeBTransition (r : ℝ) : ℝ := (r - 1) / 6

/-- Squared distance from `(epsilon,0)` after maximizing vertically at a fixed
real coordinate `x`. -/
def routeBDiskScore (beta d epsilon x : ℝ) : ℝ :=
  (x - epsilon) ^ 2 + min (beta ^ 2) (d ^ 2 - x ^ 2)

/-- The finite candidate formula in Route B equation (3.7).  When the
transition point is outside `[0,kappa]`, its slot repeats the zero endpoint, so
the definition remains total without adding a spurious candidate. -/
def routeBDiskBoundSq (kappa rho r c : ℝ) : ℝ :=
  let beta := routeBBeta r
  let d := routeBD0
  let epsilon := routeBEpsilon rho c
  let transition := routeBTransition r
  max (routeBDiskScore beta d epsilon 0)
    (max (routeBDiskScore beta d epsilon kappa)
      (if 0 ≤ transition ∧ transition ≤ kappa then
        routeBDiskScore beta d epsilon transition
      else routeBDiskScore beta d epsilon 0))

/-- The nonnegative disk bound `D` from equation (3.7). -/
def routeBDiskBound (kappa rho r c : ℝ) : ℝ :=
  Real.sqrt (routeBDiskBoundSq kappa rho r c)

/-- The parameter-only part of the coarse disk-radius bound. -/
def routeBDiskStaticConstant (kappa r : ℝ) : ℝ :=
  1 + 2 * kappa ^ 2 + 2 * routeBTransition r ^ 2 + routeBBeta r ^ 2

theorem routeBDiskStaticConstant_nonneg (kappa r : ℝ) :
    0 ≤ routeBDiskStaticConstant kappa r := by
  unfold routeBDiskStaticConstant
  positivity

theorem measurable_routeBEpsilon (rho : ℝ) :
    Measurable (routeBEpsilon rho) := by
  unfold routeBEpsilon
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  fun_prop

theorem measurable_routeBDiskBound (kappa rho r : ℝ) :
    Measurable (routeBDiskBound kappa rho r) := by
  have hepsilon : Measurable (routeBEpsilon rho) :=
    measurable_routeBEpsilon rho
  have hscore (x : ℝ) : Measurable (fun c : ℝ =>
      routeBDiskScore (routeBBeta r) routeBD0 (routeBEpsilon rho c) x) := by
    unfold routeBDiskScore
    exact (((measurable_const.sub hepsilon).pow_const 2).add
      (measurable_const.min measurable_const))
  unfold routeBDiskBound routeBDiskBoundSq
  dsimp only
  by_cases htransition :
      0 ≤ routeBTransition r ∧ routeBTransition r ≤ kappa
  · simp only [if_pos htransition]
    exact ((hscore 0).max ((hscore kappa).max
      (hscore (routeBTransition r)))).sqrt
  · simp only [if_neg htransition]
    exact ((hscore 0).max ((hscore kappa).max (hscore 0))).sqrt

/-- The normalized complex Taylor remainder used in the disk argument. -/
def routeBNormalizedRemainder (mu : Measure ℝ) (rho u : ℝ) : ℂ :=
  (charFun mu u - ((1 - u ^ 2 / 2 : ℝ) : ℂ)) /
    ((rho * |u| ^ 3 : ℝ) : ℂ)

theorem integrable_charFun_integrand_real
    (mu : Measure ℝ) [IsFiniteMeasure mu] (u : ℝ) :
    Integrable (fun x : ℝ =>
      Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I)) mu := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  exact ae_of_all mu fun x => by
    rw [Complex.norm_exp]
    simp

theorem charFun_re_eq_integral_cos
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (u : ℝ) :
    (charFun mu u).re = ∫ x : ℝ, Real.cos (u * x) ∂mu := by
  rw [charFun_apply_real]
  calc
    (∫ x : ℝ, Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I) ∂mu).re =
        ∫ x : ℝ, (Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I)).re ∂mu := by
      simpa using (integral_re (integrable_charFun_integrand_real mu u)).symm
    _ = ∫ x : ℝ, Real.cos (u * x) ∂mu := by
      apply integral_congr_ae
      exact ae_of_all mu fun x => by
        change (Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I)).re =
          Real.cos (u * x)
        rw [show (u : ℂ) * (x : ℂ) * Complex.I =
          (u * x : ℝ) * Complex.I by push_cast; ring]
        exact Complex.exp_ofReal_mul_I_re (u * x)

theorem charFun_im_eq_integral_sin
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (u : ℝ) :
    (charFun mu u).im = ∫ x : ℝ, Real.sin (u * x) ∂mu := by
  rw [charFun_apply_real]
  calc
    (∫ x : ℝ, Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I) ∂mu).im =
        ∫ x : ℝ, (Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I)).im ∂mu := by
      simpa using (integral_im (integrable_charFun_integrand_real mu u)).symm
    _ = ∫ x : ℝ, Real.sin (u * x) ∂mu := by
      apply integral_congr_ae
      exact ae_of_all mu fun x => by
        change (Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I)).im =
          Real.sin (u * x)
        rw [show (u : ℂ) * (x : ℂ) * Complex.I =
          (u * x : ℝ) * Complex.I by push_cast; ring]
        exact Complex.exp_ofReal_mul_I_im (u * x)

theorem integrable_abs_cube_of_memLp
    {mu : Measure ℝ} (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    Integrable (fun x : ℝ => |x| ^ 3) mu := by
  have h := hX.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
  simpa only [id_eq, Real.norm_eq_abs] using h

theorem integrable_routeBCosineRemainder
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) (u : ℝ) :
    Integrable (fun x : ℝ => routeBCosineRemainder (u * x)) mu := by
  have hcos : Integrable (fun x : ℝ => Real.cos (u * x)) mu := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    exact ae_of_all mu fun x => by
      simpa only [Real.norm_eq_abs, norm_one] using Real.abs_cos_le_one (u * x)
  have hsq : Integrable (fun x : ℝ => x ^ 2) mu :=
    (hX.mono_exponent (by norm_num)).integrable_sq
  have hquad : Integrable (fun x : ℝ => (u * x) ^ 2 / 2) mu := by
    have h := hsq.const_mul (u ^ 2 / 2)
    apply h.congr
    exact ae_of_all mu fun x => by ring
  unfold routeBCosineRemainder
  exact (hcos.sub (integrable_const 1)).add hquad

theorem integral_routeBCosineRemainder
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) (u : ℝ) :
    (∫ x : ℝ, routeBCosineRemainder (u * x) ∂mu) =
      (charFun mu u).re - (1 - u ^ 2 / 2) := by
  have hcos : Integrable (fun x : ℝ => Real.cos (u * x)) mu := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    exact ae_of_all mu fun x => by
      simpa only [Real.norm_eq_abs, norm_one] using Real.abs_cos_le_one (u * x)
  have hsq : Integrable (fun x : ℝ => x ^ 2) mu :=
    (hX.mono_exponent (by norm_num)).integrable_sq
  have hquad : Integrable (fun x : ℝ => (u * x) ^ 2 / 2) mu := by
    have h := hsq.const_mul (u ^ 2 / 2)
    apply h.congr
    exact ae_of_all mu fun x => by ring
  have hquadIntegral : (∫ x : ℝ, (u * x) ^ 2 / 2 ∂mu) = u ^ 2 / 2 := by
    calc
      (∫ x : ℝ, (u * x) ^ 2 / 2 ∂mu) =
          ∫ x : ℝ, (u ^ 2 / 2) * x ^ 2 ∂mu := by
            apply integral_congr_ae
            exact ae_of_all mu fun x => by ring
      _ = (u ^ 2 / 2) * ∫ x : ℝ, x ^ 2 ∂mu := by
        rw [integral_const_mul]
      _ = u ^ 2 / 2 := by rw [hsecond]; ring
  have hsubIntegral :
      (∫ x : ℝ, Real.cos (u * x) - 1 ∂mu) =
        (∫ x : ℝ, Real.cos (u * x) ∂mu) - ∫ _x : ℝ, (1 : ℝ) ∂mu := by
    simpa only [Pi.sub_apply] using
      integral_sub hcos (integrable_const (μ := mu) (1 : ℝ))
  have haddIntegral :
      (∫ x : ℝ, (Real.cos (u * x) - 1) + (u * x) ^ 2 / 2 ∂mu) =
        (∫ x : ℝ, Real.cos (u * x) - 1 ∂mu) +
          ∫ x : ℝ, (u * x) ^ 2 / 2 ∂mu := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      integral_add (hcos.sub (integrable_const (μ := mu) (1 : ℝ))) hquad
  unfold routeBCosineRemainder
  change (∫ x : ℝ, (Real.cos (u * x) - 1) + (u * x) ^ 2 / 2 ∂mu) =
    (charFun mu u).re - (1 - u ^ 2 / 2)
  rw [haddIntegral, hsubIntegral, integral_const, probReal_univ,
    hquadIntegral, charFun_re_eq_integral_cos]
  simp only [one_smul]
  ring

theorem routeBCosineRemainder_nonneg (v : ℝ) :
    0 ≤ routeBCosineRemainder v := by
  have h : 1 - v ^ 2 / 2 ≤ Real.cos v :=
    Real.one_sub_sq_div_two_le_cos
  unfold routeBCosineRemainder
  linarith

theorem routeBCosineRemainder_le_certificate {kappa theta : ℝ}
    (hcert : RouteBMinorantCertificate kappa theta) (v : ℝ) :
    routeBCosineRemainder v ≤ kappa * |v| ^ 3 := by
  by_cases hv : v = 0
  · simp [hv, routeBCosineRemainder]
  · let a : ℝ := |v|
    have ha : 0 < a := abs_pos.mpr hv
    have hminor := hcert.line_minorant a ha
    have hscaled := mul_le_mul_of_nonneg_left hminor (sq_nonneg a)
    have hacancel : a ^ 2 * routeBPsi a = 1 - Real.cos a := by
      unfold routeBPsi
      field_simp [ha.ne']
    rw [hacancel] at hscaled
    have hsq : a ^ 2 = v ^ 2 := by
      dsimp [a]
      exact sq_abs v
    have hcos : Real.cos a = Real.cos v := by
      dsimp [a]
      exact Real.cos_abs v
    unfold routeBCosineRemainder
    rw [← hcos, ← hsq]
    nlinarith

theorem charFun_real_remainder_nonneg
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) (u : ℝ) :
    0 ≤ (charFun mu u).re - (1 - u ^ 2 / 2) := by
  have hnonneg : 0 ≤ ∫ x : ℝ, routeBCosineRemainder (u * x) ∂mu :=
    integral_nonneg_of_ae (ae_of_all mu fun x =>
      routeBCosineRemainder_nonneg (u * x))
  rwa [integral_routeBCosineRemainder mu hX hsecond u] at hnonneg

theorem charFun_real_remainder_le_certificate
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    (u : ℝ) :
    (charFun mu u).re - (1 - u ^ 2 / 2) ≤
      (thirdAbsoluteMoment mu * |u| ^ 3) * kappa := by
  have hremInt := integrable_routeBCosineRemainder mu hX u
  have hcube := integrable_abs_cube_of_memLp hX
  have hdomInt : Integrable
      (fun x : ℝ => kappa * |u * x| ^ 3) mu := by
    have h := hcube.const_mul (kappa * |u| ^ 3)
    simpa only [abs_mul, mul_pow, mul_assoc] using h
  have hpoint : ∀ x : ℝ,
      routeBCosineRemainder (u * x) ≤ kappa * |u * x| ^ 3 :=
    fun x => routeBCosineRemainder_le_certificate hcert (u * x)
  have hIntegral := integral_mono hremInt hdomInt hpoint
  have hdomValue : (∫ x : ℝ, kappa * |u * x| ^ 3 ∂mu) =
      (thirdAbsoluteMoment mu * |u| ^ 3) * kappa := by
    calc
      (∫ x : ℝ, kappa * |u * x| ^ 3 ∂mu) =
          ∫ x : ℝ, (kappa * |u| ^ 3) * |x| ^ 3 ∂mu := by
            apply integral_congr_ae
            exact ae_of_all mu fun x => by
              change kappa * |u * x| ^ 3 = (kappa * |u| ^ 3) * |x| ^ 3
              rw [abs_mul, mul_pow]
              ring
      _ = (kappa * |u| ^ 3) * ∫ x : ℝ, |x| ^ 3 ∂mu := by
        rw [integral_const_mul]
      _ = (thirdAbsoluteMoment mu * |u| ^ 3) * kappa := by
        unfold thirdAbsoluteMoment
        ring
  rw [integral_routeBCosineRemainder mu hX hsecond u, hdomValue] at hIntegral
  exact hIntegral

theorem routeBNormalizedRemainder_re
    (mu : Measure ℝ) (rho u : ℝ) :
    (routeBNormalizedRemainder mu rho u).re =
      ((charFun mu u).re - (1 - u ^ 2 / 2)) / (rho * |u| ^ 3) := by
  unfold routeBNormalizedRemainder
  rw [Complex.div_re, Complex.normSq_ofReal]
  norm_num only [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_im, mul_zero, zero_div, add_zero]
  field_simp

theorem routeBNormalizedRemainder_im
    (mu : Measure ℝ) (rho u : ℝ) :
    (routeBNormalizedRemainder mu rho u).im =
      (charFun mu u).im / (rho * |u| ^ 3) := by
  unfold routeBNormalizedRemainder
  rw [Complex.div_im, Complex.normSq_ofReal]
  norm_num only [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_im, mul_zero, zero_div, sub_zero]
  field_simp

theorem routeBNormalizedRemainder_re_bounds
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    {u : ℝ} (hu : u ≠ 0) :
    0 ≤ (routeBNormalizedRemainder mu (thirdAbsoluteMoment mu) u).re ∧
      (routeBNormalizedRemainder mu (thirdAbsoluteMoment mu) u).re ≤ kappa := by
  have hrho : 0 < thirdAbsoluteMoment mu := by
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have huabs : 0 < |u| := abs_pos.mpr hu
  have hscale : 0 < thirdAbsoluteMoment mu * |u| ^ 3 := by positivity
  rw [routeBNormalizedRemainder_re]
  constructor
  · exact div_nonneg (charFun_real_remainder_nonneg mu hX hsecond u) hscale.le
  · apply (div_le_iff₀ hscale).2
    simpa only [mul_comm] using
      charFun_real_remainder_le_certificate mu hX hsecond hcert u

theorem routeBNormalizedRemainder_im_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {u : ℝ} (hu : u ≠ 0) :
    |(routeBNormalizedRemainder mu (thirdAbsoluteMoment mu) u).im| ≤
      routeBBeta (symmetrizationRatio mu) := by
  have hrho : 0 < thirdAbsoluteMoment mu := by
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have huabs : 0 < |u| := abs_pos.mpr hu
  have hscale : 0 < thirdAbsoluteMoment mu * |u| ^ 3 := by positivity
  have hsine := sine_remainder_circle mu hX hmean hsecond u
  have him : (charFun mu u).im = sineRemainderExpectation mu u := by
    rw [charFun_im_eq_integral_sin,
      sineRemainderExpectation_eq_sine_integral mu hX hmean]
  rw [routeBNormalizedRemainder_im, abs_div,
    abs_of_pos hscale, him]
  apply (div_le_iff₀ hscale).2
  unfold routeBBeta
  nlinarith

theorem routeBNormalizedRemainder_norm_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {u : ℝ} (hu : u ≠ 0) :
    ‖routeBNormalizedRemainder mu (thirdAbsoluteMoment mu) u‖ ≤ routeBD0 := by
  have hint1 : Integrable (fun x : ℝ => x) mu :=
    hX.integrable (by norm_num)
  have hint2 : Integrable (fun x : ℝ => x ^ 2) mu :=
    (hX.mono_exponent (by norm_num)).integrable_sq
  have hint3 := integrable_abs_cube_of_memLp hX
  have hTaylor := StatLean.HypothesisTesting.norm_charFun_sub_quadratic_le
    mu hint1 hint2 hint3 hmean hsecond u
  have hpoly :
      (1 - ((1 : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) =
        ((1 - u ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hpoly] at hTaylor
  have hrho : 0 < thirdAbsoluteMoment mu := by
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have huabs : 0 < |u| := abs_pos.mpr hu
  have hscale : 0 < thirdAbsoluteMoment mu * |u| ^ 3 := by positivity
  unfold routeBNormalizedRemainder
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale]
  apply (div_le_iff₀ hscale).2
  unfold routeBD0 thirdAbsoluteMoment
  nlinarith

theorem routeBBeta_nonneg (r : ℝ) : 0 ≤ routeBBeta r := by
  unfold routeBBeta
  positivity

theorem routeBD0_nonneg : 0 ≤ routeBD0 := by
  norm_num [routeBD0]

theorem routeBDiskScore_zero_nonneg (beta d epsilon : ℝ) :
    0 ≤ routeBDiskScore beta d epsilon 0 := by
  unfold routeBDiskScore
  have hbeta : 0 ≤ beta ^ 2 := sq_nonneg beta
  have hd : 0 ≤ d ^ 2 := sq_nonneg d
  have hmin : 0 ≤ min (beta ^ 2) (d ^ 2) := le_min hbeta hd
  simpa using add_nonneg (sq_nonneg (0 - epsilon)) hmin

theorem routeBDiskBoundSq_nonneg (kappa rho r c : ℝ) :
    0 ≤ routeBDiskBoundSq kappa rho r c := by
  unfold routeBDiskBoundSq
  exact (routeBDiskScore_zero_nonneg _ _ _).trans (le_max_left _ _)

theorem routeBDiskBound_nonneg (kappa rho r c : ℝ) :
    0 ≤ routeBDiskBound kappa rho r c := by
  exact Real.sqrt_nonneg _

/-- A squared distance on a nonnegative interval is maximized at an endpoint. -/
theorem sq_sub_le_max_endpoints {x z epsilon : ℝ}
    (hx : 0 ≤ x) (hxz : x ≤ z) (hepsilon : 0 ≤ epsilon) :
    (x - epsilon) ^ 2 ≤
      max (((0 : ℝ) - epsilon) ^ 2) ((z - epsilon) ^ 2) := by
  by_cases hxe : x ≤ epsilon
  · have hfactor : 0 ≤ x * (2 * epsilon - x) :=
      mul_nonneg hx (by linarith)
    calc
      (x - epsilon) ^ 2 ≤ ((0 : ℝ) - epsilon) ^ 2 := by nlinarith
      _ ≤ max (((0 : ℝ) - epsilon) ^ 2) ((z - epsilon) ^ 2) := le_max_left _ _
  · have hex : epsilon ≤ x := le_of_not_ge hxe
    have hfactor : 0 ≤ (z - x) * (z + x - 2 * epsilon) :=
      mul_nonneg (sub_nonneg.mpr hxz) (by linarith)
    calc
      (x - epsilon) ^ 2 ≤ (z - epsilon) ^ 2 := by nlinarith
      _ ≤ max (((0 : ℝ) - epsilon) ^ 2) ((z - epsilon) ^ 2) := le_max_right _ _

/-- The fixed-`x` score bounds every feasible vertical coordinate. -/
theorem complex_disk_distance_sq_le_score
    {beta d epsilon x y : ℝ}
    (hy : |y| ≤ beta) (hcircle : x ^ 2 + y ^ 2 ≤ d ^ 2) :
    (x - epsilon) ^ 2 + y ^ 2 ≤ routeBDiskScore beta d epsilon x := by
  have hysqBeta : y ^ 2 ≤ beta ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg y) hy 2
    simpa only [sq_abs] using h
  have hysqCircle : y ^ 2 ≤ d ^ 2 - x ^ 2 := by linarith
  unfold routeBDiskScore
  nlinarith [le_min hysqBeta hysqCircle]

/-- The planar maximum is attained among the two horizontal endpoints and the
single strip/circle transition point. -/
theorem routeBDiskScore_le_finite_candidates
    {kappa beta d epsilon transition x : ℝ}
    (hepsilon : 0 ≤ epsilon) (htransition : 0 ≤ transition)
    (htransitionSq : transition ^ 2 = d ^ 2 - beta ^ 2)
    (hx : 0 ≤ x) (hxkappa : x ≤ kappa) :
    routeBDiskScore beta d epsilon x ≤
      max (routeBDiskScore beta d epsilon 0)
        (max (routeBDiskScore beta d epsilon kappa)
          (if 0 ≤ transition ∧ transition ≤ kappa then
            routeBDiskScore beta d epsilon transition
          else routeBDiskScore beta d epsilon 0)) := by
  have hbetaSqLe : beta ^ 2 ≤ d ^ 2 := by
    nlinarith [sq_nonneg transition]
  have hminZero : min (beta ^ 2) (d ^ 2 - (0 : ℝ) ^ 2) = beta ^ 2 := by
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, min_eq_left hbetaSqLe]
  by_cases hxtransition : x ≤ transition
  · have hminX : min (beta ^ 2) (d ^ 2 - x ^ 2) = beta ^ 2 := by
      rw [min_eq_left]
      nlinarith [mul_nonneg hx (sub_nonneg.mpr hxtransition),
        sq_nonneg (transition - x)]
    by_cases htransitionKappa : transition ≤ kappa
    · have hcondition : 0 ≤ transition ∧ transition ≤ kappa :=
        ⟨htransition, htransitionKappa⟩
      have hminTransition :
          min (beta ^ 2) (d ^ 2 - transition ^ 2) = beta ^ 2 := by
        rw [min_eq_left]
        nlinarith
      have hdist := sq_sub_le_max_endpoints hx hxtransition hepsilon
      have hscore : routeBDiskScore beta d epsilon x ≤
          max (routeBDiskScore beta d epsilon 0)
            (routeBDiskScore beta d epsilon transition) := by
        unfold routeBDiskScore
        rw [hminX, hminZero, hminTransition]
        calc
          (x - epsilon) ^ 2 + beta ^ 2 ≤
              max (((0 : ℝ) - epsilon) ^ 2) ((transition - epsilon) ^ 2) +
                beta ^ 2 := by nlinarith
          _ = max (((0 : ℝ) - epsilon) ^ 2 + beta ^ 2)
              ((transition - epsilon) ^ 2 + beta ^ 2) := by
                rw [max_add_add_right]
      rw [if_pos hcondition]
      apply hscore.trans
      apply max_le
      · exact le_max_left _ _
      · exact (le_max_right _ _).trans (le_max_right _ _)
    · have hkappaTransition : kappa ≤ transition :=
        (lt_of_not_ge htransitionKappa).le
      have hkappa : 0 ≤ kappa := hx.trans hxkappa
      have hminKappa : min (beta ^ 2) (d ^ 2 - kappa ^ 2) = beta ^ 2 := by
        rw [min_eq_left]
        nlinarith [mul_nonneg hkappa (sub_nonneg.mpr hkappaTransition),
          sq_nonneg (transition - kappa)]
      have hdist := sq_sub_le_max_endpoints hx hxkappa hepsilon
      have hscore : routeBDiskScore beta d epsilon x ≤
          max (routeBDiskScore beta d epsilon 0)
            (routeBDiskScore beta d epsilon kappa) := by
        unfold routeBDiskScore
        rw [hminX, hminZero, hminKappa]
        calc
          (x - epsilon) ^ 2 + beta ^ 2 ≤
              max (((0 : ℝ) - epsilon) ^ 2) ((kappa - epsilon) ^ 2) +
                beta ^ 2 := by nlinarith
          _ = max (((0 : ℝ) - epsilon) ^ 2 + beta ^ 2)
              ((kappa - epsilon) ^ 2 + beta ^ 2) := by
                rw [max_add_add_right]
      have hcondition : ¬(0 ≤ transition ∧ transition ≤ kappa) := by
        intro h
        exact htransitionKappa h.2
      rw [if_neg hcondition]
      apply hscore.trans
      apply max_le
      · exact le_max_left _ _
      · exact (le_max_left _ _).trans (le_max_right _ _)
  · have htransitionX : transition ≤ x := (lt_of_not_ge hxtransition).le
    have htransitionKappa : transition ≤ kappa := htransitionX.trans hxkappa
    have hcondition : 0 ≤ transition ∧ transition ≤ kappa :=
      ⟨htransition, htransitionKappa⟩
    have hminX : min (beta ^ 2) (d ^ 2 - x ^ 2) = d ^ 2 - x ^ 2 := by
      rw [min_eq_right]
      nlinarith [mul_nonneg htransition (sub_nonneg.mpr htransitionX),
        sq_nonneg (x - transition)]
    have hminTransition :
        min (beta ^ 2) (d ^ 2 - transition ^ 2) = beta ^ 2 := by
      rw [min_eq_left]
      nlinarith
    have hscore : routeBDiskScore beta d epsilon x ≤
        routeBDiskScore beta d epsilon transition := by
      unfold routeBDiskScore
      rw [hminX, hminTransition]
      nlinarith [mul_nonneg hepsilon (sub_nonneg.mpr htransitionX)]
    simpa only [if_pos hcondition] using
      hscore.trans ((le_max_right
        (routeBDiskScore beta d epsilon kappa)
        (routeBDiskScore beta d epsilon transition)).trans
          (le_max_right (routeBDiskScore beta d epsilon 0) _))

theorem routeBTransition_nonneg {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ routeBTransition r := by
  unfold routeBTransition
  linarith

theorem routeBTransition_sq_eq {r : ℝ} (hrLower : 1 ≤ r) (hrUpper : r ≤ 2) :
    routeBTransition r ^ 2 = routeBD0 ^ 2 - routeBBeta r ^ 2 := by
  have hradicand : 0 ≤ 1 - (r - 1) ^ 2 := by nlinarith
  unfold routeBTransition routeBD0 routeBBeta
  rw [mul_pow, Real.sq_sqrt hradicand]
  ring

theorem routeBEpsilon_nonneg {rho c : ℝ} (hrho : 0 < rho) (hc : 0 ≤ c) :
    0 ≤ routeBEpsilon rho c := by
  by_cases hcZero : c = 0
  · simp [routeBEpsilon, hcZero]
  · have hcPos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcZero)
    let a : ℝ := c ^ 2 / (2 * rho ^ 2)
    have hrem : 0 ≤ Real.exp (-a) - 1 + a := by
      linarith [Real.add_one_le_exp (-a)]
    have hprefactor : 0 ≤ rho ^ 2 / c ^ 3 := by positivity
    have hrem' :
        0 ≤ Real.exp (-(c ^ 2) / (2 * rho ^ 2)) - 1 +
          c ^ 2 / (2 * rho ^ 2) := by
      simpa only [a, neg_div] using hrem
    unfold routeBEpsilon
    rw [if_neg hcZero]
    exact mul_nonneg hprefactor hrem'

/-- A coarse endpoint estimate sufficient for smoothing-integral
integrability.  It deliberately uses only `exp (-a) ≤ 1`, rather than a
higher-order Taylor bound. -/
theorem routeBEpsilon_le_inv_two_mul {rho c : ℝ}
    (hrho : 0 < rho) (hc : 0 < c) :
    routeBEpsilon rho c ≤ 1 / (2 * c) := by
  have hcNe : c ≠ 0 := hc.ne'
  let a : ℝ := c ^ 2 / (2 * rho ^ 2)
  have ha : 0 ≤ a := by
    dsimp only [a]
    positivity
  have hexp : Real.exp (-a) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
  have hrem : Real.exp (-a) - 1 + a ≤ a := by linarith
  have hprefactor : 0 ≤ rho ^ 2 / c ^ 3 := by positivity
  unfold routeBEpsilon
  rw [if_neg hcNe]
  calc
    rho ^ 2 / c ^ 3 *
          (Real.exp (-(c ^ 2) / (2 * rho ^ 2)) - 1 +
            c ^ 2 / (2 * rho ^ 2)) ≤
        rho ^ 2 / c ^ 3 * (c ^ 2 / (2 * rho ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hprefactor
      simpa only [a, neg_div] using hrem
    _ = 1 / (2 * c) := by
      field_simp [hrho.ne', hcNe]

/-- Every fixed-horizontal-coordinate disk score has a quadratic bound in
the Gaussian offset. -/
theorem routeBDiskScore_le_quadratic (beta d epsilon x : ℝ) :
    routeBDiskScore beta d epsilon x ≤
      2 * x ^ 2 + 2 * epsilon ^ 2 + beta ^ 2 := by
  have hmin : min (beta ^ 2) (d ^ 2 - x ^ 2) ≤ beta ^ 2 := min_le_left _ _
  have hsquare : 0 ≤ (x + epsilon) ^ 2 := sq_nonneg _
  unfold routeBDiskScore
  nlinarith

/-- A parameter-explicit quadratic bound for the finite disk maximum. -/
theorem routeBDiskBoundSq_le_quadratic (kappa rho r c : ℝ) :
    routeBDiskBoundSq kappa rho r c ≤
      2 * routeBEpsilon rho c ^ 2 + 2 * kappa ^ 2 +
        2 * routeBTransition r ^ 2 + routeBBeta r ^ 2 := by
  unfold routeBDiskBoundSq
  dsimp only
  refine max_le ?_ (max_le ?_ ?_)
  · calc
      routeBDiskScore (routeBBeta r) routeBD0 (routeBEpsilon rho c) 0 ≤
          2 * (0 : ℝ) ^ 2 + 2 * routeBEpsilon rho c ^ 2 +
            routeBBeta r ^ 2 := routeBDiskScore_le_quadratic _ _ _ _
      _ ≤ 2 * routeBEpsilon rho c ^ 2 + 2 * kappa ^ 2 +
            2 * routeBTransition r ^ 2 + routeBBeta r ^ 2 := by
        nlinarith [sq_nonneg kappa, sq_nonneg (routeBTransition r)]
  · calc
      routeBDiskScore (routeBBeta r) routeBD0 (routeBEpsilon rho c) kappa ≤
          2 * kappa ^ 2 + 2 * routeBEpsilon rho c ^ 2 +
            routeBBeta r ^ 2 := routeBDiskScore_le_quadratic _ _ _ _
      _ ≤ 2 * routeBEpsilon rho c ^ 2 + 2 * kappa ^ 2 +
            2 * routeBTransition r ^ 2 + routeBBeta r ^ 2 := by
        nlinarith [sq_nonneg (routeBTransition r)]
  · split_ifs
    · calc
        routeBDiskScore (routeBBeta r) routeBD0 (routeBEpsilon rho c)
            (routeBTransition r) ≤
            2 * routeBTransition r ^ 2 + 2 * routeBEpsilon rho c ^ 2 +
              routeBBeta r ^ 2 := routeBDiskScore_le_quadratic _ _ _ _
        _ ≤ 2 * routeBEpsilon rho c ^ 2 + 2 * kappa ^ 2 +
              2 * routeBTransition r ^ 2 + routeBBeta r ^ 2 := by
          nlinarith [sq_nonneg kappa]
    · calc
        routeBDiskScore (routeBBeta r) routeBD0 (routeBEpsilon rho c) 0 ≤
            2 * (0 : ℝ) ^ 2 + 2 * routeBEpsilon rho c ^ 2 +
              routeBBeta r ^ 2 := routeBDiskScore_le_quadratic _ _ _ _
        _ ≤ 2 * routeBEpsilon rho c ^ 2 + 2 * kappa ^ 2 +
              2 * routeBTransition r ^ 2 + routeBBeta r ^ 2 := by
          nlinarith [sq_nonneg kappa, sq_nonneg (routeBTransition r)]

/-- The disk radius grows at most quadratically in the Gaussian offset.  This
coarse form is chosen to make the removable lower-endpoint singularity
transparent. -/
theorem routeBDiskBound_le_quadratic (kappa rho r c : ℝ) :
    routeBDiskBound kappa rho r c ≤
      1 + 2 * routeBEpsilon rho c ^ 2 + 2 * kappa ^ 2 +
        2 * routeBTransition r ^ 2 + routeBBeta r ^ 2 := by
  let s := routeBDiskBoundSq kappa rho r c
  have hsNonneg : 0 ≤ s := routeBDiskBoundSq_nonneg kappa rho r c
  have hsqrtSq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hsNonneg
  have hsqrtNonneg : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hsqrtLe : Real.sqrt s ≤ 1 + s := by
    nlinarith [sq_nonneg (Real.sqrt s - (1 : ℝ) / 2)]
  unfold routeBDiskBound
  change Real.sqrt s ≤ _
  calc
    Real.sqrt s ≤ 1 + s := hsqrtLe
    _ ≤ 1 + 2 * routeBEpsilon rho c ^ 2 + 2 * kappa ^ 2 +
          2 * routeBTransition r ^ 2 + routeBBeta r ^ 2 := by
      linarith [routeBDiskBoundSq_le_quadratic kappa rho r c]

theorem routeBDiskBound_le_static_add_epsilon_sq (kappa rho r c : ℝ) :
    routeBDiskBound kappa rho r c ≤
      routeBDiskStaticConstant kappa r + 2 * routeBEpsilon rho c ^ 2 := by
  unfold routeBDiskStaticConstant
  linarith [routeBDiskBound_le_quadratic kappa rho r c]

theorem routeBEpsilon_scaled_frequency {rho u : ℝ}
    (hrho : 0 < rho) (hu : u ≠ 0) :
    routeBEpsilon rho (rho * |u|) =
      (Real.exp (-(u ^ 2) / 2) - 1 + u ^ 2 / 2) /
        (rho * |u| ^ 3) := by
  have huabs : 0 < |u| := abs_pos.mpr hu
  have hc : rho * |u| ≠ 0 := mul_ne_zero hrho.ne' huabs.ne'
  have harg :
      -((rho * |u|) ^ 2) / (2 * rho ^ 2) = -(u ^ 2) / 2 := by
    field_simp [hrho.ne']
    rw [sq_abs]
  unfold routeBEpsilon
  rw [if_neg hc, harg]
  field_simp [hrho.ne', huabs.ne']
  rw [sq_abs]

theorem complex_gaussian_eq_real (u : ℝ) :
    Complex.exp (-(u : ℂ) ^ 2 / 2) =
      (Real.exp (-(u ^ 2) / 2) : ℂ) := by
  rw [show -(u : ℂ) ^ 2 / 2 = ((-(u ^ 2) / 2 : ℝ) : ℂ) by
    push_cast; ring]
  exact (Complex.ofReal_exp (-(u ^ 2) / 2)).symm

theorem routeB_one_step_factorization
    (mu : Measure ℝ) {rho u : ℝ} (hrho : 0 < rho) (hu : u ≠ 0) :
    charFun mu u - Complex.exp (-(u : ℂ) ^ 2 / 2) =
      ((rho * |u| ^ 3 : ℝ) : ℂ) *
        (routeBNormalizedRemainder mu rho u -
          (routeBEpsilon rho (rho * |u|) : ℂ)) := by
  have huabs : 0 < |u| := abs_pos.mpr hu
  have hscale : rho * |u| ^ 3 ≠ 0 := by positivity
  have hrhoC : (rho : ℂ) ≠ 0 := by exact_mod_cast hrho.ne'
  have huabsC : ((|u| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast huabs.ne'
  rw [complex_gaussian_eq_real,
    routeBEpsilon_scaled_frequency hrho hu]
  unfold routeBNormalizedRemainder
  push_cast
  field_simp [hscale, hrhoC, huabsC]
  ring

theorem routeB_complex_disk_distance_sq_le_boundSq
    {kappa rho r c x y : ℝ}
    (hrho : 0 < rho) (hc : 0 ≤ c)
    (hrLower : 1 ≤ r) (hrUpper : r ≤ 2)
    (hx : 0 ≤ x) (hxkappa : x ≤ kappa)
    (hy : |y| ≤ routeBBeta r)
    (hcircle : x ^ 2 + y ^ 2 ≤ routeBD0 ^ 2) :
    (x - routeBEpsilon rho c) ^ 2 + y ^ 2 ≤
      routeBDiskBoundSq kappa rho r c := by
  calc
    (x - routeBEpsilon rho c) ^ 2 + y ^ 2 ≤
        routeBDiskScore (routeBBeta r) routeBD0 (routeBEpsilon rho c) x :=
      complex_disk_distance_sq_le_score hy hcircle
    _ ≤ routeBDiskBoundSq kappa rho r c := by
      unfold routeBDiskBoundSq
      exact routeBDiskScore_le_finite_candidates
        (routeBEpsilon_nonneg hrho hc)
        (routeBTransition_nonneg hrLower)
        (routeBTransition_sq_eq hrLower hrUpper) hx hxkappa

theorem routeB_complex_disk_norm_le_bound
    {kappa rho r c : ℝ} (z : ℂ)
    (hrho : 0 < rho) (hc : 0 ≤ c)
    (hrLower : 1 ≤ r) (hrUpper : r ≤ 2)
    (hreLower : 0 ≤ z.re) (hreUpper : z.re ≤ kappa)
    (him : |z.im| ≤ routeBBeta r)
    (hnorm : ‖z‖ ≤ routeBD0) :
    ‖z - (routeBEpsilon rho c : ℂ)‖ ≤
      routeBDiskBound kappa rho r c := by
  have hnormSq : ‖z‖ ^ 2 ≤ routeBD0 ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg z) hnorm 2
  have hcircle : z.re ^ 2 + z.im ^ 2 ≤ routeBD0 ^ 2 := by
    calc
      z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by
        rw [Complex.normSq_apply]
        ring
      _ = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
      _ ≤ routeBD0 ^ 2 := hnormSq
  have hsq := routeB_complex_disk_distance_sq_le_boundSq hrho hc
    hrLower hrUpper hreLower hreUpper him hcircle
  apply (sq_le_sq₀ (norm_nonneg _) (routeBDiskBound_nonneg kappa rho r c)).mp
  change ‖z - (routeBEpsilon rho c : ℂ)‖ ^ 2 ≤
    routeBDiskBound kappa rho r c ^ 2
  rw [routeBDiskBound, Real.sq_sqrt (routeBDiskBoundSq_nonneg kappa rho r c)]
  rw [Complex.sq_norm, Complex.normSq_apply]
  norm_num only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero]
  simpa only [pow_two] using hsq

/-- Route B equation (3.8): the one-factor characteristic function lies in the
finite disk bound (3.7).  The only non-analytic input is the same explicit
breakpoint certificate already used in (3.3)--(3.5). -/
theorem routeB_one_step_disk
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    (u : ℝ) :
    ‖charFun mu u - Complex.exp (-(u : ℂ) ^ 2 / 2)‖ ≤
      thirdAbsoluteMoment mu * |u| ^ 3 *
        routeBDiskBound kappa (thirdAbsoluteMoment mu)
          (symmetrizationRatio mu) (thirdAbsoluteMoment mu * |u|) := by
  by_cases hu : u = 0
  · subst u
    simp [charFun_zero, probReal_univ]
  · have hrho : 0 < thirdAbsoluteMoment mu := by
      linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
    have hscale : 0 < thirdAbsoluteMoment mu * |u| ^ 3 := by
      have huabs : 0 < |u| := abs_pos.mpr hu
      positivity
    have hrLower := symmetrizationRatio_lower mu hX hmean hsecond
    have hrUpper := symmetrizationRatio_le_two mu hX hmean hsecond
    have hre := routeBNormalizedRemainder_re_bounds mu hX hsecond hcert hu
    have him := routeBNormalizedRemainder_im_bound mu hX hmean hsecond hu
    have hnorm := routeBNormalizedRemainder_norm_bound mu hX hmean hsecond hu
    have hgeometry := routeB_complex_disk_norm_le_bound
      (kappa := kappa)
      (rho := thirdAbsoluteMoment mu)
      (r := symmetrizationRatio mu)
      (c := thirdAbsoluteMoment mu * |u|)
      (routeBNormalizedRemainder mu (thirdAbsoluteMoment mu) u)
      hrho (mul_nonneg hrho.le (abs_nonneg u)) hrLower hrUpper
      hre.1 hre.2 him hnorm
    rw [routeB_one_step_factorization mu hrho hu, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale]
    exact mul_le_mul_of_nonneg_left hgeometry hscale.le

end

end BerryEsseen
