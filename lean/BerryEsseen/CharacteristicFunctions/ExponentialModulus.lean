import BerryEsseen.BreakpointNumerics
import BerryEsseen.DyadicElementary
import BerryEsseen.PrawitzLargeN
import BerryEsseen.SineCircle

/-!
# Characteristic Functions / Exponential Modulus
-/

open Finset

namespace BerryEsseen

noncomputable section

lemma sqrt_sub_le_max_inv_mul
    {rho r : ℝ} (hrho : 0 < rho) (hr : 1 ≤ r) :
    Real.sqrt (r - 1) ≤ max (1 / rho) (rho * (r - 1)) := by
  let a := 1 / rho
  let b := rho * (r - 1)
  let m := max a b
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have hb0 : 0 ≤ b := by
    dsimp only [b]
    exact mul_nonneg hrho.le (sub_nonneg.mpr hr)
  have hm0 : 0 ≤ m := ha0.trans (le_max_left _ _)
  have ha : a ≤ m := le_max_left _ _
  have hb : b ≤ m := le_max_right _ _
  have hab : a * b = r - 1 := by
    dsimp only [a, b]
    field_simp [hrho.ne']
  have hprod : a * b ≤ m ^ 2 := by
    rw [pow_two]
    exact mul_le_mul ha hb hb0 hm0
  have hsqrtSq : (Real.sqrt (r - 1)) ^ 2 = r - 1 :=
    Real.sq_sqrt (sub_nonneg.mpr hr)
  nlinarith [Real.sqrt_nonneg (r - 1)]

lemma d_le_one_sub_sqrt
    {d rho r : ℝ} (hrho : 0 < rho) (hr : 1 ≤ r)
    (hdInv : d ≤ 1 - 1 / rho)
    (hdStop : d ≤ 1 - rho * (r - 1)) :
    d ≤ 1 - Real.sqrt (r - 1) := by
  have hdMax : d ≤ 1 - max (1 / rho) (rho * (r - 1)) := by
    rcases le_total (1 / rho) (rho * (r - 1)) with h | h
    · rw [max_eq_right h]
      exact hdStop
    · rw [max_eq_left h]
      exact hdInv
  have hsqrt := sqrt_sub_le_max_inv_mul hrho hr
  linarith

lemma d_le_thirteen_over_250
    {d r : ℝ} (hr : 19 / 10 ≤ r)
    (hd : d ≤ 1 - Real.sqrt (r - 1)) :
    d ≤ 13 / 250 := by
  have hrm0 : 0 ≤ r - 1 := by norm_num at hr ⊢; linarith
  have hsquare : (237 / 250 : ℝ) ^ 2 ≤ r - 1 := by
    norm_num at hr ⊢
    linarith
  have hsqrt : (237 / 250 : ℝ) ≤ Real.sqrt (r - 1) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 237 / 250)]
    exact Real.sqrt_le_sqrt hsquare
  nlinarith

lemma low_frequency_le_five_sixths
    {t rho r : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4)
    (hrho : 1 ≤ rho) (hr : 19 / 10 ≤ r) :
    2 * Real.pi * t / (rho * r) ≤ 5 / 6 := by
  have hrho0 : 0 ≤ rho := zero_le_one.trans hrho
  have hr0 : 0 ≤ r := by norm_num at hr ⊢; linarith
  have hdenPos : 0 < rho * r :=
    mul_pos (zero_lt_one.trans_le hrho) (by norm_num at hr ⊢; linarith)
  have hdenLower : (19 / 10 : ℝ) ≤ rho * r := by
    calc
      (19 / 10 : ℝ) = 1 * (19 / 10) := by ring
      _ ≤ rho * r := mul_le_mul hrho hr (by norm_num) hrho0
  have hpi : Real.pi < 19 / 6 :=
    Real.pi_lt_d20.trans_le (by norm_num [piUpper20])
  have hfreq : 2 * Real.pi * t ≤ 19 / 12 := by
    have htwoPi0 : 0 ≤ 2 * Real.pi := by positivity
    have hmul := mul_le_mul_of_nonneg_left ht htwoPi0
    nlinarith
  apply (div_le_iff₀ hdenPos).2
  have hrhs : (19 / 12 : ℝ) ≤ (5 / 6 : ℝ) * (rho * r) := by
    nlinarith
  exact hfreq.trans hrhs

lemma cos_le_fourth
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.cos u ≤ 1 - u ^ 2 / 2 + u ^ 4 / 24 := by
  have h := cos_upper_bound hu0 hu1 1
  norm_num [alternatingPartial, cosMagnitude, sum_range_succ] at h
  nlinarith

lemma sin_le_fifth
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.sin u ≤ u - u ^ 3 / 6 + u ^ 5 / 120 := by
  have h := sin_upper_bound hu0 hu1 1
  norm_num [alternatingPartial, sinMagnitude, sum_range_succ] at h
  nlinarith

lemma cos_nonneg
    {u : ℝ} (hu0 : 0 ≤ u) (hu56 : u ≤ 5 / 6) :
    0 ≤ Real.cos u := by
  have hu1 : u ≤ 1 := by norm_num at hu56 ⊢; linarith
  have h := cos_lower_bound hu0 hu1 1
  norm_num [alternatingPartial, cosMagnitude, sum_range_succ] at h
  have hu2 : u ^ 2 ≤ (5 / 6 : ℝ) ^ 2 := by nlinarith
  nlinarith

lemma sin_nonneg
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ Real.sin u := by
  have h := sin_lower_bound hu0 hu1 1
  norm_num [alternatingPartial, sinMagnitude, sum_range_succ] at h
  have hu2 : u ^ 2 ≤ 1 := by nlinarith
  nlinarith

lemma sqrt_two_d_le
    {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 13 / 250) :
    Real.sqrt (2 * d) ≤ 81 / 250 := by
  have hsqrt0 : 0 ≤ Real.sqrt (2 * d) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (2 * d)) ^ 2 = 2 * d := by
    rw [Real.sq_sqrt]
    nlinarith
  nlinarith

lemma u_cube_le
    {u : ℝ} (hu0 : 0 ≤ u) (hu56 : u ≤ 5 / 6) :
    u ^ 3 ≤ (5 / 6 : ℝ) * u ^ 2 := by
  nlinarith [sq_nonneg u]

lemma imag_envelope_le
    {d u : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 13 / 250)
    (hu0 : 0 ≤ u) (hu56 : u ≤ 5 / 6) :
    Real.sqrt (2 * d) * |Real.sin u - u * Real.cos u| + d * u ^ 2 ≤
      (71 / 500 : ℝ) * u ^ 2 := by
  have hsqrt := sqrt_two_d_le hd0 hd
  have hremainder := abs_mul_cos_sub_sin_le_cube_div_three u hu0
  have habs : |Real.sin u - u * Real.cos u| ≤ u ^ 3 / 3 := by
    simpa [abs_sub_comm] using hremainder
  have hmul :
      Real.sqrt (2 * d) * |Real.sin u - u * Real.cos u| ≤
        (81 / 250 : ℝ) * (u ^ 3 / 3) := by
    calc
      Real.sqrt (2 * d) * |Real.sin u - u * Real.cos u| ≤
          (81 / 250 : ℝ) * |Real.sin u - u * Real.cos u| :=
        mul_le_mul_of_nonneg_right hsqrt (abs_nonneg _)
      _ ≤ (81 / 250 : ℝ) * (u ^ 3 / 3) :=
        mul_le_mul_of_nonneg_left habs (by norm_num)
  have hcube := u_cube_le hu0 hu56
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  nlinarith

def realPolynomial (x : ℝ) : ℝ :=
  1 - (99 / 250 : ℝ) * x +
    ((1 / 24 : ℝ) - 13 / 1500) * x ^ 2 +
    (13 / 30000 : ℝ) * x ^ 3

lemma real_envelope_le
    {d u : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 13 / 250)
    (hu0 : 0 ≤ u) (hu56 : u ≤ 5 / 6) :
    Real.cos u + d * (u * Real.sin u + u ^ 2) ≤
      realPolynomial (u ^ 2) := by
  have hu1 : u ≤ 1 := by norm_num at hu56 ⊢; linarith
  have hcos := cos_le_fourth hu0 hu1
  have hsin := sin_le_fifth hu0 hu1
  have hsin0 := sin_nonneg hu0 hu1
  have hfactor0 : 0 ≤ u * Real.sin u + u ^ 2 := by positivity
  have hdmul :
      d * (u * Real.sin u + u ^ 2) ≤
        (13 / 250 : ℝ) * (u * Real.sin u + u ^ 2) :=
    mul_le_mul_of_nonneg_right hd hfactor0
  have husin :
      u * Real.sin u ≤ u * (u - u ^ 3 / 6 + u ^ 5 / 120) :=
    mul_le_mul_of_nonneg_left hsin hu0
  unfold realPolynomial
  nlinarith

lemma real_envelope_nonneg
    {d u : ℝ} (hd0 : 0 ≤ d)
    (hu0 : 0 ≤ u) (hu56 : u ≤ 5 / 6) :
    0 ≤ Real.cos u + d * (u * Real.sin u + u ^ 2) := by
  have hu1 : u ≤ 1 := by norm_num at hu56 ⊢; linarith
  have hcos0 := cos_nonneg hu0 hu56
  have hsin0 := sin_nonneg hu0 hu1
  positivity

lemma sq_le_25_36
    {u : ℝ} (hu0 : 0 ≤ u) (hu56 : u ≤ 5 / 6) :
    0 ≤ u ^ 2 ∧ u ^ 2 ≤ (25 / 36 : ℝ) := by
  constructor
  · positivity
  · nlinarith

lemma exp_polynomial_gap_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hxh : x ≤ 25 / 36) :
    0 ≤
      (1 - (39 / 50 : ℝ) * x +
          ((39 / 50 : ℝ) * x) ^ 2 / 2 -
          ((39 / 50 : ℝ) * x) ^ 3 / 6) -
        (realPolynomial x) ^ 2 -
        ((71 / 500 : ℝ) * x) ^ 2 := by
  have hx2 : x ^ 2 ≤ (25 / 36 : ℝ) * x := by nlinarith
  have hx3 : x ^ 3 ≤ (25 / 36 : ℝ) ^ 2 * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2) hx0]
  have hx4 : x ^ 4 ≤ (25 / 36 : ℝ) ^ 3 * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx3) hx0]
  have hx5 : x ^ 5 ≤ (25 / 36 : ℝ) ^ 4 * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx4) hx0]
  have hx6 : x ^ 6 ≤ (25 / 36 : ℝ) ^ 5 * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx5) hx0]
  unfold realPolynomial
  nlinarith

lemma rectangular_sq_le_exp
    {d u : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 13 / 250)
    (hu0 : 0 ≤ u) (hu56 : u ≤ 5 / 6) :
    (Real.cos u + d * (u * Real.sin u + u ^ 2)) ^ 2 +
        (Real.sqrt (2 * d) * |Real.sin u - u * Real.cos u| +
          d * u ^ 2) ^ 2 ≤
      Real.exp (-((39 / 50 : ℝ) * u ^ 2)) := by
  let x := u ^ 2
  let A := Real.cos u + d * (u * Real.sin u + u ^ 2)
  let B := Real.sqrt (2 * d) * |Real.sin u - u * Real.cos u| + d * u ^ 2
  have hx := sq_le_25_36 hu0 hu56
  have hA0 : 0 ≤ A := by
    simpa only [A] using real_envelope_nonneg hd0 hu0 hu56
  have hAP0 : 0 ≤ realPolynomial x :=
    (show 0 ≤ A from hA0).trans (by
      simpa only [A, x] using real_envelope_le hd0 hd hu0 hu56)
  have hA : A ≤ realPolynomial x := by
    simpa only [A, x] using real_envelope_le hd0 hd hu0 hu56
  have hB0 : 0 ≤ B := by positivity
  have hB : B ≤ (71 / 500 : ℝ) * x := by
    simpa only [B, x] using imag_envelope_le hd0 hd hu0 hu56
  have hsqA : A ^ 2 ≤ (realPolynomial x) ^ 2 := by nlinarith
  have hsqB : B ^ 2 ≤ ((71 / 500 : ℝ) * x) ^ 2 := by nlinarith
  have hgap := exp_polynomial_gap_nonneg hx.1 hx.2
  have hy0 : 0 ≤ (39 / 50 : ℝ) * x := by positivity
  have hy1 : (39 / 50 : ℝ) * x ≤ 1 := by nlinarith
  have hexp := expNeg_lower_bound hy0 hy1 2
  norm_num [alternatingPartial, expMagnitude, sum_range_succ] at hexp
  dsimp only [A, B, x] at hsqA hsqB ⊢
  nlinarith

/-- Uniform large-`n` characteristic-function modulus rate used by the first-absolute-moment bounds.
The square-root form is the one needed by the telescoping power factor. -/
theorem rectangular_modulus_le_exp
    {d u : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 13 / 250)
    (hu0 : 0 ≤ u) (hu56 : u ≤ 5 / 6) :
    Real.sqrt
        ((Real.cos u + d * (u * Real.sin u + u ^ 2)) ^ 2 +
          (Real.sqrt (2 * d) * |Real.sin u - u * Real.cos u| +
            d * u ^ 2) ^ 2) ≤
      Real.exp (-((39 / 100 : ℝ) * u ^ 2)) := by
  have hsq := rectangular_sq_le_exp hd0 hd hu0 hu56
  have hnonneg :
      0 ≤
        (Real.cos u + d * (u * Real.sin u + u ^ 2)) ^ 2 +
          (Real.sqrt (2 * d) * |Real.sin u - u * Real.cos u| +
            d * u ^ 2) ^ 2 := by positivity
  have hsqrt := Real.sqrt_le_sqrt hsq
  have hexpSqrt :
      Real.sqrt (Real.exp (-((39 / 50 : ℝ) * u ^ 2))) =
        Real.exp (-((39 / 100 : ℝ) * u ^ 2)) := by
    calc
      Real.sqrt (Real.exp (-((39 / 50 : ℝ) * u ^ 2))) =
          Real.sqrt ((Real.exp (-((39 / 100 : ℝ) * u ^ 2))) ^ 2) := by
        congr 1
        rw [show (Real.exp (-((39 / 100 : ℝ) * u ^ 2))) ^ 2 =
            Real.exp (-((39 / 100 : ℝ) * u ^ 2) +
              -((39 / 100 : ℝ) * u ^ 2)) by
              rw [pow_two, ← Real.exp_add]]
        congr 1
        ring
      _ = |Real.exp (-((39 / 100 : ℝ) * u ^ 2))| :=
        Real.sqrt_sq_eq_abs _
      _ = Real.exp (-((39 / 100 : ℝ) * u ^ 2)) :=
        abs_of_pos (Real.exp_pos _)
  rwa [hexpSqrt] at hsqrt

/-- Abstract complex-number bridge used to instantiate the rate with the
characteristic function after the real and imaginary moment bounds are proved. -/
theorem complex_norm_le_exp
    {d u : ℝ} {z : ℂ}
    (hd0 : 0 ≤ d) (hd : d ≤ 13 / 250)
    (hu0 : 0 ≤ u) (hu56 : u ≤ 5 / 6)
    (hreLower : 1 - u ^ 2 / 2 ≤ z.re)
    (hreUpper :
      z.re ≤ Real.cos u + d * (u * Real.sin u + u ^ 2))
    (him :
      |z.im| ≤ Real.sqrt (2 * d) *
        |Real.sin u - u * Real.cos u| + d * u ^ 2) :
    ‖z‖ ≤ Real.exp (-((39 / 100 : ℝ) * u ^ 2)) := by
  let A := Real.cos u + d * (u * Real.sin u + u ^ 2)
  let B := Real.sqrt (2 * d) *
    |Real.sin u - u * Real.cos u| + d * u ^ 2
  have hu2 : u ^ 2 ≤ (25 / 36 : ℝ) :=
    (sq_le_25_36 hu0 hu56).2
  have hre0 : 0 ≤ z.re := by nlinarith
  have hA0 : 0 ≤ A := by
    simpa only [A] using real_envelope_nonneg hd0 hu0 hu56
  have hB0 : 0 ≤ B := by positivity
  have hreSq : z.re ^ 2 ≤ A ^ 2 := by
    dsimp only [A] at hreUpper ⊢
    nlinarith
  have himSq : z.im ^ 2 ≤ B ^ 2 := by
    have himAbs0 : 0 ≤ |z.im| := abs_nonneg _
    have hsquare : |z.im| ^ 2 ≤ B ^ 2 := by
      dsimp only [B] at him hB0 ⊢
      nlinarith
    simpa [sq_abs] using hsquare
  have hsum : z.re ^ 2 + z.im ^ 2 ≤ A ^ 2 + B ^ 2 :=
    add_le_add hreSq himSq
  have hsqrt := Real.sqrt_le_sqrt hsum
  have hrate := rectangular_modulus_le_exp hd0 hd hu0 hu56
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  exact hsqrt.trans (by simpa only [A, B] using hrate)

def largeRateQ (r y : ℝ) : ℝ :=
  (39 / 100 : ℝ) * (2 * Real.pi * y) ^ 2 / r ^ 2

lemma largeRateQ_nonneg
    {r y : ℝ} : 0 ≤ largeRateQ r y := by
  unfold largeRateQ
  positivity

lemma rate_frequency_eq_small
    {n : ℕ} (hn : 0 < n) {rho r y : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) :
    (n : ℝ) * ((39 / 100 : ℝ) *
      routeBUFrequency rho r (routeBSmoothingScale n rho * y) ^ 2) =
        largeRateQ r y := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  unfold largeRateQ routeBUFrequency routeBSmoothingScale
  field_simp [hrho.ne', hr.ne', hsqrt.ne']
  rw [Real.sq_sqrt hnReal.le]

/-- Generic power-factor consequence of the fixed `39/100` modulus rate. -/
lemma max_pow_le_rate_exp
    {n : ℕ} (hn : 100 ≤ n) {A u : ℝ}
    (hA0 : 0 ≤ A)
    (hA : A ≤ Real.exp (-((39 / 100 : ℝ) * u ^ 2))) :
    (max A (Real.exp (-(u ^ 2 / 2)))) ^ (n - 1) ≤
      Real.exp (-routeBLargeNAlpha *
        ((n : ℝ) * ((39 / 100 : ℝ) * u ^ 2))) := by
  let x := (39 / 100 : ℝ) * u ^ 2
  have hx : 0 ≤ x := by positivity
  have hnormal : Real.exp (-(u ^ 2 / 2)) ≤ Real.exp (-x) := by
    apply Real.exp_le_exp.mpr
    dsimp only [x]
    nlinarith [sq_nonneg u]
  have hmax : max A (Real.exp (-(u ^ 2 / 2))) ≤ Real.exp (-x) :=
    max_le (by simpa only [x] using hA) hnormal
  have hpow := pow_le_pow_left₀
    (hA0.trans (le_max_left _ _)) hmax (n - 1)
  have hcoefficient := routeBLargeNAlpha_mul_nat_le_sub_one hn
  have hexponent : ((n - 1 : ℕ) : ℝ) * (-x) ≤
      -routeBLargeNAlpha * ((n : ℝ) * x) := by
    nlinarith [mul_le_mul_of_nonneg_right hcoefficient hx]
  calc
    (max A (Real.exp (-(u ^ 2 / 2)))) ^ (n - 1) ≤
        Real.exp (-x) ^ (n - 1) := hpow
    _ = Real.exp (((n - 1 : ℕ) : ℝ) * (-x)) := by
      rw [Real.exp_nat_mul]
    _ ≤ Real.exp (-routeBLargeNAlpha * ((n : ℝ) * x)) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp (-routeBLargeNAlpha *
        ((n : ℝ) * ((39 / 100 : ℝ) * u ^ 2))) := by
      simp only [x]

theorem max_pow_le_small_rate_exp
    {n : ℕ} (hn : 100 ≤ n) {rho r y A : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) (hA0 : 0 ≤ A)
    (hA : A ≤ Real.exp (-((39 / 100 : ℝ) *
      routeBUFrequency rho r (routeBSmoothingScale n rho * y) ^ 2))) :
    (max A (Real.exp (-(routeBUFrequency rho r
      (routeBSmoothingScale n rho * y) ^ 2 / 2)))) ^ (n - 1) ≤
        Real.exp (-routeBLargeNAlpha * largeRateQ r y) := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hpow := max_pow_le_rate_exp hn hA0 hA
  rw [rate_frequency_eq_small hnPos hrho hr] at hpow
  exact hpow

end

end BerryEsseen
