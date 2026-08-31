import BerryEsseen.Smoothing.PrawitzDbound
import BerryEsseen.Smoothing.ExplicitSmoothing
/-!
# Large-`n` Route B envelopes

This module formalizes the analytic reduction used before the three compact large-`n`
certificates.  Its first layer proves the two exponential power bounds from the numerical-lemma
supplement.  The later disk and integral layers can therefore be developed against a fixed
`n = 100`-independent integrand.
-/

namespace BerryEsseen

noncomputable section

/-- The uniform exponent loss `(n - 1) / n ≥ 99 / 100` for `n ≥ 100`. -/
def routeBLargeNAlpha : ℝ := 99 / 100

/-- The exponent denoted by `Q(t)` before rewriting it in terms of
`L = rho / sqrt n`. -/
def routeBLargeNQ (n : ℕ) (rho r t : ℝ) : ℝ :=
  (n : ℝ) * routeBUFrequency rho r t ^ 2 *
    routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t)

/-- The checker-facing form of `Q(t)`, expressed through
`L = rho / sqrt n`. -/
def routeBLargeQ (L r t : ℝ) : ℝ :=
  (2 * Real.pi * t) ^ 2 *
      routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t) /
    (r ^ 2 * L ^ 2)

lemma routeBLargeQ_nonneg
    {L r t : ℝ} (hL : 0 < L) (hr : 0 < r) (ht : 0 ≤ t) :
    0 ≤ routeBLargeQ L r t := by
  unfold routeBLargeQ
  exact div_nonneg
    (mul_nonneg (sq_nonneg _)
      (routeBMinorant_nonneg routeB_exactMinorantCertificate _ (by positivity)))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem routeBLargeNQ_eq_routeBLargeQ
    {n : ℕ} {rho r t : ℝ}
    (hn : 0 < n) (hrho : 0 < rho) (hr : 0 < r) :
    routeBLargeNQ n rho r t =
      routeBLargeQ (routeBSmoothingScale n rho) r t := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  unfold routeBLargeNQ routeBLargeQ routeBUFrequency routeBSmoothingScale
  field_simp [hrho.ne', hr.ne', hsqrt.ne']
  rw [Real.sq_sqrt hnReal.le]
  ring

lemma routeBLargeNAlpha_nonneg : 0 ≤ routeBLargeNAlpha := by
  norm_num [routeBLargeNAlpha]

lemma routeBLargeNAlpha_le_one : routeBLargeNAlpha ≤ 1 := by
  norm_num [routeBLargeNAlpha]

lemma routeBLargeNAlpha_mul_nat_le_sub_one
    {n : ℕ} (hn : 100 ≤ n) :
    routeBLargeNAlpha * (n : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
  have hnOne : 1 ≤ n := by omega
  have hnReal : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Nat.cast_sub hnOne]
  norm_num [routeBLargeNAlpha]
  linarith

/-- The elementary square-root form of `[1 - x]₊ ≤ exp(-x)`, with the factor two
used by the Route B modulus envelope. -/
lemma sqrt_max_one_sub_two_mul_le_exp_neg
    {x : ℝ} (_hx : 0 ≤ x) :
    Real.sqrt (max (1 - 2 * x) 0) ≤ Real.exp (-x) := by
  have hone : 1 - 2 * x ≤ Real.exp (-2 * x) := by
    linarith [Real.add_one_le_exp (-2 * x)]
  have hmax : max (1 - 2 * x) 0 ≤ Real.exp (-2 * x) :=
    max_le hone (Real.exp_nonneg _)
  have hsq : Real.sqrt (max (1 - 2 * x) 0) ^ 2 ≤ Real.exp (-x) ^ 2 := by
    rw [Real.sq_sqrt (le_max_right _ _)]
    calc
      max (1 - 2 * x) 0 ≤ Real.exp (-2 * x) := hmax
      _ = Real.exp (-x) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.exp_nonneg _)).mp hsq

lemma routeBLargeN_minorant_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t) := by
  apply routeBMinorant_nonneg routeB_exactMinorantCertificate
  positivity

lemma routeBLargeN_minorant_le_half
    {t : ℝ} (ht : 0 ≤ t) :
    routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t) ≤ 1 / 2 := by
  have hv : 0 ≤ 2 * Real.pi * t := by positivity
  have habs := routeBMinorant_abs_le_half
    routeB_exactMinorantCertificate (2 * Real.pi * t) hv
  rw [abs_of_nonneg (routeBMinorant_nonneg
    routeB_exactMinorantCertificate _ hv)] at habs
  exact habs

theorem routeBModulusEnvelope_le_largeN_exp
    {rho r t : ℝ} (hrho : 0 < rho) (hr : 0 < r) (ht : 0 ≤ t) :
    routeBModulusEnvelope routeBKappa routeBTheta rho r t ≤
      Real.exp (-(routeBUFrequency rho r t ^ 2 *
        routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t))) := by
  let x := routeBUFrequency rho r t ^ 2 *
    routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t)
  have hx : 0 ≤ x := mul_nonneg (sq_nonneg _) (routeBLargeN_minorant_nonneg ht)
  unfold routeBModulusEnvelope
  convert sqrt_max_one_sub_two_mul_le_exp_neg hx using 1 <;>
    dsimp only [x] <;> ring

theorem routeBGaussianEnvelope_le_largeN_exp
    {rho r t : ℝ} (hrho : 0 < rho) (hr : 0 < r) (ht : 0 ≤ t) :
    routeBGaussianEnvelope rho r t ≤
      Real.exp (-(routeBUFrequency rho r t ^ 2 *
        routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t))) := by
  have hq := routeBLargeN_minorant_le_half ht
  have hu2 : 0 ≤ routeBUFrequency rho r t ^ 2 := sq_nonneg _
  unfold routeBGaussianEnvelope
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hq hu2]

theorem routeBPowerModulusEnvelope_le_largeN_exp
    {n : ℕ} {rho r t : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) (ht : 0 ≤ t) :
    routeBPowerModulusEnvelope routeBKappa routeBTheta n rho r t ≤
      Real.exp (-routeBLargeNQ n rho r t) := by
  let x := routeBUFrequency rho r t ^ 2 *
    routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t)
  have hbase : routeBModulusEnvelope routeBKappa routeBTheta rho r t ≤
      Real.exp (-x) := routeBModulusEnvelope_le_largeN_exp hrho hr ht
  have hpow := pow_le_pow_left₀
    (routeBModulusEnvelope_nonneg routeBKappa routeBTheta rho r t) hbase n
  unfold routeBPowerModulusEnvelope routeBLargeNQ
  rw [← Real.exp_nat_mul] at hpow
  convert hpow using 1 <;> dsimp only [x] <;> ring

theorem routeBPowerModulusEnvelope_le_largeQ_exp
    {n : ℕ} {rho r t : ℝ}
    (hn : 0 < n) (hrho : 0 < rho) (hr : 0 < r) (ht : 0 ≤ t) :
    routeBPowerModulusEnvelope routeBKappa routeBTheta n rho r t ≤
      Real.exp (-routeBLargeQ (routeBSmoothingScale n rho) r t) := by
  rw [← routeBLargeNQ_eq_routeBLargeQ hn hrho hr]
  exact routeBPowerModulusEnvelope_le_largeN_exp hrho hr ht

theorem routeBMaxEnvelope_pow_le_largeN_exp
    {n : ℕ} (hn : 100 ≤ n) {rho r t : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) (ht : 0 ≤ t) :
    max (routeBModulusEnvelope routeBKappa routeBTheta rho r t)
          (routeBGaussianEnvelope rho r t) ^ (n - 1) ≤
      Real.exp (-routeBLargeNAlpha * routeBLargeNQ n rho r t) := by
  let x := routeBUFrequency rho r t ^ 2 *
    routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t)
  have hx : 0 ≤ x := mul_nonneg (sq_nonneg _) (routeBLargeN_minorant_nonneg ht)
  have hA : routeBModulusEnvelope routeBKappa routeBTheta rho r t ≤
      Real.exp (-x) := routeBModulusEnvelope_le_largeN_exp hrho hr ht
  have hB : routeBGaussianEnvelope rho r t ≤ Real.exp (-x) :=
    routeBGaussianEnvelope_le_largeN_exp hrho hr ht
  have hmax : max (routeBModulusEnvelope routeBKappa routeBTheta rho r t)
      (routeBGaussianEnvelope rho r t) ≤ Real.exp (-x) := max_le hA hB
  have hpow := pow_le_pow_left₀
    ((routeBModulusEnvelope_nonneg routeBKappa routeBTheta rho r t).trans
      (le_max_left _ _))
    hmax (n - 1)
  have hcoefficient := routeBLargeNAlpha_mul_nat_le_sub_one hn
  have hexponent : ((n - 1 : ℕ) : ℝ) * (-x) ≤
      -routeBLargeNAlpha * ((n : ℝ) * x) := by
    nlinarith [mul_le_mul_of_nonneg_right hcoefficient hx]
  calc
    max (routeBModulusEnvelope routeBKappa routeBTheta rho r t)
          (routeBGaussianEnvelope rho r t) ^ (n - 1) ≤
        Real.exp (-x) ^ (n - 1) := hpow
    _ = Real.exp (((n - 1 : ℕ) : ℝ) * (-x)) := by
      rw [Real.exp_nat_mul]
    _ ≤ Real.exp (-routeBLargeNAlpha * ((n : ℝ) * x)) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp (-routeBLargeNAlpha * routeBLargeNQ n rho r t) := by
      simp only [routeBLargeNQ, x]
      ring

theorem routeBMaxEnvelope_pow_le_largeQ_exp
    {n : ℕ} (hn : 100 ≤ n) {rho r t : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) (ht : 0 ≤ t) :
    max (routeBModulusEnvelope routeBKappa routeBTheta rho r t)
          (routeBGaussianEnvelope rho r t) ^ (n - 1) ≤
      Real.exp (-routeBLargeNAlpha *
        routeBLargeQ (routeBSmoothingScale n rho) r t) := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  rw [← routeBLargeNQ_eq_routeBLargeQ hnPos hrho hr]
  exact routeBMaxEnvelope_pow_le_largeN_exp hn hrho hr ht

end

end BerryEsseen
