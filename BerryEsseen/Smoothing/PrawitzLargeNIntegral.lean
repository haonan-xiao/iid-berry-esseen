import BerryEsseen.Smoothing.PrawitzLargeNDisk
import BerryEsseen.Smoothing.PrawitzFiniteCell
/-!
# Direct large-`n` Route B integral envelopes

This module formalizes the real pointwise envelope in equation (15) of the
numerical-lemma supplement.  It rewrites the finite-`n` Route B terms through
`L = rho / sqrt n`, replaces their powers by the uniform exponential bounds,
and replaces the one-step disk radius by `routeBDiskStar`.
-/

namespace BerryEsseen

noncomputable section

/-- The exact Gaussian power after the `L = rho / sqrt n` rewrite. -/
def routeBLargeNormalEnvelope (L r t : ℝ) : ℝ :=
  Real.exp (-((2 * Real.pi * t) ^ 2 / (2 * r ^ 2 * L ^ 2)))

/-- Equation (15), the large-`n` envelope for the characteristic-function
power difference. -/
def routeBLargeDifferenceEnvelope (L r t : ℝ) : ℝ :=
  min
    (((2 * Real.pi * t) ^ 3 / (r ^ 3 * L ^ 2)) *
      routeBDiskStar r (2 * Real.pi * t / r) *
      Real.exp (-routeBLargeNAlpha * routeBLargeQ L r t))
    (Real.exp (-routeBLargeQ L r t) +
      routeBLargeNormalEnvelope L r t)

def routeBLargeLowerDifferenceIntegrand (L r t : ℝ) : ℝ :=
  2 / L * ‖prawitzKernel t‖ * routeBLargeDifferenceEnvelope L r t

def routeBLargeCorrectionIntegrand (L r t : ℝ) : ℝ :=
  2 / L * ‖prawitzKernelCorrection t‖ *
    routeBLargeNormalEnvelope L r t

def routeBLargeHighIntegrand (L r t : ℝ) : ℝ :=
  2 / L * ‖prawitzKernel t‖ * Real.exp (-routeBLargeQ L r t)

lemma routeBLargeNormalEnvelope_nonneg (L r t : ℝ) :
    0 ≤ routeBLargeNormalEnvelope L r t := by
  exact (Real.exp_pos _).le

lemma routeBLargeDifferenceEnvelope_nonneg
    {L r t : ℝ} (hL : 0 < L) (hr : 0 < r) (ht : 0 ≤ t) :
    0 ≤ routeBLargeDifferenceEnvelope L r t := by
  unfold routeBLargeDifferenceEnvelope
  apply le_min
  · have hcoefficient :
        0 ≤ (2 * Real.pi * t) ^ 3 / (r ^ 3 * L ^ 2) := by
      exact div_nonneg
        (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) ht) 3)
        (mul_nonneg (pow_nonneg hr.le 3) (sq_nonneg L))
    exact mul_nonneg
      (mul_nonneg hcoefficient (routeBDiskStar_nonneg r (2 * Real.pi * t / r)))
      (Real.exp_pos _).le
  · exact add_nonneg (Real.exp_pos _).le
      (routeBLargeNormalEnvelope_nonneg L r t)

lemma routeBPowerGaussianEnvelope_eq_largeNormal
    {n : ℕ} {rho r t : ℝ}
    (hn : 0 < n) (hrho : 0 < rho) (hr : 0 < r) :
    routeBPowerGaussianEnvelope n rho r t =
      routeBLargeNormalEnvelope (routeBSmoothingScale n rho) r t := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  unfold routeBPowerGaussianEnvelope routeBGaussianEnvelope
  rw [← Real.exp_nat_mul]
  unfold routeBLargeNormalEnvelope routeBUFrequency routeBSmoothingScale
  congr 1
  field_simp [hrho.ne', hr.ne', hsqrt.ne']
  rw [Real.sq_sqrt hnReal.le]
  ring

lemma routeBLarge_coefficient_identity
    {n : ℕ} {rho r t : ℝ}
    (hn : 0 < n) (hrho : 0 < rho) (hr : 0 < r) :
    (n : ℝ) * rho * routeBUFrequency rho r t ^ 3 =
      (2 * Real.pi * t) ^ 3 /
        (r ^ 3 * routeBSmoothingScale n rho ^ 2) := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  unfold routeBUFrequency routeBSmoothingScale
  field_simp [hrho.ne', hr.ne', hsqrt.ne']
  rw [Real.sq_sqrt hnReal.le]
  ring

/-- Pointwise form of equation (15). -/
theorem routeBPowerDifferenceEnvelope_le_largeDifference
    {n : ℕ} (hn : 100 ≤ n) {rho r t : ℝ}
    (hrho1 : 1 ≤ rho) (hr1 : 1 ≤ r) (ht : 0 ≤ t) :
    routeBPowerDifferenceEnvelope routeBKappa routeBTheta n rho r t ≤
      routeBLargeDifferenceEnvelope (routeBSmoothingScale n rho) r t := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  have hrPos : 0 < r := zero_lt_one.trans_le hr1
  let L := routeBSmoothingScale n rho
  let c := 2 * Real.pi * t / r
  have hL : 0 < L := routeBSmoothingScale_pos hnPos hrhoPos
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hD : routeBDiskBound routeBKappa rho r c ≤
      routeBDiskStar r c := routeBDiskBound_le_diskStar hrho1 hr1 hc0
  have hH := routeBMaxEnvelope_pow_le_largeQ_exp
    hn hrhoPos hrPos ht
  have hM := routeBPowerModulusEnvelope_le_largeQ_exp
    hnPos hrhoPos hrPos ht
  have hN := routeBPowerGaussianEnvelope_eq_largeNormal
    (n := n) (rho := rho) (r := r) (t := t) hnPos hrhoPos hrPos
  have hcoefficient := routeBLarge_coefficient_identity
    (n := n) (rho := rho) (r := r) (t := t) hnPos hrhoPos hrPos
  unfold routeBPowerDifferenceEnvelope routeBLargeDifferenceEnvelope
  dsimp only
  apply min_le_min
  · rw [hcoefficient]
    change
      ((2 * Real.pi * t) ^ 3 / (r ^ 3 * L ^ 2)) *
          routeBDiskBound routeBKappa rho r c *
          max (routeBModulusEnvelope routeBKappa routeBTheta rho r t)
            (routeBGaussianEnvelope rho r t) ^ (n - 1) ≤
        ((2 * Real.pi * t) ^ 3 / (r ^ 3 * L ^ 2)) *
          routeBDiskStar r c *
          Real.exp (-routeBLargeNAlpha * routeBLargeQ L r t)
    have hcoeff0 :
        0 ≤ (2 * Real.pi * t) ^ 3 / (r ^ 3 * L ^ 2) := by
      exact div_nonneg
        (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) ht) 3)
        (mul_nonneg (pow_nonneg hrPos.le 3) (sq_nonneg L))
    have hDstar0 : 0 ≤ routeBDiskStar r c := routeBDiskStar_nonneg r c
    have hmax0 :
        0 ≤ max (routeBModulusEnvelope routeBKappa routeBTheta rho r t)
          (routeBGaussianEnvelope rho r t) :=
      (routeBModulusEnvelope_nonneg routeBKappa routeBTheta rho r t).trans
        (le_max_left _ _)
    have hH0 :
        0 ≤ max (routeBModulusEnvelope routeBKappa routeBTheta rho r t)
            (routeBGaussianEnvelope rho r t) ^ (n - 1) :=
      pow_nonneg hmax0 _
    calc
      ((2 * Real.pi * t) ^ 3 / (r ^ 3 * L ^ 2)) *
            routeBDiskBound routeBKappa rho r c *
            max (routeBModulusEnvelope routeBKappa routeBTheta rho r t)
              (routeBGaussianEnvelope rho r t) ^ (n - 1) ≤
          ((2 * Real.pi * t) ^ 3 / (r ^ 3 * L ^ 2)) *
            routeBDiskStar r c *
            max (routeBModulusEnvelope routeBKappa routeBTheta rho r t)
              (routeBGaussianEnvelope rho r t) ^ (n - 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hD hcoeff0) hH0
      _ ≤ ((2 * Real.pi * t) ^ 3 / (r ^ 3 * L ^ 2)) *
            routeBDiskStar r c *
            Real.exp (-routeBLargeNAlpha * routeBLargeQ L r t) := by
        exact mul_le_mul_of_nonneg_left hH
          (mul_nonneg hcoeff0 hDstar0)
  · rw [hN]
    exact add_le_add hM le_rfl

theorem routeBNormalizedLowerDifference_le_largeIntegrand
    {n : ℕ} (hn : 100 ≤ n) {rho r t : ℝ}
    (hrho1 : 1 ≤ rho) (hr1 : 1 ≤ r) (ht : 0 ≤ t) :
    2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖ *
        routeBPowerDifferenceEnvelope routeBKappa routeBTheta n rho r t ≤
      routeBLargeLowerDifferenceIntegrand
        (routeBSmoothingScale n rho) r t := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  have hL : 0 < routeBSmoothingScale n rho :=
    routeBSmoothingScale_pos hnPos hrhoPos
  have hdiff := routeBPowerDifferenceEnvelope_le_largeDifference
    hn hrho1 hr1 ht
  have hscale :
      2 * Real.sqrt (n : ℝ) / rho = 2 / routeBSmoothingScale n rho := by
    unfold routeBSmoothingScale
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
    field_simp [hrhoPos.ne', hsqrt.ne']
  rw [hscale]
  unfold routeBLargeLowerDifferenceIntegrand
  have hfactor :
      0 ≤ 2 / routeBSmoothingScale n rho * ‖prawitzKernel t‖ :=
    mul_nonneg (div_nonneg (by norm_num) hL.le) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left hdiff hfactor

theorem routeBNormalizedCorrection_le_largeIntegrand
    {n : ℕ} (hn : 100 ≤ n) {rho r t : ℝ}
    (hrho1 : 1 ≤ rho) (hr1 : 1 ≤ r) :
    2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernelCorrection t‖ *
        routeBPowerGaussianEnvelope n rho r t ≤
      routeBLargeCorrectionIntegrand
        (routeBSmoothingScale n rho) r t := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  have hrPos : 0 < r := zero_lt_one.trans_le hr1
  have hN := routeBPowerGaussianEnvelope_eq_largeNormal
    (n := n) (rho := rho) (r := r) (t := t) hnPos hrhoPos hrPos
  have hscale :
      2 * Real.sqrt (n : ℝ) / rho = 2 / routeBSmoothingScale n rho := by
    unfold routeBSmoothingScale
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
    field_simp [hrhoPos.ne', hsqrt.ne']
  rw [hscale, hN]
  rfl

theorem routeBNormalizedHigh_le_largeIntegrand
    {n : ℕ} (hn : 100 ≤ n) {rho r t : ℝ}
    (hrho1 : 1 ≤ rho) (hr1 : 1 ≤ r) (ht : 0 ≤ t) :
    2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖ *
        routeBPowerModulusEnvelope routeBKappa routeBTheta n rho r t ≤
      routeBLargeHighIntegrand (routeBSmoothingScale n rho) r t := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  have hrPos : 0 < r := zero_lt_one.trans_le hr1
  have hM := routeBPowerModulusEnvelope_le_largeQ_exp
    hnPos hrhoPos hrPos ht
  have hscale :
      2 * Real.sqrt (n : ℝ) / rho = 2 / routeBSmoothingScale n rho := by
    unfold routeBSmoothingScale
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
    field_simp [hrhoPos.ne', hsqrt.ne']
  rw [hscale]
  unfold routeBLargeHighIntegrand
  have hL : 0 < routeBSmoothingScale n rho :=
    routeBSmoothingScale_pos hnPos hrhoPos
  have hfactor :
      0 ≤ 2 / routeBSmoothingScale n rho * ‖prawitzKernel t‖ :=
    mul_nonneg (div_nonneg (by norm_num) hL.le) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left hM
    hfactor

end

end BerryEsseen
