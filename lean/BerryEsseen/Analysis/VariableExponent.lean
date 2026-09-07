import BerryEsseen.Smoothing.Prawitz.LargeN

/-!
# Analysis / Variable Exponent
-/

namespace BerryEsseen

noncomputable section

def largeVariableAlphaReal (L : ℝ) : ℝ :=
  max routeBLargeNAlpha (1 - L ^ 2)

lemma largeVariableAlphaReal_nonneg (L : ℝ) :
    0 ≤ largeVariableAlphaReal L :=
  routeBLargeNAlpha_nonneg.trans (le_max_left _ _)

lemma routeBSmoothingScale_sq_mul_nat
    {n : ℕ} (hn : 0 < n) (rho : ℝ) :
    routeBSmoothingScale n rho ^ 2 * (n : ℝ) = rho ^ 2 := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold routeBSmoothingScale
  rw [div_pow, Real.sq_sqrt hnReal.le]
  field_simp [hnReal.ne']

lemma largeVariableAlpha_mul_nat_le_sub_one
    {n : ℕ} (hn : 100 ≤ n) {rho : ℝ} (hrho : 1 ≤ rho) :
    largeVariableAlphaReal (routeBSmoothingScale n rho) * (n : ℝ) ≤
      ((n - 1 : ℕ) : ℝ) := by
  have hnOne : 1 ≤ n := by omega
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hfixed := routeBLargeNAlpha_mul_nat_le_sub_one hn
  have hscale := routeBSmoothingScale_sq_mul_nat hnPos rho
  have hrhoSq : 1 ≤ rho ^ 2 := by nlinarith
  have hvariable :
      (1 - routeBSmoothingScale n rho ^ 2) * (n : ℝ) ≤
        ((n - 1 : ℕ) : ℝ) := by
    calc
      (1 - routeBSmoothingScale n rho ^ 2) * (n : ℝ) =
          (n : ℝ) - routeBSmoothingScale n rho ^ 2 * (n : ℝ) := by ring
      _ = (n : ℝ) - rho ^ 2 := by rw [hscale]
      _ ≤ (n : ℝ) - 1 := sub_le_sub_left hrhoSq (n : ℝ)
      _ = ((n - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hnOne]
        norm_num
  unfold largeVariableAlphaReal
  by_cases hbranch : routeBLargeNAlpha ≤
      1 - routeBSmoothingScale n rho ^ 2
  · rw [max_eq_right hbranch]
    exact hvariable
  · rw [max_eq_left (le_of_not_ge hbranch)]
    exact hfixed

theorem routeBMaxEnvelope_pow_le_variableAlpha_largeN_exp
    {n : ℕ} (hn : 100 ≤ n) {rho r t : ℝ}
    (hrho1 : 1 ≤ rho) (hr : 0 < r) (ht : 0 ≤ t) :
    max (routeBModulusEnvelope routeBKappa routeBTheta rho r t)
          (routeBGaussianEnvelope rho r t) ^ (n - 1) ≤
      Real.exp
        (-largeVariableAlphaReal (routeBSmoothingScale n rho) *
          routeBLargeNQ n rho r t) := by
  have hrho : 0 < rho := zero_lt_one.trans_le hrho1
  let x := routeBUFrequency rho r t ^ 2 *
    routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t)
  have hx : 0 ≤ x :=
    mul_nonneg (sq_nonneg _) (routeBLargeN_minorant_nonneg ht)
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
  have hcoefficient :=
    largeVariableAlpha_mul_nat_le_sub_one hn hrho1
  have hexponent : ((n - 1 : ℕ) : ℝ) * (-x) ≤
      -largeVariableAlphaReal (routeBSmoothingScale n rho) *
        ((n : ℝ) * x) := by
    nlinarith [mul_le_mul_of_nonneg_right hcoefficient hx]
  calc
    max (routeBModulusEnvelope routeBKappa routeBTheta rho r t)
          (routeBGaussianEnvelope rho r t) ^ (n - 1) ≤
        Real.exp (-x) ^ (n - 1) := hpow
    _ = Real.exp (((n - 1 : ℕ) : ℝ) * (-x)) := by
      rw [Real.exp_nat_mul]
    _ ≤ Real.exp
        (-largeVariableAlphaReal (routeBSmoothingScale n rho) *
          ((n : ℝ) * x)) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp
        (-largeVariableAlphaReal (routeBSmoothingScale n rho) *
          routeBLargeNQ n rho r t) := by
      simp only [routeBLargeNQ, x]
      ring

theorem routeBMaxEnvelope_pow_le_variableAlpha_largeQ_exp
    {n : ℕ} (hn : 100 ≤ n) {rho r t : ℝ}
    (hrho1 : 1 ≤ rho) (hr : 0 < r) (ht : 0 ≤ t) :
    max (routeBModulusEnvelope routeBKappa routeBTheta rho r t)
          (routeBGaussianEnvelope rho r t) ^ (n - 1) ≤
      Real.exp
        (-largeVariableAlphaReal (routeBSmoothingScale n rho) *
          routeBLargeQ (routeBSmoothingScale n rho) r t) := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrho : 0 < rho := zero_lt_one.trans_le hrho1
  rw [← routeBLargeNQ_eq_routeBLargeQ hnPos hrho hr]
  exact routeBMaxEnvelope_pow_le_variableAlpha_largeN_exp
    hn hrho1 hr ht

end

end BerryEsseen
