import BerryEsseen.Analysis.VariableExponent
import BerryEsseen.Smoothing.LargeSampleComparison

/-!
# Smoothing / Variable Exponent Comparison
-/

namespace BerryEsseen

noncomputable section

lemma max_pow_le_variable_rate_exp
    {n : ℕ} (hn : 100 ≤ n) {rho A u : ℝ}
    (hrho : 1 ≤ rho) (hA0 : 0 ≤ A)
    (hA : A ≤ Real.exp (-((39 / 100 : ℝ) * u ^ 2))) :
    (max A (Real.exp (-(u ^ 2 / 2)))) ^ (n - 1) ≤
      Real.exp
        (-largeVariableAlphaReal (routeBSmoothingScale n rho) *
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
  have hcoefficient :=
    largeVariableAlpha_mul_nat_le_sub_one hn hrho
  have hexponent : ((n - 1 : ℕ) : ℝ) * (-x) ≤
      -largeVariableAlphaReal (routeBSmoothingScale n rho) *
        ((n : ℝ) * x) := by
    nlinarith [mul_le_mul_of_nonneg_right hcoefficient hx]
  calc
    (max A (Real.exp (-(u ^ 2 / 2)))) ^ (n - 1) ≤
        Real.exp (-x) ^ (n - 1) := hpow
    _ = Real.exp (((n - 1 : ℕ) : ℝ) * (-x)) := by
      rw [Real.exp_nat_mul]
    _ ≤ Real.exp
        (-largeVariableAlphaReal (routeBSmoothingScale n rho) *
          ((n : ℝ) * x)) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp
        (-largeVariableAlphaReal (routeBSmoothingScale n rho) *
          ((n : ℝ) * ((39 / 100 : ℝ) * u ^ 2))) := by
      simp only [x]

lemma scalarMaxPower_le_large_old_variable_exp
    {n : ℕ} (hn : 100 ≤ n) {rho r t : ℝ}
    (hrho : 1 ≤ rho) (hr : 1 ≤ r) (ht0 : 0 ≤ t) :
    max (scalarModulus rho (rho * (r - 1)) t)
          (scalarNormalOne rho (rho * (r - 1)) t) ^ (n - 1) ≤
      Real.exp
        (-largeVariableAlphaReal (routeBSmoothingScale n rho) *
          routeBLargeQ (routeBSmoothingScale n rho) r t) := by
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hrPos : 0 < r := zero_lt_one.trans_le hr
  have hrouteR : routeBDboundR rho (rho * (r - 1)) = r := by
    simpa using routeBDboundR_mul_excess hrhoPos.ne'
  have hF : scalarModulus rho (rho * (r - 1)) t ≤
      routeBModulusEnvelope routeBKappa routeBTheta rho r t := by
    simpa only [hrouteR] using
      scalarModulus_le_routeB rho (rho * (r - 1)) t
  have hB : scalarNormalOne rho (rho * (r - 1)) t =
      routeBGaussianEnvelope rho r t := by
    simp only [scalarNormalOne, hrouteR]
  have hbase :
      max (scalarModulus rho (rho * (r - 1)) t)
          (scalarNormalOne rho (rho * (r - 1)) t) ≤
        max (routeBModulusEnvelope routeBKappa routeBTheta rho r t)
          (routeBGaussianEnvelope rho r t) := by
    rw [hB]
    exact max_le_max hF le_rfl
  have hbase0 : 0 ≤
      max (scalarModulus rho (rho * (r - 1)) t)
        (scalarNormalOne rho (rho * (r - 1)) t) :=
    (scalarModulus_nonneg rho (rho * (r - 1)) t).trans
      (le_max_left _ _)
  have hpow := pow_le_pow_left₀ hbase0 hbase (n - 1)
  exact hpow.trans <|
    routeBMaxEnvelope_pow_le_variableAlpha_largeQ_exp
      hn hrho hrPos ht0

lemma scalarMaxPower_le_large_rate_variable_exp
    {n : ℕ} (hn : 100 ≤ n) {rho r t : ℝ}
    (hrho : 1 ≤ rho) (hr : 19 / 10 ≤ r)
    (hfeasible : rho * (r - 1) ≤ 1)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) :
    max (scalarModulus rho (rho * (r - 1)) t)
          (scalarNormalOne rho (rho * (r - 1)) t) ^ (n - 1) ≤
      Real.exp
        (-largeVariableAlphaReal (routeBSmoothingScale n rho) *
          largeDirectRateQReal (routeBSmoothingScale n rho) r t) := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hrPos : 0 < r := by norm_num at hr ⊢; linarith
  have hrouteR : routeBDboundR rho (rho * (r - 1)) = r := by
    simpa using routeBDboundR_mul_excess hrhoPos.ne'
  have hF := scalarModulus_le_large_rate hrho hr hfeasible ht0 ht
  have hpow := max_pow_le_variable_rate_exp hn hrho
    (scalarModulus_nonneg rho (rho * (r - 1)) t) hF
  rw [rate_frequency_eq_direct hnPos hrhoPos hrPos] at hpow
  simpa only [scalarNormalOne, routeBGaussianEnvelope,
    scalarU, hrouteR, neg_div] using hpow

theorem scalarMaxPower_le_large_strong_variable_exp
    {n : ℕ} (hn : 100 ≤ n) {rho r t : ℝ}
    (hrho : 1 ≤ rho) (hr : 19 / 10 ≤ r)
    (hfeasible : rho * (r - 1) ≤ 1) (ht0 : 0 ≤ t) :
    max (scalarModulus rho (rho * (r - 1)) t)
          (scalarNormalOne rho (rho * (r - 1)) t) ^ (n - 1) ≤
      Real.exp
        (-largeVariableAlphaReal (routeBSmoothingScale n rho) *
          largeDirectStrongQReal
            (routeBSmoothingScale n rho) r t) := by
  have hrOne : 1 ≤ r := by norm_num at hr ⊢; linarith
  have hold := scalarMaxPower_le_large_old_variable_exp
    hn hrho hrOne ht0
  by_cases htQuarter : t ≤ 1 / 4
  · have hrate := scalarMaxPower_le_large_rate_variable_exp
      hn hrho hr hfeasible ht0 htQuarter
    unfold largeDirectStrongQReal
    rw [if_pos htQuarter]
    rcases le_total
        (routeBLargeQ (routeBSmoothingScale n rho) r t)
        (largeDirectRateQReal (routeBSmoothingScale n rho) r t) with
      hle | hge
    · rw [max_eq_right hle]
      exact hrate
    · rw [max_eq_left hge]
      exact hold
  · unfold largeDirectStrongQReal
    rw [if_neg htQuarter]
    exact hold

end

end BerryEsseen
