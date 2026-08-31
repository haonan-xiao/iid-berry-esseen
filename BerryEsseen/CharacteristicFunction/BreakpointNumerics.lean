import BerryEsseen.CharacteristicFunction.BreakpointCertificate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Exact numerical bounds for the Route B breakpoint

This module supplies a small axiom-clean numerical kernel for sine and cosine
on `[0, 1]`: even and odd alternating Taylor partial sums give exact rational
lower and upper bounds.  It then combines those bounds with Mathlib's rational
enclosure of `π` and the analytic results in `BreakpointCertificate.lean` to
prove the tight enclosures used by the supplied Route B numerical verifier:

* `3.99589567 < routeBTheta < 3.99589570`;
* `0.09916191350 < routeBKappa < 0.09916191353`.

All decimal literals in this file elaborate to exact rationals.  The finite
Taylor sums are discharged by `norm_num`; no floating-point evaluation enters
the theorem dependency graph.
-/

open Finset

namespace BerryEsseen

noncomputable section

def cosMagnitude (x : ℝ) (n : ℕ) : ℝ := x ^ (2 * n) / (2 * n).factorial

def sinMagnitude (x : ℝ) (n : ℕ) : ℝ := x ^ (2 * n + 1) / (2 * n + 1).factorial

def alternatingPartial (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, (-1 : ℝ) ^ i * f i

theorem cosMagnitude_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (cosMagnitude x) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold cosMagnitude
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [pow_add]
  have hpow : x ^ 2 ≤ 1 := by nlinarith
  have hfac : (0 : ℝ) < (2 * n).factorial := by positivity
  have h1 : (1 : ℝ) ≤ 2 * n + 1 := by exact_mod_cast (by omega : 1 ≤ 2 * n + 1)
  have h2 : (1 : ℝ) ≤ 2 * n + 2 := by exact_mod_cast (by omega : 1 ≤ 2 * n + 2)
  have hden : x ^ 2 ≤ (2 * n + 1 : ℝ) * (2 * n + 2 : ℝ) := by
    refine hpow.trans ?_
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  have hbase : 0 ≤ x ^ (2 * n) * ((2 * n).factorial : ℝ) :=
    mul_nonneg (pow_nonneg hx0 _) hfac.le
  rw [div_le_div_iff₀]
  · calc
      x ^ (2 * n + 1) * x ^ 1 * ((2 * n).factorial : ℝ) =
          (x ^ (2 * n) * ((2 * n).factorial : ℝ)) * x ^ 2 := by
            rw [show 2 * n + 1 = (2 * n) + 1 by omega, pow_succ]
            ring
      _ ≤ (x ^ (2 * n) * ((2 * n).factorial : ℝ)) *
          ((2 * n + 1 : ℝ) * (2 * n + 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hden hbase
      _ = x ^ (2 * n) *
          ((2 * (n : ℝ) + 1 + 1) *
            ((2 * (n : ℝ) + 1) * ((2 * n).factorial : ℝ))) := by ring
  · positivity
  · positivity

theorem sinMagnitude_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (sinMagnitude x) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold sinMagnitude
  rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 by omega]
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [show 2 * n + 3 = (2 * n + 1) + 2 by omega, pow_add]
  have hpow : x ^ 2 ≤ 1 := by nlinarith
  have hfac : (0 : ℝ) < (2 * n + 1).factorial := by positivity
  have h1 : (1 : ℝ) ≤ 2 * n + 2 := by exact_mod_cast (by omega : 1 ≤ 2 * n + 2)
  have h2 : (1 : ℝ) ≤ 2 * n + 3 := by exact_mod_cast (by omega : 1 ≤ 2 * n + 3)
  have hden : x ^ 2 ≤ (2 * n + 2 : ℝ) * (2 * n + 3 : ℝ) := by
    refine hpow.trans ?_
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  have hbase : 0 ≤ x ^ (2 * n + 1) * ((2 * n + 1).factorial : ℝ) :=
    mul_nonneg (pow_nonneg hx0 _) hfac.le
  rw [div_le_div_iff₀]
  · calc
      x ^ (2 * n + 1) * x ^ 2 * ((2 * n + 1).factorial : ℝ) =
          (x ^ (2 * n + 1) * ((2 * n + 1).factorial : ℝ)) * x ^ 2 := by ring
      _ ≤ (x ^ (2 * n + 1) * ((2 * n + 1).factorial : ℝ)) *
          ((2 * n + 2 : ℝ) * (2 * n + 3 : ℝ)) :=
            mul_le_mul_of_nonneg_left hden hbase
      _ = x ^ (2 * n + 1) *
          ((2 * (n : ℝ) + 2 + 1) *
            ((2 * (n : ℝ) + 1 + 1) * ((2 * n + 1).factorial : ℝ))) := by ring
  · positivity
  · positivity

theorem cos_lower_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    alternatingPartial (cosMagnitude x) (2 * k) ≤ Real.cos x := by
  have hsum : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * cosMagnitude x n) (Real.cos x) := by
    simpa only [cosMagnitude, mul_div_assoc] using Real.hasSum_cos x
  exact (cosMagnitude_antitone hx0 hx1).alternating_series_le_tendsto
    hsum.tendsto_sum_nat k

theorem cos_upper_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    Real.cos x ≤ alternatingPartial (cosMagnitude x) (2 * k + 1) := by
  have hsum : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * cosMagnitude x n) (Real.cos x) := by
    simpa only [cosMagnitude, mul_div_assoc] using Real.hasSum_cos x
  exact (cosMagnitude_antitone hx0 hx1).tendsto_le_alternating_series
    hsum.tendsto_sum_nat k

theorem sin_lower_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    alternatingPartial (sinMagnitude x) (2 * k) ≤ Real.sin x := by
  have hsum : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * sinMagnitude x n) (Real.sin x) := by
    simpa only [sinMagnitude, mul_div_assoc] using Real.hasSum_sin x
  exact (sinMagnitude_antitone hx0 hx1).alternating_series_le_tendsto
    hsum.tendsto_sum_nat k

theorem sin_upper_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    Real.sin x ≤ alternatingPartial (sinMagnitude x) (2 * k + 1) := by
  have hsum : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * sinMagnitude x n) (Real.sin x) := by
    simpa only [sinMagnitude, mul_div_assoc] using Real.hasSum_sin x
  exact (sinMagnitude_antitone hx0 hx1).tendsto_le_alternating_series
    hsum.tendsto_sum_nat k

def routeBThetaLower : ℝ := 3.99589567

def routeBThetaUpper : ℝ := 3.99589570

def piLower20 : ℝ := 3.14159265358979323846

def piUpper20 : ℝ := 3.14159265358979323847

theorem routeBF_thetaLower_pos : 0 < routeBF routeBThetaLower := by
  let yLower := routeBThetaLower - piUpper20
  let yUpper := routeBThetaLower - piLower20
  have hpiLower : piLower20 < Real.pi := by
    exact Real.pi_gt_d20
  have hpiUpper : Real.pi < piUpper20 := by
    exact Real.pi_lt_d20
  have hyLower0 : 0 ≤ yLower := by
    norm_num [yLower, routeBThetaLower, piUpper20]
  have hyLower1 : yLower ≤ 1 := by
    norm_num [yLower, routeBThetaLower, piUpper20]
  have hyUpper0 : 0 ≤ yUpper := by
    norm_num [yUpper, routeBThetaLower, piLower20]
  have hyUpper1 : yUpper ≤ 1 := by
    norm_num [yUpper, routeBThetaLower, piLower20]
  have hyActualLower : yLower ≤ routeBThetaLower - Real.pi := by
    dsimp only [yLower]
    linarith
  have hyActualUpper : routeBThetaLower - Real.pi ≤ yUpper := by
    dsimp only [yUpper]
    linarith
  have hyActualMemSin : routeBThetaLower - Real.pi ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · norm_num [routeBThetaLower]
      linarith [Real.pi_lt_four]
    · norm_num [routeBThetaLower]
      nlinarith [Real.pi_gt_three]
  have hyLowerMemSin : yLower ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith [hyLower0, Real.pi_pos]
    · norm_num [yLower, routeBThetaLower, piUpper20]
      nlinarith [Real.pi_gt_three]
  have hyActualMemCos : routeBThetaLower - Real.pi ∈ Set.Icc 0 Real.pi := by
    constructor
    · exact hyActualLower.trans' hyLower0
    · norm_num [routeBThetaLower]
      nlinarith [Real.pi_gt_three]
  have hyUpperMemCos : yUpper ∈ Set.Icc 0 Real.pi := by
    constructor
    · exact hyUpper0
    · norm_num [yUpper, routeBThetaLower, piLower20]
      nlinarith [Real.pi_gt_three]
  have hcosTaylor := cos_lower_bound hyUpper0 hyUpper1 6
  have hsinTaylor := sin_lower_bound hyLower0 hyLower1 6
  have hcos : alternatingPartial (cosMagnitude yUpper) 12 ≤
      Real.cos (routeBThetaLower - Real.pi) :=
    hcosTaylor.trans (Real.strictAntiOn_cos.antitoneOn hyActualMemCos hyUpperMemCos hyActualUpper)
  have hsin : alternatingPartial (sinMagnitude yLower) 12 ≤
      Real.sin (routeBThetaLower - Real.pi) :=
    hsinTaylor.trans (Real.monotoneOn_sin hyLowerMemSin hyActualMemSin hyActualLower)
  have hnumeric : 0 <
      3 * (1 + alternatingPartial (cosMagnitude yUpper) 12) +
        routeBThetaLower * alternatingPartial (sinMagnitude yLower) 12 -
          routeBThetaLower ^ 2 / 2 := by
    norm_num [alternatingPartial, cosMagnitude, sinMagnitude, Finset.sum_range_succ,
      yUpper, yLower, routeBThetaLower, piLower20, piUpper20]
  have hcosRewrite : Real.cos routeBThetaLower =
      -Real.cos (routeBThetaLower - Real.pi) := by
    rw [show routeBThetaLower = Real.pi + (routeBThetaLower - Real.pi) by ring,
      Real.cos_add]
    simp
  have hsinRewrite : Real.sin routeBThetaLower =
      -Real.sin (routeBThetaLower - Real.pi) := by
    rw [show routeBThetaLower = Real.pi + (routeBThetaLower - Real.pi) by ring,
      Real.sin_add]
    simp
  rw [routeBF, hcosRewrite, hsinRewrite]
  have htheta : 0 < routeBThetaLower := by norm_num [routeBThetaLower]
  nlinarith

theorem routeBF_thetaUpper_neg : routeBF routeBThetaUpper < 0 := by
  let yLower := routeBThetaUpper - piUpper20
  let yUpper := routeBThetaUpper - piLower20
  have hpiLower : piLower20 < Real.pi := by
    exact Real.pi_gt_d20
  have hpiUpper : Real.pi < piUpper20 := by
    exact Real.pi_lt_d20
  have hyLower0 : 0 ≤ yLower := by
    norm_num [yLower, routeBThetaUpper, piUpper20]
  have hyLower1 : yLower ≤ 1 := by
    norm_num [yLower, routeBThetaUpper, piUpper20]
  have hyUpper0 : 0 ≤ yUpper := by
    norm_num [yUpper, routeBThetaUpper, piLower20]
  have hyUpper1 : yUpper ≤ 1 := by
    norm_num [yUpper, routeBThetaUpper, piLower20]
  have hyActualLower : yLower ≤ routeBThetaUpper - Real.pi := by
    dsimp only [yLower]
    linarith
  have hyActualUpper : routeBThetaUpper - Real.pi ≤ yUpper := by
    dsimp only [yUpper]
    linarith
  have hyActualMemSin : routeBThetaUpper - Real.pi ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · norm_num [routeBThetaUpper]
      linarith [Real.pi_lt_four]
    · norm_num [routeBThetaUpper]
      nlinarith [Real.pi_gt_three]
  have hyUpperMemSin : yUpper ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith [hyUpper0, Real.pi_pos]
    · norm_num [yUpper, routeBThetaUpper, piLower20]
      nlinarith [Real.pi_gt_three]
  have hyActualMemCos : routeBThetaUpper - Real.pi ∈ Set.Icc 0 Real.pi := by
    constructor
    · exact hyActualLower.trans' hyLower0
    · norm_num [routeBThetaUpper]
      nlinarith [Real.pi_gt_three]
  have hyLowerMemCos : yLower ∈ Set.Icc 0 Real.pi := by
    constructor
    · exact hyLower0
    · norm_num [yLower, routeBThetaUpper, piUpper20]
      nlinarith [Real.pi_gt_three]
  have hcosTaylor := cos_upper_bound hyLower0 hyLower1 6
  have hsinTaylor := sin_upper_bound hyUpper0 hyUpper1 6
  have hcos : Real.cos (routeBThetaUpper - Real.pi) ≤
      alternatingPartial (cosMagnitude yLower) 13 :=
    (Real.strictAntiOn_cos.antitoneOn hyLowerMemCos hyActualMemCos hyActualLower).trans hcosTaylor
  have hsin : Real.sin (routeBThetaUpper - Real.pi) ≤
      alternatingPartial (sinMagnitude yUpper) 13 :=
    (Real.monotoneOn_sin hyActualMemSin hyUpperMemSin hyActualUpper).trans hsinTaylor
  have hnumeric :
      3 * (1 + alternatingPartial (cosMagnitude yLower) 13) +
        routeBThetaUpper * alternatingPartial (sinMagnitude yUpper) 13 -
          routeBThetaUpper ^ 2 / 2 < 0 := by
    norm_num [alternatingPartial, cosMagnitude, sinMagnitude, Finset.sum_range_succ,
      yUpper, yLower, routeBThetaUpper, piLower20, piUpper20]
  have hcosRewrite : Real.cos routeBThetaUpper =
      -Real.cos (routeBThetaUpper - Real.pi) := by
    rw [show routeBThetaUpper = Real.pi + (routeBThetaUpper - Real.pi) by ring,
      Real.cos_add]
    simp
  have hsinRewrite : Real.sin routeBThetaUpper =
      -Real.sin (routeBThetaUpper - Real.pi) := by
    rw [show routeBThetaUpper = Real.pi + (routeBThetaUpper - Real.pi) by ring,
      Real.sin_add]
    simp
  rw [routeBF, hcosRewrite, hsinRewrite]
  have htheta : 0 < routeBThetaUpper := by norm_num [routeBThetaUpper]
  nlinarith

theorem routeBTheta_gt_lower : routeBThetaLower < routeBTheta := by
  by_contra h
  have hle : routeBTheta ≤ routeBThetaLower := le_of_not_gt h
  rcases hle.eq_or_lt with heq | hlt
  · have hF := routeBF_thetaLower_pos
    rw [← heq, routeBF_routeBTheta] at hF
    exact lt_irrefl 0 hF
  · have hneg := routeBF_neg_of_theta_lt hlt
    linarith [routeBF_thetaLower_pos]

theorem routeBTheta_lt_upper : routeBTheta < routeBThetaUpper := by
  by_contra h
  have hle : routeBThetaUpper ≤ routeBTheta := le_of_not_gt h
  rcases hle.eq_or_lt with heq | hlt
  · have hF := routeBF_thetaUpper_neg
    rw [heq, routeBF_routeBTheta] at hF
    exact lt_irrefl 0 hF
  · have hpos := routeBF_pos_of_pos_of_lt_theta
      (by norm_num [routeBThetaUpper]) hlt
    linarith [routeBF_thetaUpper_neg]

def routeBKappaLower : ℝ := 0.09916191350

def routeBKappaUpper : ℝ := 0.09916191353

def routeBQuotientAtLowerUpper : ℝ := 0.099161913515

theorem routeBMaxQuotient_thetaLower_gt_kappaLower :
    routeBKappaLower < routeBMaxQuotient routeBThetaLower := by
  let yLower := routeBThetaLower - piUpper20
  have hpiUpper : Real.pi < piUpper20 := Real.pi_lt_d20
  have hyLower0 : 0 ≤ yLower := by
    norm_num [yLower, routeBThetaLower, piUpper20]
  have hyLower1 : yLower ≤ 1 := by
    norm_num [yLower, routeBThetaLower, piUpper20]
  have hyActualLower : yLower ≤ routeBThetaLower - Real.pi := by
    dsimp only [yLower]
    linarith
  have hyActualMemCos : routeBThetaLower - Real.pi ∈ Set.Icc 0 Real.pi := by
    constructor
    · linarith [hyLower0]
    · norm_num [routeBThetaLower]
      nlinarith [Real.pi_gt_three]
  have hyLowerMemCos : yLower ∈ Set.Icc 0 Real.pi := by
    constructor
    · exact hyLower0
    · norm_num [yLower, routeBThetaLower, piUpper20]
      nlinarith [Real.pi_gt_three]
  have hcosTaylor := cos_upper_bound hyLower0 hyLower1 6
  have hcos : Real.cos (routeBThetaLower - Real.pi) ≤
      alternatingPartial (cosMagnitude yLower) 13 :=
    (Real.strictAntiOn_cos.antitoneOn hyLowerMemCos hyActualMemCos hyActualLower).trans hcosTaylor
  have hnumeric : routeBKappaLower <
      (-alternatingPartial (cosMagnitude yLower) 13 - 1 +
          routeBThetaLower ^ 2 / 2) / routeBThetaLower ^ 3 := by
    norm_num [routeBKappaLower, alternatingPartial, cosMagnitude,
      Finset.sum_range_succ, yLower, routeBThetaLower, piUpper20]
  have hcosRewrite : Real.cos routeBThetaLower =
      -Real.cos (routeBThetaLower - Real.pi) := by
    rw [show routeBThetaLower = Real.pi + (routeBThetaLower - Real.pi) by ring,
      Real.cos_add]
    simp
  rw [routeBMaxQuotient, routeBG, hcosRewrite]
  have hden : 0 < routeBThetaLower ^ 3 := by norm_num [routeBThetaLower]
  rw [lt_div_iff₀ hden] at hnumeric ⊢
  nlinarith

theorem routeBMaxQuotient_thetaLower_lt_upper :
    routeBMaxQuotient routeBThetaLower < routeBQuotientAtLowerUpper := by
  let yUpper := routeBThetaLower - piLower20
  have hpiLower : piLower20 < Real.pi := Real.pi_gt_d20
  have hyUpper0 : 0 ≤ yUpper := by
    norm_num [yUpper, routeBThetaLower, piLower20]
  have hyUpper1 : yUpper ≤ 1 := by
    norm_num [yUpper, routeBThetaLower, piLower20]
  have hyActualUpper : routeBThetaLower - Real.pi ≤ yUpper := by
    dsimp only [yUpper]
    linarith
  have hyActualMemCos : routeBThetaLower - Real.pi ∈ Set.Icc 0 Real.pi := by
    constructor
    · have hpiUpper : Real.pi < piUpper20 := Real.pi_lt_d20
      norm_num [routeBThetaLower, piUpper20] at hpiUpper ⊢
      linarith
    · norm_num [routeBThetaLower]
      nlinarith [Real.pi_gt_three]
  have hyUpperMemCos : yUpper ∈ Set.Icc 0 Real.pi := by
    constructor
    · exact hyUpper0
    · norm_num [yUpper, routeBThetaLower, piLower20]
      nlinarith [Real.pi_gt_three]
  have hcosTaylor := cos_lower_bound hyUpper0 hyUpper1 6
  have hcos : alternatingPartial (cosMagnitude yUpper) 12 ≤
      Real.cos (routeBThetaLower - Real.pi) :=
    hcosTaylor.trans
      (Real.strictAntiOn_cos.antitoneOn hyActualMemCos hyUpperMemCos hyActualUpper)
  have hnumeric :
      (-alternatingPartial (cosMagnitude yUpper) 12 - 1 +
          routeBThetaLower ^ 2 / 2) / routeBThetaLower ^ 3 <
        routeBQuotientAtLowerUpper := by
    norm_num [routeBQuotientAtLowerUpper, alternatingPartial, cosMagnitude,
      Finset.sum_range_succ, yUpper, routeBThetaLower, piLower20]
  have hcosRewrite : Real.cos routeBThetaLower =
      -Real.cos (routeBThetaLower - Real.pi) := by
    rw [show routeBThetaLower = Real.pi + (routeBThetaLower - Real.pi) by ring,
      Real.cos_add]
    simp
  rw [routeBMaxQuotient, routeBG, hcosRewrite]
  have hden : 0 < routeBThetaLower ^ 3 := by norm_num [routeBThetaLower]
  rw [div_lt_iff₀ hden] at hnumeric ⊢
  nlinarith

theorem routeBF_thetaLower_lt_one_div_100 : routeBF routeBThetaLower < 1 / 100 := by
  let yLower := routeBThetaLower - piUpper20
  let yUpper := routeBThetaLower - piLower20
  have hpiLower : piLower20 < Real.pi := Real.pi_gt_d20
  have hpiUpper : Real.pi < piUpper20 := Real.pi_lt_d20
  have hyLower0 : 0 ≤ yLower := by
    norm_num [yLower, routeBThetaLower, piUpper20]
  have hyLower1 : yLower ≤ 1 := by
    norm_num [yLower, routeBThetaLower, piUpper20]
  have hyUpper0 : 0 ≤ yUpper := by
    norm_num [yUpper, routeBThetaLower, piLower20]
  have hyUpper1 : yUpper ≤ 1 := by
    norm_num [yUpper, routeBThetaLower, piLower20]
  have hyActualLower : yLower ≤ routeBThetaLower - Real.pi := by
    dsimp only [yLower]
    linarith
  have hyActualUpper : routeBThetaLower - Real.pi ≤ yUpper := by
    dsimp only [yUpper]
    linarith
  have hyActualMemSin : routeBThetaLower - Real.pi ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · norm_num [routeBThetaLower]
      linarith [Real.pi_lt_four]
    · norm_num [routeBThetaLower]
      nlinarith [Real.pi_gt_three]
  have hyUpperMemSin : yUpper ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith [hyUpper0, Real.pi_pos]
    · norm_num [yUpper, routeBThetaLower, piLower20]
      nlinarith [Real.pi_gt_three]
  have hyActualMemCos : routeBThetaLower - Real.pi ∈ Set.Icc 0 Real.pi := by
    constructor
    · exact hyActualLower.trans' hyLower0
    · norm_num [routeBThetaLower]
      nlinarith [Real.pi_gt_three]
  have hyLowerMemCos : yLower ∈ Set.Icc 0 Real.pi := by
    constructor
    · exact hyLower0
    · norm_num [yLower, routeBThetaLower, piUpper20]
      nlinarith [Real.pi_gt_three]
  have hcosTaylor := cos_upper_bound hyLower0 hyLower1 6
  have hsinTaylor := sin_upper_bound hyUpper0 hyUpper1 6
  have hcos : Real.cos (routeBThetaLower - Real.pi) ≤
      alternatingPartial (cosMagnitude yLower) 13 :=
    (Real.strictAntiOn_cos.antitoneOn hyLowerMemCos hyActualMemCos hyActualLower).trans hcosTaylor
  have hsin : Real.sin (routeBThetaLower - Real.pi) ≤
      alternatingPartial (sinMagnitude yUpper) 13 :=
    (Real.monotoneOn_sin hyActualMemSin hyUpperMemSin hyActualUpper).trans hsinTaylor
  have hnumeric :
      3 * (1 + alternatingPartial (cosMagnitude yLower) 13) +
        routeBThetaLower * alternatingPartial (sinMagnitude yUpper) 13 -
          routeBThetaLower ^ 2 / 2 < 1 / 100 := by
    norm_num [alternatingPartial, cosMagnitude, sinMagnitude, Finset.sum_range_succ,
      yUpper, yLower, routeBThetaLower, piLower20, piUpper20]
  have hcosRewrite : Real.cos routeBThetaLower =
      -Real.cos (routeBThetaLower - Real.pi) := by
    rw [show routeBThetaLower = Real.pi + (routeBThetaLower - Real.pi) by ring,
      Real.cos_add]
    simp
  have hsinRewrite : Real.sin routeBThetaLower =
      -Real.sin (routeBThetaLower - Real.pi) := by
    rw [show routeBThetaLower = Real.pi + (routeBThetaLower - Real.pi) by ring,
      Real.sin_add]
    simp
  rw [routeBF, hcosRewrite, hsinRewrite]
  have htheta : 0 < routeBThetaLower := by norm_num [routeBThetaLower]
  nlinarith

theorem routeBKappa_gt_lower : routeBKappaLower < routeBKappa := by
  have haMem : routeBThetaLower ∈ Set.Ioc 0 routeBTheta :=
    ⟨by norm_num [routeBThetaLower], routeBTheta_gt_lower.le⟩
  have hthetaMem : routeBTheta ∈ Set.Ioc 0 routeBTheta :=
    ⟨lt_trans Real.pi_pos routeBTheta_mem.1, le_rfl⟩
  have hmono := routeBMaxQuotient_monotoneOn_to_theta
    haMem hthetaMem routeBTheta_gt_lower.le
  dsimp only [routeBKappa]
  linarith [routeBMaxQuotient_thetaLower_gt_kappaLower]

theorem routeBMaxQuotient_deriv_le_on_lower_theta {v : ℝ}
    (hv : v ∈ Set.Ioo routeBThetaLower routeBTheta) :
    deriv routeBMaxQuotient v ≤ 1 / 10000 := by
  have hv0 : 0 < v := lt_trans (by norm_num [routeBThetaLower]) hv.1
  rw [(hasDerivAt_routeBMaxQuotient hv0.ne').deriv]
  have haPi : Real.pi ≤ routeBThetaLower := by
    have hpi := Real.pi_lt_d2
    norm_num [routeBThetaLower] at hpi ⊢
    linarith
  have haMem : routeBThetaLower ∈ Set.Icc Real.pi (2 * Real.pi) :=
    ⟨haPi, by
      norm_num [routeBThetaLower]
      nlinarith [Real.pi_gt_three]⟩
  have hvMem : v ∈ Set.Icc Real.pi (2 * Real.pi) :=
    ⟨haPi.trans hv.1.le,
      by linarith [hv.2, routeBTheta_mem.2, Real.pi_pos]⟩
  have hFle : routeBF v ≤ routeBF routeBThetaLower :=
    routeBF_strictAntiOn_pi_two_pi.antitoneOn haMem hvMem hv.1.le
  have hFupper : routeBF v < 1 / 100 :=
    hFle.trans_lt routeBF_thetaLower_lt_one_div_100
  have hv35 : (7 / 2 : ℝ) < v := by
    norm_num [routeBThetaLower] at hv ⊢
    linarith [hv.1]
  have hvPowRaw := pow_lt_pow_left₀ hv35 (by norm_num : (0 : ℝ) ≤ 7 / 2)
    (by norm_num : (4 : ℕ) ≠ 0)
  have hvPow : (100 : ℝ) < v ^ 4 := by
    norm_num at hvPowRaw
    linarith
  have hden : 0 < v ^ 4 := lt_trans (by norm_num) hvPow
  rw [div_le_iff₀ hden]
  nlinarith

theorem routeBMaxQuotient_theta_variation :
    routeBMaxQuotient routeBTheta - routeBMaxQuotient routeBThetaLower ≤
      (1 / 10000) * (routeBTheta - routeBThetaLower) := by
  let D := Set.Icc routeBThetaLower routeBTheta
  have horder : routeBThetaLower ≤ routeBTheta := routeBTheta_gt_lower.le
  have hcont : ContinuousOn routeBMaxQuotient D := by
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le
      (by norm_num [routeBThetaLower]) hv.1
    exact (hasDerivAt_routeBMaxQuotient hv0.ne').continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ routeBMaxQuotient (interior D) := by
    intro v hv
    dsimp only [D] at hv
    rw [interior_Icc] at hv
    have hv0 : 0 < v := lt_trans (by norm_num [routeBThetaLower]) hv.1
    exact (hasDerivAt_routeBMaxQuotient hv0.ne').differentiableAt.differentiableWithinAt
  have hderiv : ∀ v ∈ interior D, deriv routeBMaxQuotient v ≤ 1 / 10000 := by
    intro v hv
    dsimp only [D] at hv
    rw [interior_Icc] at hv
    exact routeBMaxQuotient_deriv_le_on_lower_theta hv
  exact (convex_Icc routeBThetaLower routeBTheta).image_sub_le_mul_sub_of_deriv_le
    hcont hdiff hderiv routeBThetaLower ⟨le_rfl, horder⟩ routeBTheta
      ⟨horder, le_rfl⟩ horder

theorem routeBKappa_lt_upper : routeBKappa < routeBKappaUpper := by
  have hvar := routeBMaxQuotient_theta_variation
  have hwidth : routeBTheta - routeBThetaLower <
      routeBThetaUpper - routeBThetaLower := by
    linarith [routeBTheta_lt_upper]
  have hC : (0 : ℝ) < 1 / 10000 := by norm_num
  have hscaled : (1 / 10000) * (routeBTheta - routeBThetaLower) <
      (1 / 10000) * (routeBThetaUpper - routeBThetaLower) :=
    mul_lt_mul_of_pos_left hwidth hC
  have hnumeric : routeBQuotientAtLowerUpper +
      (1 / 10000) * (routeBThetaUpper - routeBThetaLower) < routeBKappaUpper := by
    norm_num [routeBQuotientAtLowerUpper, routeBThetaUpper,
      routeBThetaLower, routeBKappaUpper]
  dsimp only [routeBKappa]
  linarith [routeBMaxQuotient_thetaLower_lt_upper]

end

end BerryEsseen
