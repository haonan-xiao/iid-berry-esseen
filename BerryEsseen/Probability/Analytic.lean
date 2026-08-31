import BerryEsseen.Certificate.Boundary
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# First closed analytic units from Route B

These lemmas formalize the exact arithmetic used in the universal `0.56` branch and the
zero-frequency edge case of the one-step characteristic-function estimate.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal Real

namespace BerryEsseen

/-- The cubic polynomial appearing in the proof of the universal cutoff. -/
def universalPolynomial (a : ℝ) : ℝ :=
  3 - 20 * a + 53 * a ^ 2 - 20 * a ^ 3

/-- The source proof's cubic is nonnegative on `[0,1]`. -/
theorem universalPolynomial_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ universalPolynomial a := by
  by_cases hquarter : a ≤ 1 / 4
  · have htail : 0 ≤ 1 - 4 * a := by linarith
    have hfactor : 0 ≤ 5 * a ^ 2 * (1 - 4 * a) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg a)) htail
    have hsquare : 0 ≤ (24 * a - 5) ^ 2 := sq_nonneg _
    unfold universalPolynomial
    nlinarith
  · have hquarter' : 1 / 4 ≤ a := le_of_lt (lt_of_not_ge hquarter)
    by_cases hhalf : a ≤ 1 / 2
    · have htail : 0 ≤ 1 - 2 * a := by linarith
      have hfactor : 0 ≤ 10 * a ^ 2 * (1 - 2 * a) :=
        mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg a)) htail
      have hsquare : 0 ≤ (43 * a - 10) ^ 2 := sq_nonneg _
      unfold universalPolynomial
      nlinarith
    · have hhalf' : 1 / 2 ≤ a := le_of_lt (lt_of_not_ge hhalf)
      have hlinear : 0 ≤ -20 * a + 43 := by linarith
      have hfactor : 0 ≤ (a - 1 / 2) * (-20 * a + 43) :=
        mul_nonneg (sub_nonneg.mpr hhalf') hlinear
      unfold universalPolynomial
      nlinarith

/-- The rational envelope in the universal branch is at most `14/25` on `[0,1]`. -/
theorem universalRationalEnvelope_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    1 / (1 + a ^ 2) - 1 / 2 + 2 * a / 5 ≤ universalConstant := by
  have hp := universalPolynomial_nonneg ha0 ha1
  have hden : 0 < 50 * (1 + a ^ 2) := by positivity
  have hid :
      universalConstant - (1 / (1 + a ^ 2) - 1 / 2 + 2 * a / 5) =
        universalPolynomial a / (50 * (1 + a ^ 2)) := by
    rw [universalConstant, universalPolynomial]
    field_simp
    ring
  have hquot : 0 ≤ universalPolynomial a / (50 * (1 + a ^ 2)) :=
    div_nonneg hp hden.le
  linarith

/-- The normal-density bound `(2*pi)^(-1/2) < 2/5` used by the universal branch. -/
theorem inv_sqrt_two_pi_lt_two_fifths :
    (Real.sqrt (2 * Real.pi))⁻¹ < (2 / 5 : ℝ) := by
  have harg : 0 < 2 * Real.pi := by positivity
  have hsquare : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi := by
    rw [Real.sq_sqrt harg.le]
  have hroot : (5 / 2 : ℝ) < Real.sqrt (2 * Real.pi) := by
    have hnonneg := Real.sqrt_nonneg (2 * Real.pi)
    nlinarith [Real.pi_gt_d2]
  apply (inv_lt_iff_one_lt_mul₀ (Real.sqrt_pos.2 harg)).2
  nlinarith

/-- At zero frequency the characteristic-function and Gaussian terms agree exactly.  The later
normalized disk variable is therefore introduced only in the nonzero-frequency branch. -/
theorem oneStepNumerator_zero (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    charFun mu 0 - Complex.exp (-(0 : ℂ) ^ 2 / 2) = 0 := by
  rw [charFun_zero, probReal_univ]
  norm_num

/-- Telescoping power bound used in the final characteristic-function assembly. -/
theorem norm_pow_sub_pow_le {a b : ℂ} {M : ℝ}
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ ((n : ℝ) + 1) * ‖a - b‖ * M ^ n := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  induction n with
  | zero => simp
  | succ n ih =>
      have ih' :
          ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ ((n : ℝ) + 1) * ‖a - b‖ * M ^ n := ih
      have hsplit :
          a ^ (n + 2) - b ^ (n + 2) =
            (a ^ (n + 1) - b ^ (n + 1)) * a + b ^ (n + 1) * (a - b) := by
        ring
      rw [hsplit]
      calc
        ‖(a ^ (n + 1) - b ^ (n + 1)) * a + b ^ (n + 1) * (a - b)‖
            ≤ ‖(a ^ (n + 1) - b ^ (n + 1)) * a‖ + ‖b ^ (n + 1) * (a - b)‖ :=
              norm_add_le _ _
        _ = ‖a ^ (n + 1) - b ^ (n + 1)‖ * ‖a‖ + ‖b‖ ^ (n + 1) * ‖a - b‖ := by
              rw [norm_mul, norm_mul, norm_pow]
        _ ≤ ((n : ℝ) + 1) * ‖a - b‖ * M ^ n * M + M ^ (n + 1) * ‖a - b‖ := by
              apply add_le_add
              · exact mul_le_mul ih' ha (norm_nonneg a) (by positivity)
              · gcongr
        _ = (((Nat.succ n : ℕ) : ℝ) + 1) * ‖a - b‖ * M ^ (Nat.succ n) := by
              simp only [Nat.cast_succ, Nat.succ_eq_add_one]
              rw [pow_succ]
              ring

end BerryEsseen
