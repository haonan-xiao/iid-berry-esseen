import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The real-variable Vaaler majorant used by Prawitz smoothing

This file isolates the real-space half of the Prawitz argument.  The Fourier
representation is kept separate: here we define the nonnegative tail series
appearing in Vaaler's sign approximant and prove its two telescoping bounds.
-/

open Filter Finset Topology
open scoped BigOperators Real

namespace BerryEsseen

noncomputable section

/-- The positive tail in the partial-fraction representation of Vaaler's
approximant. -/
def prawitzTailSeries (x : ℝ) : ℝ :=
  ∑' m : ℕ, 1 / (x + (m : ℝ) + 1) ^ 2

private theorem prawitzTailTerm_nonneg (x : ℝ) (m : ℕ) :
    0 ≤ 1 / (x + (m : ℝ) + 1) ^ 2 := by positivity

private theorem prawitzTailTerm_le_leftTelescope {x : ℝ} (hx : 0 < x) (m : ℕ) :
    1 / (x + (m : ℝ) + 1) ^ 2 ≤
      1 / (x + (m : ℝ)) - 1 / (x + (m : ℝ) + 1) := by
  let p : ℝ := x + (m : ℝ)
  let y : ℝ := p + 1
  have hp : 0 < p := by dsimp only [p]; positivity
  have hy : 0 < y := by dsimp only [y]; positivity
  have hpy : p * y ≤ y ^ 2 := by
    have hple : p ≤ y := by dsimp only [y]; linarith
    nlinarith
  have hrecip : 1 / y ^ 2 ≤ 1 / (p * y) :=
    one_div_le_one_div_of_le (mul_pos hp hy) hpy
  have htelescope : 1 / p - 1 / y = 1 / (p * y) := by
    field_simp [hp.ne', hy.ne']
    dsimp only [y]
    ring
  have hfinal : 1 / y ^ 2 ≤ 1 / p - 1 / y := by
    rw [htelescope]
    exact hrecip
  simpa only [p, y] using hfinal

private theorem prawitzTailTerm_ge_rightTelescope {x : ℝ} (hx : 0 < x) (m : ℕ) :
    1 / (x + (m : ℝ) + 1) - 1 / (x + (m : ℝ) + 2) ≤
      1 / (x + (m : ℝ) + 1) ^ 2 := by
  let y : ℝ := x + (m : ℝ) + 1
  let z : ℝ := y + 1
  have hy : 0 < y := by dsimp only [y]; positivity
  have hz : 0 < z := by dsimp only [z]; positivity
  have hsq : y ^ 2 ≤ y * z := by
    have hyz : y ≤ z := by dsimp only [z]; linarith
    nlinarith
  have hrecip : 1 / (y * z) ≤ 1 / y ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hy) hsq
  have htelescope : 1 / y - 1 / z = 1 / (y * z) := by
    field_simp [hy.ne', hz.ne']
    dsimp only [z]
    ring
  have hfinal : 1 / y - 1 / z ≤ 1 / y ^ 2 := by
    rw [htelescope]
    exact hrecip
  dsimp only [y, z] at hfinal
  convert hfinal using 1 <;> ring

theorem summable_prawitzTailSeries {x : ℝ} (hx : 0 < x) :
    Summable (fun m : ℕ => 1 / (x + (m : ℝ) + 1) ^ 2) := by
  apply summable_of_sum_range_le (fun m => prawitzTailTerm_nonneg x m)
  intro n
  calc
    (∑ m ∈ range n, 1 / (x + (m : ℝ) + 1) ^ 2) ≤
        ∑ m ∈ range n,
          (1 / (x + (m : ℝ)) - 1 / (x + (m : ℝ) + 1)) := by
      exact sum_le_sum fun m _ => prawitzTailTerm_le_leftTelescope hx m
    _ = 1 / x - 1 / (x + (n : ℝ)) := by
      convert (sum_range_sub' (fun m : ℕ => 1 / (x + (m : ℝ))) n) using 1 <;>
        norm_num <;> ring
    _ ≤ 1 / x := by
      have hnonneg : 0 ≤ 1 / (x + (n : ℝ)) := by positivity
      linarith

theorem prawitzTailSeries_le_inv {x : ℝ} (hx : 0 < x) :
    prawitzTailSeries x ≤ 1 / x := by
  unfold prawitzTailSeries
  apply Real.tsum_le_of_sum_range_le (fun m => prawitzTailTerm_nonneg x m)
  intro n
  calc
    (∑ m ∈ range n, 1 / (x + (m : ℝ) + 1) ^ 2) ≤
        ∑ m ∈ range n,
          (1 / (x + (m : ℝ)) - 1 / (x + (m : ℝ) + 1)) := by
      exact sum_le_sum fun m _ => prawitzTailTerm_le_leftTelescope hx m
    _ = 1 / x - 1 / (x + (n : ℝ)) := by
      convert (sum_range_sub' (fun m : ℕ => 1 / (x + (m : ℝ))) n) using 1 <;>
        norm_num <;> ring
    _ ≤ 1 / x := by
      have hnonneg : 0 ≤ 1 / (x + (n : ℝ)) := by positivity
      linarith

theorem inv_add_one_le_prawitzTailSeries {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ≤ prawitzTailSeries x := by
  have hsummable := summable_prawitzTailSeries hx
  have hpartial : ∀ n : ℕ,
      1 / (x + 1) - 1 / (x + (n : ℝ) + 1) ≤ prawitzTailSeries x := by
    intro n
    calc
      1 / (x + 1) - 1 / (x + (n : ℝ) + 1) =
          ∑ m ∈ range n,
            (1 / (x + (m : ℝ) + 1) - 1 / (x + (m : ℝ) + 2)) := by
        convert
          (sum_range_sub' (fun m : ℕ => 1 / (x + (m : ℝ) + 1)) n).symm
            using 1 <;> norm_num <;> ring
      _ ≤ ∑ m ∈ range n, 1 / (x + (m : ℝ) + 1) ^ 2 := by
        exact sum_le_sum fun m _ => prawitzTailTerm_ge_rightTelescope hx m
      _ ≤ prawitzTailSeries x := by
        unfold prawitzTailSeries
        exact hsummable.sum_le_tsum (range n) (fun m _ => prawitzTailTerm_nonneg x m)
  have hinvTendsto : Tendsto (fun n : ℕ => 1 / (x + (n : ℝ) + 1)) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      positivity
    · intro n
      have hdenom : (n : ℝ) + 1 ≤ x + (n : ℝ) + 1 := by linarith
      exact one_div_le_one_div_of_le (by positivity) hdenom
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hlimit : Tendsto
      (fun n : ℕ => 1 / (x + 1) - 1 / (x + (n : ℝ) + 1))
      atTop (𝓝 (1 / (x + 1))) := by
    simpa using tendsto_const_nhds.sub hinvTendsto
  exact le_of_tendsto hlimit (Eventually.of_forall hpartial)

/-- The two inequalities used in Vaaler's pointwise sign approximation. -/
theorem prawitzTailSeries_two_sided {x : ℝ} (hx : 0 < x) :
    prawitzTailSeries x ≤ 1 / x ∧
      1 / x ≤ 1 / x ^ 2 + prawitzTailSeries x := by
  refine ⟨prawitzTailSeries_le_inv hx, ?_⟩
  have hlower := inv_add_one_le_prawitzTailSeries hx
  have haux : 1 / x ≤ 1 / x ^ 2 + 1 / (x + 1) := by
    field_simp [hx.ne']
    nlinarith [sq_nonneg x]
  linarith

/-- `S(x) = (sin (pi x) / pi)^2`. -/
def prawitzS (x : ℝ) : ℝ :=
  (Real.sin (Real.pi * x) / Real.pi) ^ 2

/-- The Fejér majorant `J`, with its removable value at zero filled in. -/
def prawitzJ (x : ℝ) : ℝ :=
  if x = 0 then 1 else prawitzS x / x ^ 2

/-- Vaaler's positive-half-line sign approximant. -/
def prawitzPositiveH (x : ℝ) : ℝ :=
  1 - prawitzS x *
    (1 / x ^ 2 + 2 * prawitzTailSeries x - 2 / x)

/-- The odd Vaaler approximant to the sign function. -/
def prawitzH (x : ℝ) : ℝ :=
  if x = 0 then 0
  else if 0 < x then prawitzPositiveH x else -prawitzPositiveH (-x)

theorem prawitzS_nonneg (x : ℝ) : 0 ≤ prawitzS x := by
  unfold prawitzS
  positivity

theorem prawitzS_neg (x : ℝ) : prawitzS (-x) = prawitzS x := by
  unfold prawitzS
  rw [mul_neg, Real.sin_neg]
  ring

theorem prawitzJ_nonneg (x : ℝ) : 0 ≤ prawitzJ x := by
  by_cases hx : x = 0
  · simp [prawitzJ, hx]
  · rw [prawitzJ, if_neg hx]
    exact div_nonneg (prawitzS_nonneg x) (sq_nonneg x)

theorem prawitzJ_neg (x : ℝ) : prawitzJ (-x) = prawitzJ x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hneg : -x ≠ 0 := neg_ne_zero.mpr hx
    rw [prawitzJ, if_neg hneg, prawitzJ, if_neg hx, prawitzS_neg]
    ring

theorem prawitzH_zero : prawitzH 0 = 0 := by
  simp [prawitzH]

theorem prawitzH_of_pos {x : ℝ} (hx : 0 < x) :
    prawitzH x = prawitzPositiveH x := by
  simp [prawitzH, hx.ne', hx]

theorem prawitzH_of_neg {x : ℝ} (hx : x < 0) :
    prawitzH x = -prawitzPositiveH (-x) := by
  simp [prawitzH, hx.ne, hx.not_gt]

theorem prawitzH_neg (x : ℝ) : prawitzH (-x) = -prawitzH x := by
  obtain hx | rfl | hx := lt_trichotomy x 0
  · have hnegPos : 0 < -x := neg_pos.mpr hx
    rw [prawitzH_of_pos hnegPos, prawitzH_of_neg hx]
    simp
  · simp [prawitzH_zero]
  · have hnegNeg : -x < 0 := neg_lt_zero.mpr hx
    rw [prawitzH_of_neg hnegNeg, prawitzH_of_pos hx]
    simp

theorem prawitzJ_eq_sincSq {x : ℝ} (hx : x ≠ 0) :
    prawitzJ x = (Real.sin (Real.pi * x) / (Real.pi * x)) ^ 2 := by
  rw [prawitzJ, if_neg hx]
  unfold prawitzS
  field_simp [Real.pi_ne_zero, hx]

/-- Vaaler's pointwise estimate on the positive half-line. -/
theorem abs_one_sub_prawitzH_le_J {x : ℝ} (hx : 0 < x) :
    |1 - prawitzH x| ≤ prawitzJ x := by
  have htail := prawitzTailSeries_two_sided hx
  let B : ℝ := 1 / x ^ 2 + 2 * prawitzTailSeries x - 2 / x
  have hBUpper : B ≤ 1 / x ^ 2 := by
    dsimp only [B]
    simp only [div_eq_mul_inv] at htail ⊢
    linarith [htail.1]
  have hBLower : -(1 / x ^ 2) ≤ B := by
    dsimp only [B]
    simp only [div_eq_mul_inv] at htail ⊢
    linarith [htail.2]
  have hBAbs : |B| ≤ 1 / x ^ 2 := by
    rw [abs_le]
    exact ⟨hBLower, hBUpper⟩
  have hS : 0 ≤ prawitzS x := prawitzS_nonneg x
  rw [prawitzH_of_pos hx]
  unfold prawitzPositiveH
  rw [show 1 - (1 - prawitzS x *
      (1 / x ^ 2 + 2 * prawitzTailSeries x - 2 / x)) =
      prawitzS x * B by dsimp only [B]; ring]
  calc
    |prawitzS x * B| = prawitzS x * |B| := by
      rw [abs_mul, abs_of_nonneg hS]
    _ ≤ prawitzS x * (1 / x ^ 2) :=
      mul_le_mul_of_nonneg_left hBAbs hS
    _ = prawitzJ x := by
      rw [prawitzJ, if_neg hx.ne']
      ring

/-- Equation (4.3): Vaaler's band-limited approximant squeezes the sign
function with Fejér error `J`. -/
theorem abs_sign_sub_prawitzH_le_J (x : ℝ) :
    |Real.sign x - prawitzH x| ≤ prawitzJ x := by
  obtain hx | rfl | hx := lt_trichotomy x 0
  · have hy : 0 < -x := neg_pos.mpr hx
    have hpos := abs_one_sub_prawitzH_le_J hy
    rw [prawitzH_of_pos hy] at hpos
    rw [Real.sign_of_neg hx, prawitzH_of_neg hx, ← prawitzJ_neg x]
    simpa only [neg_sub_neg, abs_sub_comm] using hpos
  · simp [prawitzH_zero, prawitzJ]
  · rw [Real.sign_of_pos hx]
    exact abs_one_sub_prawitzH_le_J hx

/-- The upper and lower Vaaler functions squeeze the half-line indicator. -/
theorem prawitz_halfLine_sandwich (x : ℝ) :
    (1 - prawitzH x - prawitzJ x) / 2 ≤ Set.indicator (Set.Iic 0)
        (fun _ : ℝ => (1 : ℝ)) x ∧
      Set.indicator (Set.Iic 0) (fun _ : ℝ => (1 : ℝ)) x ≤
        (1 - prawitzH x + prawitzJ x) / 2 := by
  have hV := abs_sign_sub_prawitzH_le_J x
  have hbounds := (abs_le.mp hV)
  by_cases hx : x ≤ 0
  · have hindicator : Set.indicator (Set.Iic 0)
        (fun _ : ℝ => (1 : ℝ)) x = 1 := by
      rw [Set.indicator_of_mem]
      exact hx
    rw [hindicator]
    by_cases hx0 : x = 0
    · subst x
      simp [prawitzH_zero, prawitzJ]
    · rw [Real.sign_of_neg (lt_of_le_of_ne hx hx0)] at hbounds
      constructor <;> linarith
  · have hxPos : 0 < x := lt_of_not_ge hx
    have hindicator : Set.indicator (Set.Iic 0)
        (fun _ : ℝ => (1 : ℝ)) x = 0 := by
      rw [Set.indicator_of_notMem]
      exact hx
    rw [hindicator]
    rw [Real.sign_of_pos hxPos] at hbounds
    constructor <;> linarith

end

end BerryEsseen
