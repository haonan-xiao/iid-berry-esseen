import BerryEsseen.Universal

open MeasureTheory ProbabilityTheory

namespace BerryEsseen

noncomputable section

def refinedUniversalConstant : ℝ := 109 / 200

def refinedUniversalPolynomial (a : ℝ) : ℝ :=
  9 - 80 * a + 209 * a ^ 2 - 80 * a ^ 3

theorem refinedUniversalPolynomial_nonneg
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ refinedUniversalPolynomial a := by
  by_cases hquarter : a ≤ 1 / 4
  · have htail : 0 ≤ 1 - 4 * a := by linarith
    have hcubic : 0 ≤ 20 * a ^ 2 * (1 - 4 * a) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg a)) htail
    have hsquare : 0 ≤ (189 * a - 40) ^ 2 := sq_nonneg _
    unfold refinedUniversalPolynomial
    nlinarith
  · have hquarter' : 1 / 4 ≤ a := le_of_lt (lt_of_not_ge hquarter)
    have hlinear : 0 ≤ 169 - 80 * a := by linarith
    have hqfactor : 0 ≤ (a - 1 / 4) * (169 - 80 * a) :=
      mul_nonneg (sub_nonneg.mpr hquarter') hlinear
    have hq : 0 ≤ -80 * a ^ 2 + 189 * a - 131 / 4 := by
      nlinarith
    have hmain :
        0 ≤ (a - 1 / 4) * (-80 * a ^ 2 + 189 * a - 131 / 4) :=
      mul_nonneg (sub_nonneg.mpr hquarter') hq
    unfold refinedUniversalPolynomial
    nlinarith

theorem refinedUniversalRationalEnvelope_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    1 / (1 + a ^ 2) - 1 / 2 + 2 * a / 5 ≤
      refinedUniversalConstant := by
  have hp := refinedUniversalPolynomial_nonneg ha0 ha1
  have hden : 0 < 200 * (1 + a ^ 2) := by positivity
  have hid :
      refinedUniversalConstant -
          (1 / (1 + a ^ 2) - 1 / 2 + 2 * a / 5) =
        refinedUniversalPolynomial a / (200 * (1 + a ^ 2)) := by
    rw [refinedUniversalConstant, refinedUniversalPolynomial]
    field_simp
    ring
  have hquot :
      0 ≤ refinedUniversalPolynomial a / (200 * (1 + a ^ 2)) :=
    div_nonneg hp hden.le
  linarith

theorem refinedUniversal_kolmogorov_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 2 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hvariance : Var[(id : ℝ → ℝ); mu] = 1) :
    kolmogorovDistance mu standardNormalLaw ≤ refinedUniversalConstant := by
  apply (kolmogorovDistance_le_iff_pointwise mu standardNormalLaw
    refinedUniversalConstant).2
  intro x
  have hhalf : (1 / 2 : ℝ) ≤ refinedUniversalConstant := by
    norm_num [refinedUniversalConstant]
  have hFnonneg := lawCDF_nonneg mu x
  have hFle := lawCDF_le_one mu x
  have hPhiNonneg := lawCDF_nonneg standardNormalLaw x
  have hPhiLe := lawCDF_le_one standardNormalLaw x
  rcases lt_trichotomy x 0 with hxneg | hxzero | hxpos
  · have hPhiHalf : lawCDF standardNormalLaw x ≤ 1 / 2 := by
      have hmono := isCDF_standardNormalLaw.mono hxneg.le
      rw [standardNormalCDF_zero] at hmono
      exact hmono
    have hleft : -refinedUniversalConstant ≤
        lawCDF mu x - lawCDF standardNormalLaw x := by
      linarith
    let a : ℝ := -x
    have ha : 0 < a := by dsimp [a]; linarith
    have htail := measureReal_Iic_neg_le_cantelli mu hX hmean hvariance ha
    have hFtail : lawCDF mu x ≤ 1 / (1 + a ^ 2) := by
      dsimp [a] at htail ⊢
      simpa only [neg_neg, lawCDF, measureReal_def] using htail
    have hright : lawCDF mu x - lawCDF standardNormalLaw x ≤
        refinedUniversalConstant := by
      by_cases haone : a ≤ 1
      · have hnormal := standardNormalCDF_neg_linear_lower ha.le
        have hnormalX : 1 / 2 - 2 * a / 5 ≤
            lawCDF standardNormalLaw x := by
          simpa only [a, neg_neg] using hnormal
        have henv := refinedUniversalRationalEnvelope_le ha.le haone
        linarith
      · have haone' : 1 ≤ a := le_of_lt (lt_of_not_ge haone)
        have htailHalf := one_div_one_add_sq_le_half haone'
        linarith
    exact (abs_le).2 ⟨hleft, hright⟩
  · subst x
    rw [standardNormalCDF_zero]
    exact (abs_le).2 (by constructor <;> linarith)
  · have hPhiHalf : 1 / 2 ≤ lawCDF standardNormalLaw x := by
      have hmono := isCDF_standardNormalLaw.mono hxpos.le
      rw [standardNormalCDF_zero] at hmono
      exact hmono
    have hright : lawCDF mu x - lawCDF standardNormalLaw x ≤
        refinedUniversalConstant := by
      linarith
    have hmuComplement := lawCDF_add_upperTail mu x
    have htailOpen : mu.real (Set.Ioi x) ≤ 1 / (1 + x ^ 2) := by
      calc
        mu.real (Set.Ioi x) ≤ mu.real (Set.Ici x) :=
          measureReal_mono Set.Ioi_subset_Ici_self
        _ ≤ 1 / (1 + x ^ 2) :=
          measureReal_Ici_le_cantelli mu hX hmean hvariance hxpos
    have hleft : -refinedUniversalConstant ≤
        lawCDF mu x - lawCDF standardNormalLaw x := by
      by_cases hxone : x ≤ 1
      · have hnormal := standardNormalUpperTail_linear_lower hxpos.le
        have henv := refinedUniversalRationalEnvelope_le hxpos.le hxone
        linarith
      · have hxone' : 1 ≤ x := le_of_lt (lt_of_not_ge hxone)
        have htailHalf := one_div_one_add_sq_le_half hxone'
        have hnormalTail : 0 ≤ 1 - lawCDF standardNormalLaw x := by
          linarith
        linarith
    exact (abs_le).2 ⟨hleft, hright⟩

end

end BerryEsseen
