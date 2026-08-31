import BerryEsseen.Smoothing.Prawitz
import Mathlib.NumberTheory.ZetaValues

/-!
# Explicit cotangent bounds for the Route B checker

This module proves the two polynomial/rational bounds used by the exact numerical verifier for
`d(x) = 1 / x - cot x`.  The proof starts from Mathlib's Mittag--Leffler expansion of cotangent,
expands each positive summand through order six, and sums the coefficients using the exact
values of `zeta(2)`, `zeta(4)`, `zeta(6)`, and `zeta(8)`.  Thus the constants in the checker are
derived analytically rather than trusted as numerical assumptions.
-/

open scoped Real

namespace BerryEsseen

noncomputable section

private def cotGapSummand (s : ℝ) (n : ℕ) : ℝ :=
  2 * s / (((n + 1 : ℕ) : ℝ) ^ 2 - s ^ 2)

private def cotGapBaseSummand (s : ℝ) (n : ℕ) : ℝ :=
  let m : ℝ := (n + 1 : ℕ)
  2 * s / m ^ 2 + 2 * s ^ 3 / m ^ 4 + 2 * s ^ 5 / m ^ 6

private def cotGapRemainder (s : ℝ) (n : ℕ) : ℝ :=
  let m : ℝ := (n + 1 : ℕ)
  2 * s ^ 7 / (m ^ 6 * (m ^ 2 - s ^ 2))

private def cotGapRemainderMajorant (s : ℝ) (n : ℕ) : ℝ :=
  let m : ℝ := (n + 1 : ℕ)
  (2 * s ^ 7 / (1 - s ^ 2)) * (1 / m ^ 8)

private lemma bernoulli'_five_local : bernoulli' 5 = 0 := by
  exact bernoulli'_eq_zero_of_odd ⟨2, by norm_num⟩ (by norm_num)

private lemma bernoulli'_six_local : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_five_local, Nat.choose]

private lemma bernoulli'_seven_local : bernoulli' 7 = 0 := by
  exact bernoulli'_eq_zero_of_odd ⟨3, by norm_num⟩ (by norm_num)

private lemma bernoulli'_eight_local : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_five_local, bernoulli'_six_local,
    bernoulli'_seven_local, Nat.choose]

private lemma hasSum_zeta_six_local :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 6) (Real.pi ^ 6 / 945) := by
  convert hasSum_zeta_nat (k := 3) (by norm_num) using 1
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num : 6 ≠ 1), bernoulli'_six_local]
  norm_num [Nat.factorial]
  ring

private lemma hasSum_zeta_eight_local :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 8) (Real.pi ^ 8 / 9450) := by
  convert hasSum_zeta_nat (k := 4) (by norm_num) using 1
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num : 8 ≠ 1), bernoulli'_eight_local]
  norm_num [Nat.factorial]
  ring

private lemma tsum_zeta_nat_succ {p : ℕ} (hp : p ≠ 0) {z : ℝ}
    (h : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ p) z) :
    (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ p) = z := by
  have hsplit := h.summable.sum_add_tsum_nat_add 1
  rw [h.tsum_eq] at hsplit
  simpa [hp, Nat.cast_add, Nat.cast_one] using hsplit

private lemma summable_zeta_nat_succ {p : ℕ} {z : ℝ}
    (h : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ p) z) :
    Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ p) := by
  simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 h.summable

private lemma real_mem_integerComplement {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (s : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have hns : (n : ℝ) = s := by
    exact_mod_cast congrArg Complex.re hn
  have hn0 : (0 : ℤ) < n := by
    exact_mod_cast (show (0 : ℝ) < (n : ℝ) by simpa [hns] using hs0)
  have hn1 : n < (1 : ℤ) := by
    exact_mod_cast (show (n : ℝ) < (1 : ℝ) by simpa [hns] using hs1)
  omega

private lemma cotTerm_ofReal_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (n : ℕ) :
    cotTerm (s : ℂ) n = (-(cotGapSummand s n) : ℝ) := by
  have hm : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
  have hminus : s - ((n + 1 : ℕ) : ℝ) ≠ 0 := by linarith
  have hplus : s + ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hsq : (((n + 1 : ℕ) : ℝ) ^ 2 - s ^ 2) ≠ 0 := by nlinarith
  have hreal :
      1 / (s - ((n + 1 : ℕ) : ℝ)) + 1 / (s + ((n + 1 : ℕ) : ℝ)) =
        -(2 * s / (((n + 1 : ℕ) : ℝ) ^ 2 - s ^ 2)) := by
    field_simp [hminus, hplus, hsq]
    ring
  simp only [cotTerm, cotGapSummand]
  norm_cast
  convert hreal using 1
  all_goals norm_num

private lemma cot_gap_eq_tsum {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    1 / s - Real.pi * Real.cot (Real.pi * s) =
      ∑' n : ℕ, cotGapSummand s n := by
  have hz := real_mem_integerComplement hs0 hs1
  have hcot := cot_series_rep' hz
  simp_rw [cotTerm_ofReal_eq hs0 hs1] at hcot
  rw [← Complex.ofReal_tsum] at hcot
  rw [tsum_neg] at hcot
  have hcotReal :
      Complex.cot ((Real.pi : ℂ) * (s : ℂ)) =
        (Real.cot (Real.pi * s) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cot]
  rw [hcotReal] at hcot
  norm_cast at hcot
  linarith

private lemma summable_cotGapSummand {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Summable (cotGapSummand s) := by
  have hz := real_mem_integerComplement hs0 hs1
  have hc : Summable (fun n : ℕ => ((-cotGapSummand s n : ℝ) : ℂ)) :=
    (summable_cotTerm hz).congr fun n => cotTerm_ofReal_eq hs0 hs1 n
  have hr : Summable (fun n : ℕ => -cotGapSummand s n) :=
    Complex.summable_ofReal.mp hc
  simpa only [neg_neg] using hr.neg

private lemma cotGapSummand_eq_base_add_remainder {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (n : ℕ) :
    cotGapSummand s n = cotGapBaseSummand s n + cotGapRemainder s n := by
  let m : ℝ := (n + 1 : ℕ)
  have hm1 : 1 ≤ m := by simp [m]
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  have hdiff : 0 < m ^ 2 - s ^ 2 := by nlinarith
  have halgebra :
      2 * s / (m ^ 2 - s ^ 2) =
        (2 * s / m ^ 2 + 2 * s ^ 3 / m ^ 4 + 2 * s ^ 5 / m ^ 6) +
          2 * s ^ 7 / (m ^ 6 * (m ^ 2 - s ^ 2)) := by
    field_simp [hm0.ne', hdiff.ne']
    ring
  simpa [cotGapSummand, cotGapBaseSummand, cotGapRemainder, m,
    Nat.cast_add, Nat.cast_one, add_comm] using halgebra

private lemma cotGapRemainder_nonneg {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (n : ℕ) :
    0 ≤ cotGapRemainder s n := by
  let m : ℝ := (n + 1 : ℕ)
  have hm1 : 1 ≤ m := by simp [m]
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  have hdiff : 0 < m ^ 2 - s ^ 2 := by nlinarith
  dsimp [cotGapRemainder, m]
  positivity

private lemma cotGapRemainder_le_majorant {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (n : ℕ) :
    cotGapRemainder s n ≤ cotGapRemainderMajorant s n := by
  let m : ℝ := (n + 1 : ℕ)
  have hm1 : 1 ≤ m := by simp [m]
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  have hsden : 0 < 1 - s ^ 2 := by nlinarith
  have hdiff : 0 < m ^ 2 - s ^ 2 := by nlinarith
  have hmajorDen : 0 < (1 - s ^ 2) * m ^ 8 := mul_pos hsden (pow_pos hm0 8)
  have hden : (1 - s ^ 2) * m ^ 8 ≤ m ^ 6 * (m ^ 2 - s ^ 2) := by
    have hmsq : 1 ≤ m ^ 2 := by nlinarith
    have hfactor : 0 ≤ s ^ 2 * m ^ 6 * (m ^ 2 - 1) :=
      mul_nonneg (mul_nonneg (sq_nonneg s) (pow_nonneg hm0.le 6)) (sub_nonneg.mpr hmsq)
    nlinarith
  dsimp [cotGapRemainder, cotGapRemainderMajorant, m]
  calc
    2 * s ^ 7 / (m ^ 6 * (m ^ 2 - s ^ 2)) ≤
        2 * s ^ 7 / ((1 - s ^ 2) * m ^ 8) := by
      exact div_le_div_of_nonneg_left (by positivity) hmajorDen hden
    _ = (2 * s ^ 7 / (1 - s ^ 2)) * (1 / m ^ 8) := by
      field_simp [hsden.ne', hm0.ne']

private lemma summable_cotGapBaseSummand (s : ℝ) : Summable (cotGapBaseSummand s) := by
  have h2 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    simpa only [one_div] using summable_zeta_nat_succ hasSum_zeta_two
  have h4 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 4)⁻¹) := by
    simpa only [one_div] using summable_zeta_nat_succ hasSum_zeta_four
  have h6 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 6)⁻¹) := by
    simpa only [one_div] using summable_zeta_nat_succ hasSum_zeta_six_local
  have h2c := h2.mul_left (2 * s)
  have h4c := h4.mul_left (2 * s ^ 3)
  have h6c := h6.mul_left (2 * s ^ 5)
  exact ((h2c.add h4c).add h6c).congr fun n => by
    simp only [cotGapBaseSummand, div_eq_mul_inv]

private lemma tsum_cotGapBaseSummand (s : ℝ) :
    (∑' n : ℕ, cotGapBaseSummand s n) =
      Real.pi ^ 2 * s / 3 + Real.pi ^ 4 * s ^ 3 / 45 +
        2 * Real.pi ^ 6 * s ^ 5 / 945 := by
  have h2 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    simpa only [one_div] using summable_zeta_nat_succ hasSum_zeta_two
  have h4 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 4)⁻¹) := by
    simpa only [one_div] using summable_zeta_nat_succ hasSum_zeta_four
  have h6 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 6)⁻¹) := by
    simpa only [one_div] using summable_zeta_nat_succ hasSum_zeta_six_local
  have h2c := h2.mul_left (2 * s)
  have h4c := h4.mul_left (2 * s ^ 3)
  have h6c := h6.mul_left (2 * s ^ 5)
  simp only [cotGapBaseSummand, div_eq_mul_inv]
  rw [(h2c.add h4c).tsum_add h6c, h2c.tsum_add h4c]
  rw [tsum_mul_left, tsum_mul_left, tsum_mul_left]
  have hz2 : (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) = Real.pi ^ 2 / 6 := by
    simpa only [one_div] using tsum_zeta_nat_succ (by norm_num) hasSum_zeta_two
  have hz4 : (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ 4)⁻¹) = Real.pi ^ 4 / 90 := by
    simpa only [one_div] using tsum_zeta_nat_succ (by norm_num) hasSum_zeta_four
  have hz6 : (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ 6)⁻¹) = Real.pi ^ 6 / 945 := by
    simpa only [one_div] using tsum_zeta_nat_succ (by norm_num) hasSum_zeta_six_local
  rw [hz2, hz4, hz6]
  ring

private lemma summable_cotGapRemainderMajorant (s : ℝ) :
    Summable (cotGapRemainderMajorant s) := by
  have h8 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 8)⁻¹) := by
    simpa only [one_div] using summable_zeta_nat_succ hasSum_zeta_eight_local
  have hc := h8.mul_left (2 * s ^ 7 / (1 - s ^ 2))
  exact hc.congr fun n => by
    simp only [cotGapRemainderMajorant, div_eq_mul_inv, one_mul]

private lemma tsum_cotGapRemainderMajorant {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (∑' n : ℕ, cotGapRemainderMajorant s n) =
      Real.pi ^ 8 * s ^ 7 / (4725 * (1 - s ^ 2)) := by
  have hsden : 1 - s ^ 2 ≠ 0 := by nlinarith
  simp only [cotGapRemainderMajorant, div_eq_mul_inv]
  rw [tsum_mul_left]
  simp only [one_mul]
  have hz8 : (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ 8)⁻¹) = Real.pi ^ 8 / 9450 := by
    simpa only [one_div] using tsum_zeta_nat_succ (by norm_num) hasSum_zeta_eight_local
  rw [hz8]
  field_simp [hsden]
  ring

private lemma cotGap_scaled_lower {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Real.pi ^ 2 * s / 3 + Real.pi ^ 4 * s ^ 3 / 45 +
        2 * Real.pi ^ 6 * s ^ 5 / 945 ≤
      1 / s - Real.pi * Real.cot (Real.pi * s) := by
  rw [cot_gap_eq_tsum hs0 hs1, ← tsum_cotGapBaseSummand]
  exact Summable.tsum_le_tsum
    (fun n => by
      rw [cotGapSummand_eq_base_add_remainder hs0 hs1]
      exact le_add_of_nonneg_right (cotGapRemainder_nonneg hs0 hs1 n))
    (summable_cotGapBaseSummand s) (summable_cotGapSummand hs0 hs1)

private lemma cotGap_scaled_upper {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    1 / s - Real.pi * Real.cot (Real.pi * s) ≤
      Real.pi ^ 2 * s / 3 + Real.pi ^ 4 * s ^ 3 / 45 +
        2 * Real.pi ^ 6 * s ^ 5 / 945 +
          Real.pi ^ 8 * s ^ 7 / (4725 * (1 - s ^ 2)) := by
  rw [cot_gap_eq_tsum hs0 hs1, ← tsum_cotGapBaseSummand,
    ← tsum_cotGapRemainderMajorant hs0 hs1]
  rw [← (summable_cotGapBaseSummand s).tsum_add
    (summable_cotGapRemainderMajorant s)]
  exact Summable.tsum_le_tsum
    (fun n => by
      rw [cotGapSummand_eq_base_add_remainder hs0 hs1]
      exact add_le_add le_rfl (cotGapRemainder_le_majorant hs0 hs1 n))
    (summable_cotGapSummand hs0 hs1)
    ((summable_cotGapBaseSummand s).add (summable_cotGapRemainderMajorant s))

/-- The lower polynomial used by `dlow` in the exact checker. -/
def prawitzCotGapLower (x : ℝ) : ℝ :=
  x / 3 + x ^ 3 / 45 + 2 * x ^ 5 / 945

/-- The upper rational expression used by `dup` in the exact checker. -/
def prawitzCotGapUpperAt (s : ℝ) : ℝ :=
  prawitzCotGapLower (Real.pi * s) +
    (Real.pi * s) ^ 7 / (4725 * (1 - s ^ 2))

/-- For `0 ≤ s < 1`, the checker's lower polynomial bounds
`1 / (π s) - cot (π s)` from below. -/
theorem prawitzCotGapLower_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    prawitzCotGapLower (Real.pi * s) ≤
      1 / (Real.pi * s) - Real.cot (Real.pi * s) := by
  by_cases hs : s = 0
  · subst s
    simp [prawitzCotGapLower, Real.cot_eq_cos_div_sin]
  · have hsPos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have h := cotGap_scaled_lower hsPos hs1
    have hgap :
        Real.pi * (1 / (Real.pi * s) - Real.cot (Real.pi * s)) =
          1 / s - Real.pi * Real.cot (Real.pi * s) := by
      field_simp [Real.pi_ne_zero, hs]
    have hlower :
        Real.pi * prawitzCotGapLower (Real.pi * s) =
          Real.pi ^ 2 * s / 3 + Real.pi ^ 4 * s ^ 3 / 45 +
            2 * Real.pi ^ 6 * s ^ 5 / 945 := by
      unfold prawitzCotGapLower
      ring
    rw [← hgap, ← hlower] at h
    exact (mul_le_mul_iff_right₀ Real.pi_pos).mp h

/-- For `0 ≤ s < 1`, the checker's rational expression bounds
`1 / (π s) - cot (π s)` from above. -/
theorem prawitzCotGap_le_upper {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    1 / (Real.pi * s) - Real.cot (Real.pi * s) ≤ prawitzCotGapUpperAt s := by
  by_cases hs : s = 0
  · subst s
    simp [prawitzCotGapUpperAt, prawitzCotGapLower, Real.cot_eq_cos_div_sin]
  · have hsPos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have h := cotGap_scaled_upper hsPos hs1
    have hgap :
        Real.pi * (1 / (Real.pi * s) - Real.cot (Real.pi * s)) =
          1 / s - Real.pi * Real.cot (Real.pi * s) := by
      field_simp [Real.pi_ne_zero, hs]
    have hupper :
        Real.pi * prawitzCotGapUpperAt s =
          Real.pi ^ 2 * s / 3 + Real.pi ^ 4 * s ^ 3 / 45 +
            2 * Real.pi ^ 6 * s ^ 5 / 945 +
              Real.pi ^ 8 * s ^ 7 / (4725 * (1 - s ^ 2)) := by
      have hsden : 1 - s ^ 2 ≠ 0 := by nlinarith
      unfold prawitzCotGapUpperAt prawitzCotGapLower
      field_simp [hsden]
    rw [← hgap, ← hupper] at h
    exact (mul_le_mul_iff_right₀ Real.pi_pos).mp h

end

end BerryEsseen
