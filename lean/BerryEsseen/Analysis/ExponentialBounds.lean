import BerryEsseen.Smoothing.Prawitz.LargeNSmallOmission

namespace BerryEsseen

open DyadicInterval

/-- A kernel-checked replacement for the native dyadic endpoint computation.
The fourth Taylor polynomial gives `exp 1 ≥ 65/24`; raising to the 32nd
power already clears `7 * 10^13`. -/
theorem expNegThirtyTwoLe :
    Real.exp (-32) ≤ (1 : ℝ) / 70000000000000 := by
  have hexpOne : (65 : ℝ) / 24 ≤ Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 5
    norm_num [Finset.sum_range_succ] at h ⊢
    exact h
  have hpow : ((65 : ℝ) / 24) ^ 32 ≤ (Real.exp 1) ^ 32 := by
    gcongr
  have hnumeric : (70000000000000 : ℝ) ≤ ((65 : ℝ) / 24) ^ 32 := by
    norm_num
  have hexpThirtyTwo :
      (70000000000000 : ℝ) ≤ Real.exp 32 := by
    calc
      (70000000000000 : ℝ) ≤ ((65 : ℝ) / 24) ^ 32 := hnumeric
      _ ≤ (Real.exp 1) ^ 32 := hpow
      _ = Real.exp 32 := by
        simpa using (Real.exp_nat_mul (1 : ℝ) 32).symm
  have hrecip :
      1 / Real.exp 32 ≤ (1 : ℝ) / 70000000000000 :=
    one_div_le_one_div_of_le (by norm_num) hexpThirtyTwo
  simpa [Real.exp_neg] using hrecip

end BerryEsseen
