import BerryEsseen.Probability.Universal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Conditional final assembly

The theorems in this module are deliberately named `conditional`: they prove the final constant
from the universal branch and the L1/L2 numerical boundary, but do not pretend that the L2
certificate verification has already been discharged. The concrete analytic reduction is proved
in `ExplicitSmoothing.lean`.
-/

open MeasureTheory ProbabilityTheory

namespace BerryEsseen

/-- Exact two-branch arithmetic behind `0.56`/`0.4495` and the final `0.45`. -/
theorem conditional_scalar_assembly {Delta L : ℝ} (hL : 0 ≤ L)
    (hUniversal : cutoff ≤ L → Delta ≤ universalConstant)
    (hCertified : L < cutoff → Delta ≤ certificateConstant * L) :
    Delta ≤ targetConstant * L := by
  by_cases hcut : cutoff ≤ L
  · calc
      Delta ≤ universalConstant := hUniversal hcut
      _ = targetConstant * cutoff := universalConstant_eq_target_mul_cutoff
      _ ≤ targetConstant * L := mul_le_mul_of_nonneg_left hcut targetConstant_pos.le
  · have hsmall : L < cutoff := lt_of_not_ge hcut
    calc
      Delta ≤ certificateConstant * L := hCertified hsmall
      _ ≤ targetConstant * L :=
        mul_le_mul_of_nonneg_right certificateConstant_lt_targetConstant.le hL

/-- L1 assembly with the numerical lemma kept as an explicit theorem parameter.  This result is
conditional until `CertifiedNumericalBound U` is proved from a Lean-checkable certificate. -/
theorem conditional_target_of_numerical_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (U : ℕ → ℝ → ℝ → ℝ) {n : ℕ} {rho r : ℝ}
    (hn : 1 ≤ n) (hrho : 1 ≤ rho) (hrLower : 1 ≤ r)
    (hrUpper : r ≤ 1 + 1 / rho)
    (hNumerical : CertifiedNumericalBound U)
    (hUniversal : kolmogorovDistance mu standardNormalLaw ≤ universalConstant)
    (hReduction : rho / Real.sqrt (n : ℝ) < cutoff →
      kolmogorovDistance mu standardNormalLaw ≤ U n rho r) :
    HasBerryEsseenBound mu rho n targetConstant := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  have hL : 0 ≤ rho / Real.sqrt (n : ℝ) :=
    div_nonneg (by linarith [hrho]) hsqrt.le
  unfold HasBerryEsseenBound normalizedRate
  rw [mul_div_assoc]
  apply conditional_scalar_assembly hL
  · intro _
    exact hUniversal
  · intro hsmall
    calc
      kolmogorovDistance mu standardNormalLaw ≤ U n rho r := hReduction hsmall
      _ ≤ certificateConstant * rho / Real.sqrt (n : ℝ) := by
        exact hNumerical n rho r
          { n_lower := hn
            rho_lower := hrho
            rho_upper := (le_of_lt ((div_lt_iff₀ hsqrt).1 hsmall))
            r_lower := hrLower
            r_upper := hrUpper }
      _ = certificateConstant * (rho / Real.sqrt (n : ℝ)) := by ring

/-- The same conditional target with the universal branch discharged from centered
variance-one moments. The concrete Route B reduction can discharge `hReduction`; the remaining
unconditional theorem still requires the scalar L2 numerical certificate and normalized-sum
packaging. -/
theorem conditional_target_of_moments_and_numerical_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (U : ℕ → ℝ → ℝ → ℝ) {n : ℕ} {rho r : ℝ}
    (hX : MemLp (id : ℝ → ℝ) 2 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hvariance : Var[(id : ℝ → ℝ); mu] = 1)
    (hn : 1 ≤ n) (hrho : 1 ≤ rho) (hrLower : 1 ≤ r)
    (hrUpper : r ≤ 1 + 1 / rho)
    (hNumerical : CertifiedNumericalBound U)
    (hReduction : rho / Real.sqrt (n : ℝ) < cutoff →
      kolmogorovDistance mu standardNormalLaw ≤ U n rho r) :
    HasBerryEsseenBound mu rho n targetConstant := by
  exact conditional_target_of_numerical_bound mu U hn hrho hrLower hrUpper hNumerical
    (universal_kolmogorov_bound mu hX hmean hvariance) hReduction

end BerryEsseen
