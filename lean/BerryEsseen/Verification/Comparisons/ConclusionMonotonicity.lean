import BerryEsseen.Theorems.NumericalAssembly
import BerryEsseen.Verification.Comparisons.CertificateImplication

/-!
# Verification / Comparisons / Conclusion Monotonicity
-/

namespace BerryEsseen

open MeasureTheory

theorem bound4395Target_lt_baselineTarget :
    bound4395TargetConstant < targetConstant := by
  norm_num [bound4395TargetConstant, targetConstant]

theorem bound4395Target_lt_intermediateTarget :
    bound4395TargetConstant < targetConstant044 := by
  norm_num [bound4395TargetConstant, targetConstant044]

theorem IIDBerryEsseen879_2000Conclusion_implies_45
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (X : ℕ → Omega → ℝ) {rho : ℝ}
    (hrho : 0 ≤ rho)
    (h879 : IIDBerryEsseen879_2000Conclusion P X rho) :
    IIDBerryEsseen45Conclusion P X rho := by
  intro n hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  have hmul : bound4395TargetConstant * rho ≤ targetConstant * rho :=
    mul_le_mul_of_nonneg_right bound4395Target_lt_baselineTarget.le hrho
  have hrate :
      normalizedRate bound4395TargetConstant rho n ≤
        normalizedRate targetConstant rho n := by
    simpa only [normalizedRate] using
      (div_le_div_of_nonneg_right hmul hsqrt.le)
  exact (h879 n hn).trans hrate

theorem IIDBerryEsseen879_2000Conclusion_implies_44
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (X : ℕ → Omega → ℝ) {rho : ℝ}
    (hrho : 0 ≤ rho)
    (h879 : IIDBerryEsseen879_2000Conclusion P X rho) :
    IIDBerryEsseen44Conclusion P X rho := by
  intro n hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  have hmul : bound4395TargetConstant * rho ≤ targetConstant044 * rho :=
    mul_le_mul_of_nonneg_right bound4395Target_lt_intermediateTarget.le hrho
  have hrate :
      normalizedRate bound4395TargetConstant rho n ≤
        normalizedRate targetConstant044 rho n := by
    simpa only [normalizedRate] using
      (div_le_div_of_nonneg_right hmul hsqrt.le)
  exact (h879 n hn).trans hrate

#print axioms BerryEsseen.bound4395Target_lt_baselineTarget
#print axioms BerryEsseen.bound4395Target_lt_intermediateTarget
#print axioms BerryEsseen.IIDBerryEsseen879_2000Conclusion_implies_45
#print axioms BerryEsseen.IIDBerryEsseen879_2000Conclusion_implies_44

end BerryEsseen
