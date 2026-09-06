import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Exact constants used by Route B

Decimal constants from the supplied proof are represented by exact rational numbers.
-/

namespace BerryEsseen

/-- The claimed Berry--Esseen constant, `0.45`. -/
noncomputable def targetConstant : ℝ := (45 : ℝ) / 100

/-- The stricter constant proved by the numerical certificate, `0.4495`. -/
noncomputable def certificateConstant : ℝ := (4495 : ℝ) / 10000

/-- The distribution-free cutoff bound, `0.56`. -/
noncomputable def universalConstant : ℝ := (14 : ℝ) / 25

/-- The cutoff for `ρ / √n`. -/
noncomputable def cutoff : ℝ := (56 : ℝ) / 45

/-- The Prawitz splitting point used by Route B. -/
noncomputable def prawitzSplit : ℝ := (19 : ℝ) / 50

theorem certificateConstant_lt_targetConstant :
    certificateConstant < targetConstant := by
  norm_num [certificateConstant, targetConstant]

theorem universalConstant_eq_target_mul_cutoff :
    universalConstant = targetConstant * cutoff := by
  norm_num [universalConstant, targetConstant, cutoff]

theorem targetConstant_pos : 0 < targetConstant := by
  norm_num [targetConstant]

theorem cutoff_pos : 0 < cutoff := by
  norm_num [cutoff]

end BerryEsseen
