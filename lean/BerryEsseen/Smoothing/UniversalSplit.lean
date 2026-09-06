import BerryEsseen.Smoothing.UniversalBound

/-!
# Smoothing / Universal Split
-/

namespace BerryEsseen

open MeasureTheory ProbabilityTheory

noncomputable section

def bound4395TargetConstant : ℝ := (879 : ℝ) / 2000

def bound4395UniversalCutoff : ℝ := (1090 : ℝ) / 879

/-- Exact intended conclusion for the post-`0.44` theorem.  The assumptions
remain theorem-level, exactly as in the the baseline bound and `0.44` interfaces. -/
def IIDBerryEsseen879_2000Conclusion
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (X : ℕ → Omega → ℝ) (rho : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    HasBerryEsseenBound (standardizedSumLaw P X n) rho n
      bound4395TargetConstant

theorem bound4395Target_lt_044 :
    bound4395TargetConstant < (44 : ℝ) / 100 := by
  norm_num [bound4395TargetConstant]

theorem bound4395Target_mul_universalCutoff :
    bound4395TargetConstant * bound4395UniversalCutoff =
      refinedUniversalConstant := by
  norm_num [bound4395TargetConstant, bound4395UniversalCutoff,
    refinedUniversalConstant]

theorem bound4395UniversalCutoff_lt_routeBCutoff :
    bound4395UniversalCutoff < (56 : ℝ) / 45 := by
  norm_num [bound4395UniversalCutoff]

/-- The existing distribution-free `109/200` estimate closes the large-ratio
branch at target `879/2000`.  The statement is generic in the positive scale;
the final i.i.d. assembly will instantiate it with `sqrt n`. -/
theorem bound4395_universal_branch
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 2 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hvariance : Var[(id : ℝ → ℝ); mu] = 1)
    {rho scale : ℝ} (hscale : 0 < scale)
    (hcut : bound4395UniversalCutoff ≤ rho / scale) :
    kolmogorovDistance mu standardNormalLaw ≤
      bound4395TargetConstant * rho / scale := by
  have huniversal := refinedUniversal_kolmogorov_bound
    mu hX hmean hvariance
  calc
    kolmogorovDistance mu standardNormalLaw ≤
        refinedUniversalConstant := huniversal
    _ = bound4395TargetConstant * bound4395UniversalCutoff :=
      bound4395Target_mul_universalCutoff.symm
    _ ≤ bound4395TargetConstant * (rho / scale) :=
      mul_le_mul_of_nonneg_left hcut (by
        norm_num [bound4395TargetConstant])
    _ = bound4395TargetConstant * rho / scale := by ring

/-- The complementary branch lies strictly inside the existing Route B domain
`rho/scale < 56/45`; no parameter-domain or theorem-assumption change is
needed at target `879/2000`. -/
theorem bound4395_complement_inside_routeB
    {rho scale : ℝ} (hscale : 0 < scale)
    (hcut : ¬ bound4395UniversalCutoff ≤ rho / scale) :
    rho < ((56 : ℝ) / 45) * scale := by
  have hsmall : rho / scale < bound4395UniversalCutoff :=
    lt_of_not_ge hcut
  have hroute : rho / scale < (56 : ℝ) / 45 :=
    hsmall.trans bound4395UniversalCutoff_lt_routeBCutoff
  exact (div_lt_iff₀ hscale).1 hroute

end

end BerryEsseen
