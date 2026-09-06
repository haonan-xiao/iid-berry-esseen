import BerryEsseen.MomentGeometry

/-!
# Moments / First Absolute Moment
-/

namespace BerryEsseen

open MeasureTheory

noncomputable section

/-- Log-convexity of absolute moments at exponents `1,2,3`, specialized to
variance one.  This is the exact inequality `1 ≤ (E|X|) (E|X|^3)` used by
the first-absolute-moment bounds. -/
theorem one_le_firstAbsoluteMoment_mul_thirdAbsoluteMoment
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    1 ≤ (∫ x : ℝ, |x| ∂mu) * thirdAbsoluteMoment mu := by
  have hlog : (∫ x : ℝ, |x| ^ 2 ∂mu) ^ 2 ≤
      (∫ x : ℝ, |x| ∂mu) * ∫ x : ℝ, |x| ^ 3 ∂mu := by
    simpa only [id_eq, Real.norm_eq_abs] using
      secondMoment_sq_le_first_mul_third mu hX.norm
        (fun x : ℝ => abs_nonneg x)
  have hsquare : (∫ x : ℝ, |x| ^ 2 ∂mu) = 1 := by
    calc
      (∫ x : ℝ, |x| ^ 2 ∂mu) = ∫ x : ℝ, x ^ 2 ∂mu := by
        apply integral_congr_ae
        exact ae_of_all mu fun x => sq_abs x
      _ = 1 := hsecond
  rw [hsquare] at hlog
  simpa [thirdAbsoluteMoment] using hlog

/-- The accepted stop-loss/symmetrization estimate, rearranged in the exact
form needed by the new coordinate: `rho (r-1) ≤ E|X|`. -/
theorem thirdAbsoluteMoment_mul_ratioExcess_le_firstAbsoluteMoment
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1) ≤
      ∫ x : ℝ, |x| ∂mu := by
  have hrho : 1 ≤ thirdAbsoluteMoment mu :=
    thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < thirdAbsoluteMoment mu :=
    lt_of_lt_of_le zero_lt_one hrho
  have hratio := symmetrizationRatio_upper_absMoment mu hX hmean hsecond
  have hexcess : symmetrizationRatio mu - 1 ≤
      (∫ x : ℝ, |x| ∂mu) / thirdAbsoluteMoment mu := by
    linarith
  calc
    thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1) ≤
        thirdAbsoluteMoment mu *
          ((∫ x : ℝ, |x| ∂mu) / thirdAbsoluteMoment mu) :=
      mul_le_mul_of_nonneg_left hexcess hrhoPos.le
    _ = ∫ x : ℝ, |x| ∂mu := by field_simp

/-- Under exactly the classical centered variance-one third-moment
assumptions, `d = 1-E|X|` is nonnegative and is bounded by both scalar
constraints used by the the first-absolute-moment bounds checker. -/
theorem radialDefect_constraints
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    let s := ∫ x : ℝ, |x| ∂mu
    let rho := thirdAbsoluteMoment mu
    let r := symmetrizationRatio mu
    0 ≤ 1 - s ∧
      1 - s ≤ 1 - 1 / rho ∧
      1 - s ≤ 1 - rho * (r - 1) := by
  let s := ∫ x : ℝ, |x| ∂mu
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  have hsUpper : s ≤ 1 := by
    simpa only [s] using first_absolute_moment_le_one mu hX hsecond
  have hrho : 1 ≤ rho := by
    simpa only [rho] using thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < rho := lt_of_lt_of_le zero_lt_one hrho
  have hproduct : 1 ≤ s * rho := by
    simpa only [s, rho] using
      one_le_firstAbsoluteMoment_mul_thirdAbsoluteMoment mu hX hsecond
  have hinv : 1 / rho ≤ s := by
    exact (div_le_iff₀ hrhoPos).2 (by simpa [mul_comm] using hproduct)
  have hratio : rho * (r - 1) ≤ s := by
    simpa only [rho, r, s] using
      thirdAbsoluteMoment_mul_ratioExcess_le_firstAbsoluteMoment
        mu hX hmean hsecond
  dsimp only [s, rho, r]
  constructor
  · linarith
  constructor <;> linarith

end

end BerryEsseen
