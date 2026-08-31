import BerryEsseen.Probability.Universal
import StatLean.AsymptoticStatistics.ForMathlib.L2
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Stop-loss and moment geometry

This module begins the smoothing branch of Route B.  It fixes source-native positive and negative
parts, their moments, and the moment identities used by the stop-loss argument.  The law itself is
the probability measure on `R`; independent copies will later live on its product measure.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

namespace BerryEsseen

noncomputable section

/-- The positive part `x_+`. -/
def positivePart (x : ℝ) : ℝ := max x 0

/-- The negative part `x_- = (-x)_+`. -/
def negativePart (x : ℝ) : ℝ := max (-x) 0

/-- The `k`-th positive-part moment. -/
def positiveMoment (mu : Measure ℝ) (k : ℕ) : ℝ :=
  ∫ x, positivePart x ^ k ∂mu

/-- The `k`-th negative-part moment. -/
def negativeMoment (mu : Measure ℝ) (k : ℕ) : ℝ :=
  ∫ x, negativePart x ^ k ∂mu

/-- The positive stop-loss transform `A(t) = E (X-t)_+`. -/
def positiveStopLoss (mu : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ x, positivePart (x - t) ∂mu

/-- The negative stop-loss transform `B(t) = E (-X-t)_+`. -/
def negativeStopLoss (mu : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ x, positivePart (-x - t) ∂mu

/-- The complementary stop-loss transform `E (t-X)₊`. -/
def reverseStopLoss (mu : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ x, positivePart (t - x) ∂mu

/-- The third absolute moment of the difference of two independent copies. -/
def symmetrizedThirdAbsoluteMoment (mu : Measure ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, |p.1 - p.2| ^ 3 ∂mu.prod mu

/-- The (signed) third raw moment. -/
def rawThirdMoment (mu : Measure ℝ) : ℝ :=
  ∫ x : ℝ, x ^ 3 ∂mu

/-- Route B's normalized symmetrization parameter `r = E|X-X'|³ / (2 E|X|³)`. -/
def symmetrizationRatio (mu : Measure ℝ) : ℝ :=
  symmetrizedThirdAbsoluteMoment mu / (2 * thirdAbsoluteMoment mu)

theorem positivePart_nonneg (x : ℝ) : 0 ≤ positivePart x := by
  simp [positivePart]

theorem negativePart_nonneg (x : ℝ) : 0 ≤ negativePart x := by
  simp [negativePart]

theorem positivePart_sub_negativePart (x : ℝ) :
    positivePart x - negativePart x = x := by
  by_cases hx : 0 ≤ x
  · simp [positivePart, negativePart, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [positivePart, negativePart, max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]

theorem positivePart_add_negativePart (x : ℝ) :
    positivePart x + negativePart x = |x| := by
  by_cases hx : 0 ≤ x
  · simp [positivePart, negativePart, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx),
      abs_of_nonneg hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [positivePart, negativePart, max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'),
      abs_of_nonpos hx']

theorem positivePart_mul_negativePart (x : ℝ) :
    positivePart x * negativePart x = 0 := by
  by_cases hx : 0 ≤ x
  · simp [positivePart, negativePart, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [positivePart, negativePart, max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]

theorem positivePart_sq_add_negativePart_sq (x : ℝ) :
    positivePart x ^ 2 + negativePart x ^ 2 = x ^ 2 := by
  calc
    positivePart x ^ 2 + negativePart x ^ 2
        = (positivePart x - negativePart x) ^ 2 := by
          nlinarith [positivePart_mul_negativePart x]
    _ = x ^ 2 := by rw [positivePart_sub_negativePart]

theorem positivePart_cube_add_negativePart_cube (x : ℝ) :
    positivePart x ^ 3 + negativePart x ^ 3 = |x| ^ 3 := by
  have hprod := positivePart_mul_negativePart x
  have hleft : positivePart x ^ 2 * negativePart x = 0 := by
    rw [pow_two, mul_assoc, hprod, mul_zero]
  have hright : positivePart x * negativePart x ^ 2 = 0 := by
    rw [pow_two, ← mul_assoc, hprod, zero_mul]
  calc
    positivePart x ^ 3 + negativePart x ^ 3
        = (positivePart x + negativePart x) ^ 3 := by
          ring_nf
          linarith
    _ = |x| ^ 3 := by rw [positivePart_add_negativePart]

theorem positivePart_cube_sub_negativePart_cube (x : ℝ) :
    positivePart x ^ 3 - negativePart x ^ 3 = x ^ 3 := by
  have hprod := positivePart_mul_negativePart x
  have hleft : positivePart x ^ 2 * negativePart x = 0 := by
    rw [pow_two, mul_assoc, hprod, mul_zero]
  have hright : positivePart x * negativePart x ^ 2 = 0 := by
    rw [pow_two, ← mul_assoc, hprod, zero_mul]
  calc
    positivePart x ^ 3 - negativePart x ^ 3
        = (positivePart x - negativePart x) ^ 3 := by
          ring_nf
          linarith
    _ = x ^ 3 := by rw [positivePart_sub_negativePart]

theorem memLp_positivePart {mu : Measure ℝ} {p : ℝ≥0∞}
    (hX : MemLp (id : ℝ → ℝ) p mu) : MemLp positivePart p mu := by
  simpa only [positivePart, id_eq] using hX.pos_part

theorem memLp_negativePart {mu : Measure ℝ} {p : ℝ≥0∞}
    (hX : MemLp (id : ℝ → ℝ) p mu) : MemLp negativePart p mu := by
  simpa only [negativePart, id_eq] using hX.neg_part

theorem integrable_positivePart {mu : Measure ℝ} [IsFiniteMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) : Integrable positivePart mu :=
  (memLp_positivePart hX).integrable (by norm_num)

theorem integrable_negativePart {mu : Measure ℝ} [IsFiniteMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) : Integrable negativePart mu :=
  (memLp_negativePart hX).integrable (by norm_num)

theorem integrable_positivePart_sq {mu : Measure ℝ} [IsFiniteMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    Integrable (fun x => positivePart x ^ 2) mu := by
  exact ((memLp_positivePart hX).mono_exponent (by norm_num)).integrable_sq

theorem integrable_negativePart_sq {mu : Measure ℝ} [IsFiniteMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    Integrable (fun x => negativePart x ^ 2) mu := by
  exact ((memLp_negativePart hX).mono_exponent (by norm_num)).integrable_sq

theorem integrable_positivePart_cube {mu : Measure ℝ}
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    Integrable (fun x => positivePart x ^ 3) mu := by
  have h := (memLp_positivePart hX).integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
  simpa only [Real.norm_of_nonneg, positivePart_nonneg] using h

theorem integrable_negativePart_cube {mu : Measure ℝ}
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    Integrable (fun x => negativePart x ^ 3) mu := by
  have h := (memLp_negativePart hX).integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
  simpa only [Real.norm_of_nonneg, negativePart_nonneg] using h

theorem centered_first_part_moments_eq
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0) :
    positiveMoment mu 1 = negativeMoment mu 1 := by
  have hdecomp : (∫ x : ℝ, x ∂mu) =
      (∫ x, positivePart x ∂mu) - ∫ x, negativePart x ∂mu := by
    calc
      (∫ x : ℝ, x ∂mu) = ∫ x, positivePart x - negativePart x ∂mu := by
        apply integral_congr_ae
        exact ae_of_all mu fun x => (positivePart_sub_negativePart x).symm
      _ = (∫ x, positivePart x ∂mu) - ∫ x, negativePart x ∂mu := by
        rw [integral_sub (integrable_positivePart hX) (integrable_negativePart hX)]
  unfold positiveMoment negativeMoment
  simp only [pow_one]
  linarith

theorem first_absolute_part_moments_add
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    positiveMoment mu 1 + negativeMoment mu 1 = ∫ x : ℝ, |x| ∂mu := by
  unfold positiveMoment negativeMoment
  simp only [pow_one]
  rw [← integral_add (integrable_positivePart hX) (integrable_negativePart hX)]
  apply integral_congr_ae
  exact ae_of_all mu positivePart_add_negativePart

theorem second_part_moments_add
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    positiveMoment mu 2 + negativeMoment mu 2 = ∫ x : ℝ, x ^ 2 ∂mu := by
  unfold positiveMoment negativeMoment
  rw [← integral_add (integrable_positivePart_sq hX) (integrable_negativePart_sq hX)]
  apply integral_congr_ae
  exact ae_of_all mu positivePart_sq_add_negativePart_sq

theorem third_absolute_part_moments_add
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    positiveMoment mu 3 + negativeMoment mu 3 = thirdAbsoluteMoment mu := by
  unfold positiveMoment negativeMoment thirdAbsoluteMoment
  rw [← integral_add (integrable_positivePart_cube hX) (integrable_negativePart_cube hX)]
  apply integral_congr_ae
  exact ae_of_all mu positivePart_cube_add_negativePart_cube

theorem third_raw_part_moments_sub
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    positiveMoment mu 3 - negativeMoment mu 3 = ∫ x : ℝ, x ^ 3 ∂mu := by
  unfold positiveMoment negativeMoment
  rw [← integral_sub (integrable_positivePart_cube hX) (integrable_negativePart_cube hX)]
  apply integral_congr_ae
  exact ae_of_all mu positivePart_cube_sub_negativePart_cube

theorem positiveMoment_nonneg (mu : Measure ℝ) (k : ℕ) :
    0 ≤ positiveMoment mu k := by
  exact integral_nonneg fun x => pow_nonneg (positivePart_nonneg x) k

theorem negativeMoment_nonneg (mu : Measure ℝ) (k : ℕ) :
    0 ≤ negativeMoment mu k := by
  exact integral_nonneg fun x => pow_nonneg (negativePart_nonneg x) k

/-- A centered, variance-one law has strictly positive mass in first positive-part moment. -/
theorem positive_firstMoment_pos
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    0 < positiveMoment mu 1 := by
  have hnonneg : 0 ≤ positiveMoment mu 1 := positiveMoment_nonneg mu 1
  by_contra hnot
  have hzero : positiveMoment mu 1 = 0 :=
    le_antisymm (le_of_not_gt hnot) hnonneg
  have hparts := centered_first_part_moments_eq mu hX hmean
  have hnegativeZero : negativeMoment mu 1 = 0 := by
    rw [← hparts, hzero]
  have hpositiveIntegral : ∫ x, positivePart x ∂mu = 0 := by
    simpa only [positiveMoment, pow_one] using hzero
  have hnegativeIntegral : ∫ x, negativePart x ∂mu = 0 := by
    simpa only [negativeMoment, pow_one] using hnegativeZero
  have hpositiveAE : positivePart =ᵐ[mu] 0 :=
    (integral_eq_zero_iff_of_nonneg positivePart_nonneg
      (integrable_positivePart hX)).1 hpositiveIntegral
  have hnegativeAE : negativePart =ᵐ[mu] 0 :=
    (integral_eq_zero_iff_of_nonneg negativePart_nonneg
      (integrable_negativePart hX)).1 hnegativeIntegral
  have hidAE : (id : ℝ → ℝ) =ᵐ[mu] 0 := by
    filter_upwards [hpositiveAE, hnegativeAE] with x hxpositive hxnegative
    simp only [Pi.zero_apply] at hxpositive hxnegative ⊢
    change x = 0
    linarith [positivePart_sub_negativePart x]
  have hsquareAE : (fun x : ℝ => x ^ 2) =ᵐ[mu] 0 := by
    filter_upwards [hidAE] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    change x = 0 at hx
    simp [hx]
  have hsecondZero : ∫ x : ℝ, x ^ 2 ∂mu = 0 := by
    calc
      (∫ x : ℝ, x ^ 2 ∂mu) = ∫ _x : ℝ, (0 : ℝ) ∂mu :=
        integral_congr_ae hsquareAE
      _ = 0 := by simp
  linarith

/-- Moment log-convexity at exponents `1,2,3`, proved directly by Cauchy--Schwarz. -/
theorem secondMoment_sq_le_first_mul_third
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    {Y : Omega → ℝ} (hY : MemLp Y 3 P)
    (hYnonneg : ∀ omega, 0 ≤ Y omega) :
    (∫ omega, Y omega ^ 2 ∂P) ^ 2 ≤
      (∫ omega, Y omega ∂P) * ∫ omega, Y omega ^ 3 ∂P := by
  have hY1 : Integrable Y P := hY.integrable (by norm_num)
  have hY3 : Integrable (fun omega => Y omega ^ 3) P := by
    have h := hY.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [Real.norm_of_nonneg, hYnonneg] using h
  let f : Omega → ℝ := fun omega => Real.sqrt (Y omega)
  let g : Omega → ℝ := fun omega => Y omega * Real.sqrt (Y omega)
  have hf : MemLp f 2 P := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    have heq : (fun omega => f omega ^ 2) = Y := by
      funext omega
      dsimp [f]
      exact Real.sq_sqrt (hYnonneg omega)
    rw [heq]
    exact hY1
  have hg : MemLp g 2 P := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    have heq : (fun omega => g omega ^ 2) = fun omega => Y omega ^ 3 := by
      funext omega
      dsimp [g]
      rw [mul_pow, Real.sq_sqrt (hYnonneg omega)]
      ring
    rw [heq]
    exact hY3
  have hcs := AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq P hf hg
  have hfg : (fun omega => f omega * g omega) = fun omega => Y omega ^ 2 := by
    funext omega
    dsimp [f, g]
    calc
      Real.sqrt (Y omega) * (Y omega * Real.sqrt (Y omega)) =
          Y omega * (Real.sqrt (Y omega) * Real.sqrt (Y omega)) := by ring
      _ = Y omega * Y omega := by rw [Real.mul_self_sqrt (hYnonneg omega)]
      _ = Y omega ^ 2 := by ring
  have hff : (fun omega => f omega ^ 2) = Y := by
    funext omega
    dsimp [f]
    exact Real.sq_sqrt (hYnonneg omega)
  have hgg : (fun omega => g omega ^ 2) = fun omega => Y omega ^ 3 := by
    funext omega
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt (hYnonneg omega)]
    ring
  rw [hfg, hff, hgg] at hcs
  have hsecondNonneg : 0 ≤ ∫ omega, Y omega ^ 2 ∂P :=
    integral_nonneg fun omega => sq_nonneg (Y omega)
  rw [abs_of_nonneg hsecondNonneg] at hcs
  have hfirstNonneg : 0 ≤ ∫ omega, Y omega ∂P :=
    integral_nonneg hYnonneg
  have hthirdNonneg : 0 ≤ ∫ omega, Y omega ^ 3 ∂P :=
    integral_nonneg fun omega => pow_nonneg (hYnonneg omega) 3
  calc
    (∫ omega, Y omega ^ 2 ∂P) ^ 2
        ≤ (Real.sqrt (∫ omega, Y omega ∂P) *
            Real.sqrt (∫ omega, Y omega ^ 3 ∂P)) ^ 2 := by
          simpa only [pow_two] using mul_self_le_mul_self hsecondNonneg hcs
    _ = (∫ omega, Y omega ∂P) * ∫ omega, Y omega ^ 3 ∂P := by
      rw [mul_pow, Real.sq_sqrt hfirstNonneg, Real.sq_sqrt hthirdNonneg]

theorem positive_secondMoment_sq_le
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    positiveMoment mu 2 ^ 2 ≤ positiveMoment mu 1 * positiveMoment mu 3 := by
  simpa only [positiveMoment, pow_one] using
    secondMoment_sq_le_first_mul_third mu (memLp_positivePart hX) positivePart_nonneg

theorem negative_secondMoment_sq_le
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    negativeMoment mu 2 ^ 2 ≤ negativeMoment mu 1 * negativeMoment mu 3 := by
  simpa only [negativeMoment, pow_one] using
    secondMoment_sq_le_first_mul_third mu (memLp_negativePart hX) negativePart_nonneg

/-- The covariance determinant inequality for the disjoint positive and negative parts. -/
theorem first_part_moment_sq_le_second_product
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    positiveMoment mu 1 ^ 2 ≤ positiveMoment mu 2 * negativeMoment mu 2 := by
  have hpositive2 : MemLp positivePart 2 mu :=
    (memLp_positivePart hX).mono_exponent (by norm_num)
  have hnegative2 : MemLp negativePart 2 mu :=
    (memLp_negativePart hX).mono_exponent (by norm_num)
  have hfirst := centered_first_part_moments_eq mu hX hmean
  have hcrossZero : ∫ x, positivePart x * negativePart x ∂mu = 0 := by
    calc
      (∫ x, positivePart x * negativePart x ∂mu) = ∫ _x : ℝ, (0 : ℝ) ∂mu := by
        apply integral_congr_ae
        exact ae_of_all mu positivePart_mul_negativePart
      _ = 0 := by simp
  have hcrossZero' : ∫ x, (positivePart * negativePart) x ∂mu = 0 := by
    simpa only [Pi.mul_apply] using hcrossZero
  have hcovCross : cov[positivePart, negativePart; mu] =
      -(positiveMoment mu 1) ^ 2 := by
    rw [covariance_eq_sub hpositive2 hnegative2, hcrossZero']
    unfold positiveMoment negativeMoment at hfirst
    unfold positiveMoment
    simp only [pow_one] at hfirst ⊢
    rw [← hfirst]
    ring
  have hcovPositive : cov[positivePart, positivePart; mu] =
      positiveMoment mu 2 - positiveMoment mu 1 ^ 2 := by
    rw [covariance_eq_sub hpositive2 hpositive2]
    unfold positiveMoment
    simp only [Pi.mul_apply, pow_one, pow_two]
  have hcovNegative : cov[negativePart, negativePart; mu] =
      negativeMoment mu 2 - positiveMoment mu 1 ^ 2 := by
    rw [covariance_eq_sub hnegative2 hnegative2]
    unfold positiveMoment negativeMoment at hfirst ⊢
    simp only [Pi.mul_apply, pow_one, pow_two] at hfirst ⊢
    rw [hfirst]
  have hcenteredPositive :
      MemLp (fun x => positivePart x - ∫ y, positivePart y ∂mu) 2 mu :=
    hpositive2.sub (memLp_const _)
  have hcenteredNegative :
      MemLp (fun x => negativePart x - ∫ y, negativePart y ∂mu) 2 mu :=
    hnegative2.sub (memLp_const _)
  have hcsRaw :=
    AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq
      mu hcenteredPositive hcenteredNegative
  have hcs : |cov[positivePart, negativePart; mu]| ≤
      Real.sqrt cov[positivePart, positivePart; mu] *
        Real.sqrt cov[negativePart, negativePart; mu] := by
    simpa only [covariance, pow_two] using hcsRaw
  have hcovPositiveNonneg : 0 ≤ cov[positivePart, positivePart; mu] := by
    rw [covariance]
    exact integral_nonneg fun x => mul_self_nonneg _
  have hcovNegativeNonneg : 0 ≤ cov[negativePart, negativePart; mu] := by
    rw [covariance]
    exact integral_nonneg fun x => mul_self_nonneg _
  rw [hcovCross, hcovPositive, hcovNegative] at hcs
  rw [hcovPositive] at hcovPositiveNonneg
  rw [hcovNegative] at hcovNegativeNonneg
  have hleft : |-(positiveMoment mu 1) ^ 2| = positiveMoment mu 1 ^ 2 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg (positiveMoment mu 1))]
  rw [hleft] at hcs
  have hsquared : (positiveMoment mu 1 ^ 2) ^ 2 ≤
      (positiveMoment mu 2 - positiveMoment mu 1 ^ 2) *
        (negativeMoment mu 2 - positiveMoment mu 1 ^ 2) := by
    calc
      (positiveMoment mu 1 ^ 2) ^ 2 ≤
          (Real.sqrt (positiveMoment mu 2 - positiveMoment mu 1 ^ 2) *
            Real.sqrt (negativeMoment mu 2 - positiveMoment mu 1 ^ 2)) ^ 2 := by
        simpa only [pow_two] using
          mul_self_le_mul_self (sq_nonneg (positiveMoment mu 1)) hcs
      _ = (positiveMoment mu 2 - positiveMoment mu 1 ^ 2) *
          (negativeMoment mu 2 - positiveMoment mu 1 ^ 2) := by
        rw [mul_pow, Real.sq_sqrt hcovPositiveNonneg,
          Real.sq_sqrt hcovNegativeNonneg]
  have hsecondParts := second_part_moments_add mu hX
  rw [hsecond] at hsecondParts
  nlinarith

/-- The common first positive/negative moment is controlled by the geometric mean of the
third positive/negative moments. -/
theorem positive_firstMoment_le_sqrt_third_product
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    positiveMoment mu 1 ≤
      Real.sqrt (positiveMoment mu 3 * negativeMoment mu 3) := by
  have hfirstPositive := positive_firstMoment_pos mu hX hmean hsecond
  have hfirstNonneg : 0 ≤ positiveMoment mu 1 := hfirstPositive.le
  have hthirdPositiveNonneg : 0 ≤ positiveMoment mu 3 := positiveMoment_nonneg mu 3
  have hthirdNegativeNonneg : 0 ≤ negativeMoment mu 3 := negativeMoment_nonneg mu 3
  have hthirdProductNonneg :
      0 ≤ positiveMoment mu 3 * negativeMoment mu 3 :=
    mul_nonneg hthirdPositiveNonneg hthirdNegativeNonneg
  have hsecondProduct :=
    first_part_moment_sq_le_second_product mu hX hmean hsecond
  have hpositiveCauchy := positive_secondMoment_sq_le mu hX
  have hnegativeCauchy := negative_secondMoment_sq_le mu hX
  have hfirstEq := centered_first_part_moments_eq mu hX hmean
  rw [← hfirstEq] at hnegativeCauchy
  have hsecondProductSquared :
      positiveMoment mu 1 ^ 2 * positiveMoment mu 1 ^ 2 ≤
        (positiveMoment mu 2 * negativeMoment mu 2) *
          (positiveMoment mu 2 * negativeMoment mu 2) := by
    exact mul_le_mul hsecondProduct hsecondProduct (sq_nonneg _)
      (le_trans (sq_nonneg _) hsecondProduct)
  have hcauchyProduct :
      positiveMoment mu 2 ^ 2 * negativeMoment mu 2 ^ 2 ≤
        (positiveMoment mu 1 * positiveMoment mu 3) *
          (positiveMoment mu 1 * negativeMoment mu 3) := by
    exact mul_le_mul hpositiveCauchy hnegativeCauchy (sq_nonneg _)
      (mul_nonneg hfirstNonneg hthirdPositiveNonneg)
  have hcancelReady :
      positiveMoment mu 1 ^ 2 * positiveMoment mu 1 ^ 2 ≤
        positiveMoment mu 1 ^ 2 *
          (positiveMoment mu 3 * negativeMoment mu 3) := by
    calc
      positiveMoment mu 1 ^ 2 * positiveMoment mu 1 ^ 2 ≤
          (positiveMoment mu 2 * negativeMoment mu 2) *
            (positiveMoment mu 2 * negativeMoment mu 2) := hsecondProductSquared
      _ = positiveMoment mu 2 ^ 2 * negativeMoment mu 2 ^ 2 := by ring
      _ ≤ (positiveMoment mu 1 * positiveMoment mu 3) *
          (positiveMoment mu 1 * negativeMoment mu 3) := hcauchyProduct
      _ = positiveMoment mu 1 ^ 2 *
          (positiveMoment mu 3 * negativeMoment mu 3) := by ring
  have hfirstSquarePositive : 0 < positiveMoment mu 1 ^ 2 := by positivity
  have hthirdBound : positiveMoment mu 1 ^ 2 ≤
      positiveMoment mu 3 * negativeMoment mu 3 :=
    le_of_mul_le_mul_left hcancelReady hfirstSquarePositive
  have hsqrtSquare := Real.sq_sqrt hthirdProductNonneg
  have hsqrtNonneg := Real.sqrt_nonneg (positiveMoment mu 3 * negativeMoment mu 3)
  nlinarith

theorem first_absolute_moment_le_one
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    (∫ x : ℝ, |x| ∂mu) ≤ 1 := by
  have hX2 : MemLp (id : ℝ → ℝ) 2 mu := hX.mono_exponent (by norm_num)
  have habs2 : MemLp (fun x : ℝ => |x|) 2 mu := by
    simpa only [id_eq, Real.norm_eq_abs] using hX2.norm
  have hone2 : MemLp (fun _x : ℝ => (1 : ℝ)) 2 mu := memLp_const 1
  have hcs := AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq
    mu habs2 hone2
  have habsSquare : (∫ x : ℝ, |x| ^ 2 ∂mu) = ∫ x : ℝ, x ^ 2 ∂mu := by
    apply integral_congr_ae
    exact ae_of_all mu fun x => sq_abs x
  have habsNonneg : 0 ≤ ∫ x : ℝ, |x| ∂mu := integral_nonneg fun x => abs_nonneg x
  simpa only [mul_one, one_pow, integral_const, probReal_univ, one_smul,
    habsSquare, hsecond, Real.sqrt_one, abs_of_nonneg habsNonneg] using hcs

theorem thirdAbsoluteMoment_ge_one
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    1 ≤ thirdAbsoluteMoment mu := by
  have hlog : (∫ x : ℝ, |x| ^ 2 ∂mu) ^ 2 ≤
      (∫ x : ℝ, |x| ∂mu) * ∫ x : ℝ, |x| ^ 3 ∂mu := by
    simpa only [id_eq, Real.norm_eq_abs] using
      secondMoment_sq_le_first_mul_third mu hX.norm (fun x => abs_nonneg x)
  have hsquare : (∫ x : ℝ, |x| ^ 2 ∂mu) = 1 := by
    calc
      (∫ x : ℝ, |x| ^ 2 ∂mu) = ∫ x : ℝ, x ^ 2 ∂mu := by
        apply integral_congr_ae
        exact ae_of_all mu fun x => sq_abs x
      _ = 1 := hsecond
  have hfirst := first_absolute_moment_le_one mu hX hsecond
  have hrhoNonneg : 0 ≤ thirdAbsoluteMoment mu :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3
  unfold thirdAbsoluteMoment at hlog hrhoNonneg ⊢
  rw [hsquare] at hlog
  have hproductUpper :
      (∫ x : ℝ, |x| ∂mu) * (∫ x : ℝ, |x| ^ 3 ∂mu) ≤
        ∫ x : ℝ, |x| ^ 3 ∂mu := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfirst hrhoNonneg
  exact le_trans (by simpa using hlog) hproductUpper

/-- Exact one-dimensional integral behind the Hardy-type stop-loss estimate, in the ordered
case `0 ≤ y ≤ z`. -/
theorem hardy_kernel_integral_eq_of_le {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) :
    3 * ∫ t in Set.Ici (0 : ℝ), positivePart (y - t) * positivePart (z - t) =
      (3 / 2 : ℝ) * y ^ 2 * z - (1 / 2 : ℝ) * y ^ 3 := by
  let f : ℝ → ℝ := fun t => positivePart (y - t) * positivePart (z - t)
  have hrestrict : ∫ t in Set.Ici (0 : ℝ), f t = ∫ t in Set.Icc 0 y, f t := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ici
    · intro t ht
      exact ht.1
    · intro t ht
      have hnotle : ¬t ≤ y := fun hty => ht.2 ⟨ht.1, hty⟩
      have hyt : y ≤ t := (lt_of_not_ge hnotle).le
      dsimp [f]
      rw [show positivePart (y - t) = 0 by
        simp [positivePart, max_eq_right (sub_nonpos.mpr hyt)]]
      exact zero_mul _
  have hinterval : ∫ t in Set.Icc 0 y, f t = ∫ t in 0..y, f t := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hy]
  have hinside : (∫ t in 0..y, f t) = ∫ t in 0..y, (y - t) * (z - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hy] at ht
    have hty : t ≤ y := ht.2
    have htz : t ≤ z := hty.trans hyz
    dsimp [f]
    simp only [positivePart, max_eq_left (sub_nonneg.mpr hty),
      max_eq_left (sub_nonneg.mpr htz)]
  have hpolynomial : (∫ t in 0..y, (y - t) * (z - t)) =
      y ^ 2 * z / 2 - y ^ 3 / 6 := by
    have hconst : IntervalIntegrable (fun _t : ℝ => y * z) volume 0 y :=
      continuous_const.intervalIntegrable 0 y
    have hlinear : IntervalIntegrable (fun t : ℝ => (y + z) * t) volume 0 y :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 y
    have hsquare : IntervalIntegrable (fun t : ℝ => t ^ 2) volume 0 y :=
      (continuous_id.pow 2).intervalIntegrable 0 y
    have hconstIntegral : (∫ _t in 0..y, y * z) = y ^ 2 * z := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    have hlinearIntegral : (∫ t in 0..y, (y + z) * t) =
        (y + z) * (y ^ 2 / 2) := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring
    have hsquareIntegral : (∫ t in 0..y, t ^ 2) = y ^ 3 / 3 := by
      rw [integral_pow]
      norm_num
    calc
      (∫ t in 0..y, (y - t) * (z - t)) =
          ∫ t in 0..y, (y * z - (y + z) * t) + t ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t _ht
        ring
      _ = (∫ t in 0..y, y * z - (y + z) * t) + ∫ t in 0..y, t ^ 2 := by
        rw [intervalIntegral.integral_add (hconst.sub hlinear) hsquare]
      _ = ((∫ _t in 0..y, y * z) - ∫ t in 0..y, (y + z) * t) +
          ∫ t in 0..y, t ^ 2 := by
        rw [intervalIntegral.integral_sub hconst hlinear]
      _ = y ^ 2 * z / 2 - y ^ 3 / 6 := by
        rw [hconstIntegral, hlinearIntegral, hsquareIntegral]
        ring
  change 3 * (∫ t in Set.Ici (0 : ℝ), f t) =
    (3 / 2 : ℝ) * y ^ 2 * z - (1 / 2 : ℝ) * y ^ 3
  rw [hrestrict, hinterval, hinside, hpolynomial]
  ring

/-- Symmetric pointwise inequality used after introducing two independent copies. -/
theorem hardy_kernel_integral_le {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    3 * ∫ t in Set.Ici (0 : ℝ), positivePart (y - t) * positivePart (z - t) ≤
      (1 / 2 : ℝ) * (y * z ^ 2 + y ^ 2 * z) := by
  rcases le_total y z with hyz | hzy
  · rw [hardy_kernel_integral_eq_of_le hy hyz]
    have hgap : 0 ≤ y * (z - y) ^ 2 := mul_nonneg hy (sq_nonneg (z - y))
    nlinarith
  · have hordered := hardy_kernel_integral_eq_of_le hz hzy
    have hcomm :
        (∫ t in Set.Ici (0 : ℝ), positivePart (y - t) * positivePart (z - t)) =
          ∫ t in Set.Ici (0 : ℝ), positivePart (z - t) * positivePart (y - t) := by
      apply setIntegral_congr_ae measurableSet_Ici
      filter_upwards [] with t _ht
      ring
    rw [hcomm, hordered]
    have hgap : 0 ≤ z * (y - z) ^ 2 := mul_nonneg hz (sq_nonneg (y - z))
    nlinarith

theorem integrableOn_hardy_kernel {y z : ℝ} :
    IntegrableOn (fun t : ℝ => positivePart (y - t) * positivePart (z - t))
      (Set.Ici 0) volume := by
  have hcontinuous :
      Continuous (fun t : ℝ => positivePart (y - t) * positivePart (z - t)) := by
    unfold positivePart
    fun_prop
  have hcompact :
      IntegrableOn (fun t : ℝ => positivePart (y - t) * positivePart (z - t))
        (Set.Icc 0 y) volume :=
    hcontinuous.integrableOn_Icc
  apply hcompact.of_forall_diff_eq_zero measurableSet_Ici
  intro t ht
  have hnotle : ¬t ≤ y := fun hty => ht.2 ⟨ht.1, hty⟩
  have hyt : y ≤ t := (lt_of_not_ge hnotle).le
  rw [show positivePart (y - t) = 0 by
    simp [positivePart, max_eq_right (sub_nonpos.mpr hyt)]]
  exact zero_mul _

theorem positivePart_positivePart_sub (x t : ℝ) (ht : 0 ≤ t) :
    positivePart (positivePart x - t) = positivePart (x - t) := by
  by_cases hx : 0 ≤ x
  · simp [positivePart, max_eq_left hx]
  · have hxnonpos : x ≤ 0 := le_of_not_ge hx
    have hleft : -t ≤ 0 := neg_nonpos.mpr ht
    have hright : x - t ≤ 0 := sub_nonpos.mpr (hxnonpos.trans ht)
    simp [positivePart, max_eq_right hxnonpos, max_eq_right hleft,
      max_eq_right hright]

theorem integrable_positivePart_sub
    {mu : Measure ℝ} [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) (t : ℝ) :
    Integrable (fun x => positivePart (x - t)) mu := by
  have hshift : MemLp (fun x : ℝ => x - t) 3 mu := by
    simpa only [id_eq] using hX.sub (memLp_const t)
  simpa only [positivePart] using hshift.pos_part.integrable (by norm_num)

theorem integrable_positivePart_reverse_sub
    {mu : Measure ℝ} [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) (t : ℝ) :
    Integrable (fun x => positivePart (t - x)) mu := by
  have hshift : MemLp (fun x : ℝ => t - x) 3 mu := by
    simpa only [id_eq] using (memLp_const t).sub hX
  simpa only [positivePart] using hshift.pos_part.integrable (by norm_num)

theorem reverseStopLoss_eq_add_positiveStopLoss
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0) (t : ℝ) :
    reverseStopLoss mu t = t + positiveStopLoss mu t := by
  have hpoint (x : ℝ) :
      positivePart (t - x) - positivePart (x - t) = t - x := by
    simpa only [negativePart, positivePart, neg_sub] using
      positivePart_sub_negativePart (t - x)
  have hreverse := integrable_positivePart_reverse_sub hX t
  have hforward := integrable_positivePart_sub hX t
  have hdifference : reverseStopLoss mu t - positiveStopLoss mu t =
      ∫ x, t - x ∂mu := by
    unfold reverseStopLoss positiveStopLoss
    rw [← integral_sub hreverse hforward]
    apply integral_congr_ae
    exact ae_of_all mu hpoint
  have hidentityIntegrable : Integrable (fun x : ℝ => x) mu := by
    simpa only [id_eq] using hX.integrable (by norm_num)
  have hright : (∫ x, t - x ∂mu) = t := by
    rw [integral_sub (integrable_const t) hidentityIntegrable, hmean]
    simp
  linarith

/-- The positive stop-loss Hardy inequality `3 ∫ A(t)^2 dt ≤ E X₊ · E X₊²`. -/
theorem positive_stopLoss_sq_integral_le
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    3 * ∫ t in Set.Ici (0 : ℝ), positiveStopLoss mu t ^ 2 ≤
      positiveMoment mu 1 * positiveMoment mu 2 := by
  let tau : Measure ℝ := volume.restrict (Set.Ici 0)
  let nu : Measure (ℝ × ℝ) := mu.prod mu
  let K : ℝ × (ℝ × ℝ) → ℝ := fun q =>
    positivePart (q.2.1 - q.1) * positivePart (q.2.2 - q.1)
  let J : ℝ × ℝ → ℝ := fun p => ∫ t, K (t, p) ∂tau
  let G : ℝ × ℝ → ℝ := fun p => ∫ t, ‖K (t, p)‖ ∂tau
  let H : ℝ × ℝ → ℝ := fun p =>
    (1 / 6 : ℝ) *
      (positivePart p.1 * positivePart p.2 ^ 2 +
        positivePart p.1 ^ 2 * positivePart p.2)
  let B : ℝ × ℝ → ℝ := fun p =>
    (1 / 2 : ℝ) *
      (positivePart p.1 * positivePart p.2 ^ 2 +
        positivePart p.1 ^ 2 * positivePart p.2)
  have hKstrong : StronglyMeasurable K := by
    dsimp [K]
    unfold positivePart
    fun_prop
  have hKnonneg (q : ℝ × (ℝ × ℝ)) : 0 ≤ K q := by
    dsimp [K]
    exact mul_nonneg (positivePart_nonneg _) (positivePart_nonneg _)
  have hsection (p : ℝ × ℝ) : Integrable (fun t => K (t, p)) tau := by
    change IntegrableOn
      (fun t : ℝ => positivePart (p.1 - t) * positivePart (p.2 - t))
      (Set.Ici 0) volume
    have hbase := integrableOn_hardy_kernel
      (y := positivePart p.1) (z := positivePart p.2)
    apply hbase.congr
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [positivePart_positivePart_sub p.1 t ht,
      positivePart_positivePart_sub p.2 t ht]
  have hinnerEq (p : ℝ × ℝ) : J p =
      ∫ t in Set.Ici (0 : ℝ),
        positivePart (positivePart p.1 - t) * positivePart (positivePart p.2 - t) := by
    dsimp [J, tau, K]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [positivePart_positivePart_sub p.1 t ht,
      positivePart_positivePart_sub p.2 t ht]
  have hG_eq_J (p : ℝ × ℝ) : G p = J p := by
    dsimp [G, J]
    apply integral_congr_ae
    exact ae_of_all tau fun t => Real.norm_of_nonneg (hKnonneg (t, p))
  have hJnonneg (p : ℝ × ℝ) : 0 ≤ J p := by
    dsimp [J]
    exact integral_nonneg fun t => hKnonneg (t, p)
  have hJbound (p : ℝ × ℝ) : 3 * J p ≤ B p := by
    rw [hinnerEq]
    exact hardy_kernel_integral_le (positivePart_nonneg p.1) (positivePart_nonneg p.2)
  have hpositive1 : Integrable positivePart mu := integrable_positivePart hX
  have hpositive2 : Integrable (fun x => positivePart x ^ 2) mu :=
    integrable_positivePart_sq hX
  have htermOne : Integrable
      (fun p : ℝ × ℝ => positivePart p.1 * positivePart p.2 ^ 2) nu := by
    dsimp [nu]
    exact hpositive1.mul_prod hpositive2
  have htermTwo : Integrable
      (fun p : ℝ × ℝ => positivePart p.1 ^ 2 * positivePart p.2) nu := by
    dsimp [nu]
    exact hpositive2.mul_prod hpositive1
  have hHintegrable : Integrable H nu := by
    dsimp [H]
    exact (htermOne.add htermTwo).const_mul (1 / 6 : ℝ)
  have hGstrong : StronglyMeasurable G := by
    dsimp [G]
    exact hKstrong.norm.integral_prod_left'
  have hGbound (p : ℝ × ℝ) : ‖G p‖ ≤ H p := by
    rw [hG_eq_J, Real.norm_of_nonneg (hJnonneg p)]
    have hbound := hJbound p
    dsimp [H, B] at hbound ⊢
    nlinarith
  have hGintegrable : Integrable G nu :=
    hHintegrable.mono' hGstrong.aestronglyMeasurable (ae_of_all nu hGbound)
  have hKintegrable : Integrable K (tau.prod nu) := by
    apply (integrable_prod_iff' hKstrong.aestronglyMeasurable).2
    constructor
    · exact ae_of_all nu hsection
    · simpa only [G] using hGintegrable
  have hsquareAt (t : ℝ) : positiveStopLoss mu t ^ 2 =
      ∫ p, K (t, p) ∂nu := by
    have hprod := integral_prod_mul (μ := mu) (ν := mu)
      (fun x : ℝ => positivePart (x - t)) (fun x : ℝ => positivePart (x - t))
    simpa only [positiveStopLoss, K, nu, pow_two] using hprod.symm
  have hleft : (∫ t, positiveStopLoss mu t ^ 2 ∂tau) =
      ∫ t, ∫ p, K (t, p) ∂nu ∂tau := by
    apply integral_congr_ae
    exact ae_of_all tau hsquareAt
  have hswap : (∫ t, ∫ p, K (t, p) ∂nu ∂tau) =
      ∫ p, J p ∂nu := by
    calc
      (∫ t, ∫ p, K (t, p) ∂nu ∂tau) = ∫ q, K q ∂tau.prod nu :=
        (integral_prod K hKintegrable).symm
      _ = ∫ p, ∫ t, K (t, p) ∂tau ∂nu := integral_prod_symm K hKintegrable
      _ = ∫ p, J p ∂nu := by rfl
  have hJintegrable : Integrable J nu := by
    simpa only [J] using hKintegrable.integral_prod_right
  have hBintegrable : Integrable B nu := by
    dsimp [B]
    exact (htermOne.add htermTwo).const_mul (1 / 2 : ℝ)
  have hintegralBound : (∫ p, 3 * J p ∂nu) ≤ ∫ p, B p ∂nu :=
    integral_mono (hJintegrable.const_mul 3) hBintegrable hJbound
  change 3 * (∫ t, positiveStopLoss mu t ^ 2 ∂tau) ≤
    positiveMoment mu 1 * positiveMoment mu 2
  calc
    3 * (∫ t, positiveStopLoss mu t ^ 2 ∂tau) = 3 * ∫ p, J p ∂nu := by
      rw [hleft, hswap]
    _ = ∫ p, 3 * J p ∂nu := by rw [integral_const_mul]
    _ ≤ ∫ p, B p ∂nu := hintegralBound
    _ = positiveMoment mu 1 * positiveMoment mu 2 := by
      have hprodOne :
          (∫ p : ℝ × ℝ, positivePart p.1 * positivePart p.2 ^ 2 ∂mu.prod mu) =
            (∫ x, positivePart x ∂mu) * ∫ x, positivePart x ^ 2 ∂mu := by
        simpa only using integral_prod_mul (μ := mu) (ν := mu)
          positivePart (fun x : ℝ => positivePart x ^ 2)
      have hprodTwo :
          (∫ p : ℝ × ℝ, positivePart p.1 ^ 2 * positivePart p.2 ∂mu.prod mu) =
            (∫ x, positivePart x ^ 2 ∂mu) * ∫ x, positivePart x ∂mu := by
        simpa only using integral_prod_mul (μ := mu) (ν := mu)
          (fun x : ℝ => positivePart x ^ 2) positivePart
      dsimp [B, nu]
      rw [integral_const_mul, integral_add htermOne htermTwo]
      unfold nu
      rw [hprodOne, hprodTwo]
      unfold positiveMoment
      simp only [pow_one]
      ring

/-- The negative stop-loss Hardy inequality, obtained by reflecting the law. -/
theorem negative_stopLoss_sq_integral_le
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    3 * ∫ t in Set.Ici (0 : ℝ), negativeStopLoss mu t ^ 2 ≤
      negativeMoment mu 1 * negativeMoment mu 2 := by
  let reflect : ℝ → ℝ := fun x => -x
  let reflectedLaw : Measure ℝ := mu.map reflect
  have hreflectMeasurable : AEMeasurable reflect mu := by
    dsimp [reflect]
    fun_prop
  letI : IsProbabilityMeasure reflectedLaw := by
    dsimp [reflectedLaw]
    exact Measure.isProbabilityMeasure_map hreflectMeasurable
  have hReflected : MemLp (id : ℝ → ℝ) 3 reflectedLaw := by
    apply (memLp_map_measure_iff aestronglyMeasurable_id hreflectMeasurable).2
    simpa only [Function.comp_apply, id_eq, reflect] using hX.neg
  have hstop (t : ℝ) : positiveStopLoss reflectedLaw t = negativeStopLoss mu t := by
    unfold positiveStopLoss negativeStopLoss
    dsimp [reflectedLaw]
    rw [integral_map hreflectMeasurable (by
      apply Continuous.aestronglyMeasurable
      unfold positivePart
      fun_prop)]
  have hmoment (k : ℕ) : positiveMoment reflectedLaw k = negativeMoment mu k := by
    unfold positiveMoment negativeMoment
    dsimp [reflectedLaw]
    rw [integral_map hreflectMeasurable (by
      apply Continuous.aestronglyMeasurable
      unfold positivePart
      fun_prop)]
    apply integral_congr_ae
    exact ae_of_all mu fun x => by rfl
  have hbound := positive_stopLoss_sq_integral_le reflectedLaw hReflected
  simp_rw [hstop] at hbound
  rw [hmoment 1, hmoment 2] at hbound
  exact hbound

/-- The nonnegative kernel whose `t`-integral represents `|x-y|³ / 6`. -/
def symmetrizationKernel (x y t : ℝ) : ℝ :=
  positivePart (x - t) * positivePart (t - y) +
    positivePart (y - t) * positivePart (t - x)

theorem symmetrizationKernel_nonneg (x y t : ℝ) :
    0 ≤ symmetrizationKernel x y t := by
  unfold symmetrizationKernel
  exact add_nonneg
    (mul_nonneg (positivePart_nonneg _) (positivePart_nonneg _))
    (mul_nonneg (positivePart_nonneg _) (positivePart_nonneg _))

/-- Exact kernel identity in the ordered case `x ≤ y`. -/
theorem symmetrizationKernel_integral_eq_of_le {x y : ℝ} (hxy : x ≤ y) :
    6 * ∫ t : ℝ, symmetrizationKernel x y t = (y - x) ^ 3 := by
  have hfirstZero (t : ℝ) :
      positivePart (x - t) * positivePart (t - y) = 0 := by
    rcases le_total t x with htx | hxt
    · have hty : t ≤ y := htx.trans hxy
      rw [show positivePart (t - y) = 0 by
        simp [positivePart, max_eq_right (sub_nonpos.mpr hty)]]
      exact mul_zero _
    · rw [show positivePart (x - t) = 0 by
        simp [positivePart, max_eq_right (sub_nonpos.mpr hxt)]]
      exact zero_mul _
  have hfirstIntegral :
      (∫ t : ℝ, positivePart (x - t) * positivePart (t - y)) = 0 := by
    calc
      (∫ t : ℝ, positivePart (x - t) * positivePart (t - y)) =
          ∫ _t : ℝ, (0 : ℝ) := by
        apply integral_congr_ae
        exact ae_of_all volume hfirstZero
      _ = 0 := by simp
  let f : ℝ → ℝ := fun t => positivePart (y - t) * positivePart (t - x)
  have hrestrict : (∫ t : ℝ, f t) = ∫ t in Set.Icc x y, f t := by
    have hset := setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (μ := volume) (f := f) MeasurableSet.univ (Set.subset_univ (Set.Icc x y))
      (fun t ht => by
        by_cases htx : t ≤ x
        · dsimp [f]
          rw [show positivePart (t - x) = 0 by
            simp [positivePart, max_eq_right (sub_nonpos.mpr htx)]]
          exact mul_zero _
        · have hxt : x < t := lt_of_not_ge htx
          have hnoty : ¬t ≤ y := fun hty => ht.2 ⟨hxt.le, hty⟩
          have hyt : y ≤ t := (lt_of_not_ge hnoty).le
          dsimp [f]
          rw [show positivePart (y - t) = 0 by
            simp [positivePart, max_eq_right (sub_nonpos.mpr hyt)]]
          exact zero_mul _)
    simpa using hset
  have hinterval : (∫ t in Set.Icc x y, f t) = ∫ t in x..y, f t := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hxy]
  have hinside : (∫ t in x..y, f t) = ∫ t in x..y, (y - t) * (t - x) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    dsimp [f]
    simp only [positivePart, max_eq_left (sub_nonneg.mpr ht.2),
      max_eq_left (sub_nonneg.mpr ht.1)]
  have hpolynomial : (∫ t in x..y, (y - t) * (t - x)) = (y - x) ^ 3 / 6 := by
    have hsquare : IntervalIntegrable (fun t : ℝ => t ^ 2) volume x y :=
      (continuous_id.pow 2).intervalIntegrable x y
    have hlinear : IntervalIntegrable (fun t : ℝ => (x + y) * t) volume x y :=
      (continuous_const.mul continuous_id).intervalIntegrable x y
    have hconst : IntervalIntegrable (fun _t : ℝ => x * y) volume x y :=
      continuous_const.intervalIntegrable x y
    have hsquareIntegral : (∫ t in x..y, t ^ 2) = (y ^ 3 - x ^ 3) / 3 := by
      rw [integral_pow]
      norm_num
    have hlinearIntegral : (∫ t in x..y, (x + y) * t) =
        (x + y) * ((y ^ 2 - x ^ 2) / 2) := by
      rw [intervalIntegral.integral_const_mul, integral_id]
    have hconstIntegral : (∫ _t in x..y, x * y) = (y - x) * (x * y) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    calc
      (∫ t in x..y, (y - t) * (t - x)) =
          ∫ t in x..y, ((x + y) * t - t ^ 2) - x * y := by
        apply intervalIntegral.integral_congr
        intro t _ht
        ring
      _ = ((∫ t in x..y, (x + y) * t) - ∫ t in x..y, t ^ 2) -
          ∫ _t in x..y, x * y := by
        rw [intervalIntegral.integral_sub (hlinear.sub hsquare) hconst,
          intervalIntegral.integral_sub hlinear hsquare]
      _ = (y - x) ^ 3 / 6 := by
        rw [hlinearIntegral, hsquareIntegral, hconstIntegral]
        ring
  change 6 * ∫ t : ℝ,
    (positivePart (x - t) * positivePart (t - y) + f t) = (y - x) ^ 3
  rw [integral_add, hfirstIntegral, zero_add, hrestrict, hinterval, hinside, hpolynomial]
  · ring
  · simpa only [hfirstZero] using
      (integrable_zero ℝ ℝ volume)
  · have hcontinuous : Continuous f := by
      dsimp [f]
      unfold positivePart
      fun_prop
    exact (hcontinuous.integrableOn_Icc).integrable_of_ae_notMem_eq_zero <| by
      filter_upwards [] with t
      intro ht
      by_cases htx : t ≤ x
      · dsimp [f]
        rw [show positivePart (t - x) = 0 by
          simp [positivePart, max_eq_right (sub_nonpos.mpr htx)]]
        exact mul_zero _
      · have hxt : x < t := lt_of_not_ge htx
        have hnoty : ¬t ≤ y := fun hty => ht ⟨hxt.le, hty⟩
        have hyt : y ≤ t := (lt_of_not_ge hnoty).le
        dsimp [f]
        rw [show positivePart (y - t) = 0 by
          simp [positivePart, max_eq_right (sub_nonpos.mpr hyt)]]
        exact zero_mul _

theorem integrable_symmetrizationKernel (x y : ℝ) :
    Integrable (fun t : ℝ => symmetrizationKernel x y t) volume := by
  have hcontinuous : Continuous (fun t : ℝ => symmetrizationKernel x y t) := by
    unfold symmetrizationKernel positivePart
    fun_prop
  have hcompact : IntegrableOn (fun t : ℝ => symmetrizationKernel x y t)
      (Set.Icc (min x y) (max x y)) volume :=
    hcontinuous.integrableOn_Icc
  apply hcompact.integrable_of_ae_notMem_eq_zero
  exact ae_of_all volume fun t ht => by
    by_cases hlow : t ≤ min x y
    · have htx : t ≤ x := hlow.trans (min_le_left x y)
      have hty : t ≤ y := hlow.trans (min_le_right x y)
      unfold symmetrizationKernel
      rw [show positivePart (t - y) = 0 by
          simp [positivePart, max_eq_right (sub_nonpos.mpr hty)],
        show positivePart (t - x) = 0 by
          simp [positivePart, max_eq_right (sub_nonpos.mpr htx)]]
      ring
    · have hmin : min x y < t := lt_of_not_ge hlow
      have hnotmax : ¬t ≤ max x y := fun hmax => ht ⟨hmin.le, hmax⟩
      have hhigh : max x y ≤ t := (lt_of_not_ge hnotmax).le
      have hxt : x ≤ t := (le_max_left x y).trans hhigh
      have hyt : y ≤ t := (le_max_right x y).trans hhigh
      unfold symmetrizationKernel
      rw [show positivePart (x - t) = 0 by
          simp [positivePart, max_eq_right (sub_nonpos.mpr hxt)],
        show positivePart (y - t) = 0 by
          simp [positivePart, max_eq_right (sub_nonpos.mpr hyt)]]
      ring

/-- Pointwise symmetrization identity for arbitrary `x,y`. -/
theorem symmetrizationKernel_integral (x y : ℝ) :
    6 * ∫ t : ℝ, symmetrizationKernel x y t = |x - y| ^ 3 := by
  rcases le_total x y with hxy | hyx
  · calc
      6 * ∫ t : ℝ, symmetrizationKernel x y t = (y - x) ^ 3 :=
        symmetrizationKernel_integral_eq_of_le hxy
      _ = |x - y| ^ 3 := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
        ring
  · have hswap : (∫ t : ℝ, symmetrizationKernel x y t) =
        ∫ t : ℝ, symmetrizationKernel y x t := by
      apply integral_congr_ae
      exact ae_of_all volume fun t => by
        unfold symmetrizationKernel
        ring
    calc
      6 * ∫ t : ℝ, symmetrizationKernel x y t =
          6 * ∫ t : ℝ, symmetrizationKernel y x t := by rw [hswap]
      _ = (x - y) ^ 3 := symmetrizationKernel_integral_eq_of_le hyx
      _ = |x - y| ^ 3 := by rw [abs_of_nonneg (sub_nonneg.mpr hyx)]

theorem integrable_symmetrized_abs_sub_cube
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ 3) (mu.prod mu) := by
  have hfirst : MemLp (fun p : ℝ × ℝ => p.1) 3 (mu.prod mu) := by
    simpa only [id_eq] using hX.comp_fst mu
  have hsecond : MemLp (fun p : ℝ × ℝ => p.2) 3 (mu.prod mu) := by
    simpa only [id_eq] using hX.comp_snd mu
  have hdifference : MemLp (fun p : ℝ × ℝ => p.1 - p.2) 3 (mu.prod mu) :=
    hfirst.sub hsecond
  have h := hdifference.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
  simpa only [Real.norm_eq_abs] using h

/-- Fubini form of the symmetrization identity. -/
theorem symmetrizedThirdAbsoluteMoment_eq_kernel_integral
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    symmetrizedThirdAbsoluteMoment mu =
      6 * ∫ t : ℝ, ∫ p : ℝ × ℝ, symmetrizationKernel p.1 p.2 t ∂mu.prod mu := by
  let nu : Measure (ℝ × ℝ) := mu.prod mu
  let K : ℝ × (ℝ × ℝ) → ℝ := fun q =>
    symmetrizationKernel q.2.1 q.2.2 q.1
  let J : ℝ × ℝ → ℝ := fun p => ∫ t : ℝ, K (t, p)
  let G : ℝ × ℝ → ℝ := fun p => ∫ t : ℝ, ‖K (t, p)‖
  have hKstrong : StronglyMeasurable K := by
    dsimp [K]
    unfold symmetrizationKernel positivePart
    fun_prop
  have hKnonneg (q : ℝ × (ℝ × ℝ)) : 0 ≤ K q := by
    dsimp [K]
    exact symmetrizationKernel_nonneg _ _ _
  have hsection (p : ℝ × ℝ) : Integrable (fun t : ℝ => K (t, p)) volume := by
    simpa only [K] using integrable_symmetrizationKernel p.1 p.2
  have hJformula (p : ℝ × ℝ) : J p = |p.1 - p.2| ^ 3 / 6 := by
    have hidentity := symmetrizationKernel_integral p.1 p.2
    dsimp [J, K]
    linarith
  have hG_eq_J (p : ℝ × ℝ) : G p = J p := by
    dsimp [G, J]
    apply integral_congr_ae
    exact ae_of_all volume fun t => Real.norm_of_nonneg (hKnonneg (t, p))
  have hGfun : G = fun p : ℝ × ℝ => (1 / 6 : ℝ) * |p.1 - p.2| ^ 3 := by
    funext p
    rw [hG_eq_J, hJformula]
    ring
  have habsIntegrable : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ 3) nu := by
    simpa only [nu] using integrable_symmetrized_abs_sub_cube mu hX
  have hGintegrable : Integrable G nu := by
    rw [hGfun]
    exact habsIntegrable.const_mul (1 / 6 : ℝ)
  have hKintegrable : Integrable K (volume.prod nu) := by
    apply (integrable_prod_iff' hKstrong.aestronglyMeasurable).2
    constructor
    · exact ae_of_all nu hsection
    · simpa only [G] using hGintegrable
  have hswap : (∫ p, J p ∂nu) =
      ∫ t : ℝ, ∫ p, K (t, p) ∂nu := by
    calc
      (∫ p, J p ∂nu) = ∫ p, (∫ t : ℝ, K (t, p) ∂volume) ∂nu := by rfl
      _ = ∫ q, K q ∂volume.prod nu :=
        (integral_prod_symm K hKintegrable).symm
      _ = ∫ t : ℝ, ∫ p, K (t, p) ∂nu := integral_prod K hKintegrable
  have hmoment : (∫ p : ℝ × ℝ, |p.1 - p.2| ^ 3 ∂nu) =
      6 * ∫ p, J p ∂nu := by
    calc
      (∫ p : ℝ × ℝ, |p.1 - p.2| ^ 3 ∂nu) = ∫ p, 6 * J p ∂nu := by
        apply integral_congr_ae
        exact ae_of_all nu fun p => by
          change |p.1 - p.2| ^ 3 = 6 * J p
          rw [hJformula]
          ring
      _ = 6 * ∫ p, J p ∂nu := by rw [integral_const_mul]
  unfold symmetrizedThirdAbsoluteMoment
  change (∫ p : ℝ × ℝ, |p.1 - p.2| ^ 3 ∂nu) =
    6 * ∫ t : ℝ, ∫ p, K (t, p) ∂nu
  rw [hmoment, hswap]

theorem integral_symmetrizationKernel_prod
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) (t : ℝ) :
    (∫ p : ℝ × ℝ, symmetrizationKernel p.1 p.2 t ∂mu.prod mu) =
      2 * positiveStopLoss mu t * reverseStopLoss mu t := by
  have hforward := integrable_positivePart_sub hX t
  have hreverse := integrable_positivePart_reverse_sub hX t
  have htermOne : Integrable
      (fun p : ℝ × ℝ => positivePart (p.1 - t) * positivePart (t - p.2))
      (mu.prod mu) :=
    hforward.mul_prod hreverse
  have htermTwo : Integrable
      (fun p : ℝ × ℝ => positivePart (p.2 - t) * positivePart (t - p.1))
      (mu.prod mu) := by
    simpa only [mul_comm] using hreverse.mul_prod hforward
  have hprodOne :
      (∫ p : ℝ × ℝ, positivePart (p.1 - t) * positivePart (t - p.2) ∂mu.prod mu) =
        positiveStopLoss mu t * reverseStopLoss mu t := by
    simpa only [positiveStopLoss, reverseStopLoss] using
      integral_prod_mul (μ := mu) (ν := mu)
        (fun x : ℝ => positivePart (x - t))
        (fun y : ℝ => positivePart (t - y))
  have hprodTwo :
      (∫ p : ℝ × ℝ, positivePart (p.2 - t) * positivePart (t - p.1) ∂mu.prod mu) =
        positiveStopLoss mu t * reverseStopLoss mu t := by
    simpa only [positiveStopLoss, reverseStopLoss, mul_comm] using
      integral_prod_mul (μ := mu) (ν := mu)
        (fun x : ℝ => positivePart (t - x))
        (fun y : ℝ => positivePart (y - t))
  unfold symmetrizationKernel
  rw [integral_add htermOne htermTwo, hprodOne, hprodTwo]
  ring

theorem integrable_symmetrizationKernel_joint
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    Integrable
      (fun q : ℝ × (ℝ × ℝ) => symmetrizationKernel q.2.1 q.2.2 q.1)
      (volume.prod (mu.prod mu)) := by
  let nu : Measure (ℝ × ℝ) := mu.prod mu
  let K : ℝ × (ℝ × ℝ) → ℝ := fun q =>
    symmetrizationKernel q.2.1 q.2.2 q.1
  let G : ℝ × ℝ → ℝ := fun p => ∫ t : ℝ, ‖K (t, p)‖
  have hKstrong : StronglyMeasurable K := by
    dsimp [K]
    unfold symmetrizationKernel positivePart
    fun_prop
  have hKnonneg (q : ℝ × (ℝ × ℝ)) : 0 ≤ K q := by
    dsimp [K]
    exact symmetrizationKernel_nonneg _ _ _
  have hsection (p : ℝ × ℝ) : Integrable (fun t : ℝ => K (t, p)) volume := by
    simpa only [K] using integrable_symmetrizationKernel p.1 p.2
  have hGformula (p : ℝ × ℝ) : G p = (1 / 6 : ℝ) * |p.1 - p.2| ^ 3 := by
    have hidentity := symmetrizationKernel_integral p.1 p.2
    have hnormIntegral : (∫ t : ℝ, |K (t, p)|) = ∫ t : ℝ, K (t, p) := by
      apply integral_congr_ae
      exact ae_of_all volume fun t => abs_of_nonneg (hKnonneg (t, p))
    dsimp [G]
    rw [hnormIntegral]
    dsimp [K] at hidentity ⊢
    linarith
  have habsIntegrable : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ 3) nu := by
    simpa only [nu] using integrable_symmetrized_abs_sub_cube mu hX
  have hGintegrable : Integrable G nu := by
    have hscaled := habsIntegrable.const_mul (1 / 6 : ℝ)
    exact hscaled.congr (ae_of_all nu fun p => (hGformula p).symm)
  change Integrable K (volume.prod nu)
  apply (integrable_prod_iff' hKstrong.aestronglyMeasurable).2
  constructor
  · exact ae_of_all nu hsection
  · simpa only [G] using hGintegrable

theorem integrable_symmetrizationKernel_marginal
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    Integrable
      (fun t : ℝ => ∫ p : ℝ × ℝ,
        symmetrizationKernel p.1 p.2 t ∂mu.prod mu) volume := by
  exact (integrable_symmetrizationKernel_joint mu hX).integral_prod_left

theorem integrable_full_stopLoss_integrand
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0) :
    Integrable (fun t : ℝ => positiveStopLoss mu t * (t + positiveStopLoss mu t)) volume := by
  have hmarginal := integrable_symmetrizationKernel_marginal mu hX
  have hscaled := hmarginal.const_mul (1 / 2 : ℝ)
  apply hscaled.congr
  exact ae_of_all volume fun t => by
    change (1 / 2 : ℝ) *
      (∫ p : ℝ × ℝ, symmetrizationKernel p.1 p.2 t ∂mu.prod mu) =
        positiveStopLoss mu t * (t + positiveStopLoss mu t)
    rw [integral_symmetrizationKernel_prod mu hX t,
      reverseStopLoss_eq_add_positiveStopLoss mu hX hmean t]
    ring

theorem positiveStopLoss_neg_eq_add_negativeStopLoss
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0) (t : ℝ) :
    positiveStopLoss mu (-t) = t + negativeStopLoss mu t := by
  have hreverse := reverseStopLoss_eq_add_positiveStopLoss mu hX hmean (-t)
  have hreflect : reverseStopLoss mu (-t) = negativeStopLoss mu t := by
    unfold reverseStopLoss negativeStopLoss
    apply integral_congr_ae
    exact ae_of_all mu fun x => congrArg positivePart (by ring)
  rw [hreflect] at hreverse
  linarith

theorem full_stopLoss_integral_eq_positive_negative_halves
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0) :
    (∫ t : ℝ, positiveStopLoss mu t * (t + positiveStopLoss mu t)) =
      (∫ t in Set.Ici (0 : ℝ),
        (positiveStopLoss mu t) ^ 2 + t * positiveStopLoss mu t) +
      ∫ t in Set.Ici (0 : ℝ),
        (negativeStopLoss mu t) ^ 2 + t * negativeStopLoss mu t := by
  let F : ℝ → ℝ := fun t => positiveStopLoss mu t * (t + positiveStopLoss mu t)
  let P : ℝ → ℝ := fun t =>
    positiveStopLoss mu t ^ 2 + t * positiveStopLoss mu t
  let N : ℝ → ℝ := fun t =>
    negativeStopLoss mu t ^ 2 + t * negativeStopLoss mu t
  have hF : Integrable F volume := by
    simpa only [F] using integrable_full_stopLoss_integrand mu hX hmean
  have hsplit := integral_add_compl (μ := volume) (f := F)
    (s := Set.Iic (0 : ℝ)) measurableSet_Iic hF
  rw [Set.compl_Iic] at hsplit
  have hnegativeSubstitution : (∫ t in Set.Iic (0 : ℝ), F t) =
      ∫ s in Set.Ioi (0 : ℝ), F (-s) := by
    have hsubstitution := integral_comp_neg_Ioi (0 : ℝ) F
    simpa only [neg_zero] using hsubstitution.symm
  have hnegativePoint (s : ℝ) : F (-s) = N s := by
    dsimp [F, N]
    rw [positiveStopLoss_neg_eq_add_negativeStopLoss mu hX hmean s]
    ring
  have hnegative : (∫ t in Set.Iic (0 : ℝ), F t) =
      ∫ t in Set.Ici (0 : ℝ), N t := by
    calc
      (∫ t in Set.Iic (0 : ℝ), F t) = ∫ s in Set.Ioi (0 : ℝ), F (-s) :=
        hnegativeSubstitution
      _ = ∫ s in Set.Ioi (0 : ℝ), N s := by
        apply setIntegral_congr_ae measurableSet_Ioi
        exact ae_of_all volume fun s _hs => hnegativePoint s
      _ = ∫ s in Set.Ici (0 : ℝ), N s := integral_Ici_eq_integral_Ioi.symm
  have hpositivePoint (t : ℝ) : F t = P t := by
    dsimp [F, P]
    ring
  have hpositive : (∫ t in Set.Ioi (0 : ℝ), F t) =
      ∫ t in Set.Ici (0 : ℝ), P t := by
    calc
      (∫ t in Set.Ioi (0 : ℝ), F t) = ∫ t in Set.Ioi (0 : ℝ), P t := by
        apply setIntegral_congr_ae measurableSet_Ioi
        exact ae_of_all volume fun t _ht => hpositivePoint t
      _ = ∫ t in Set.Ici (0 : ℝ), P t := integral_Ici_eq_integral_Ioi.symm
  change (∫ t : ℝ, F t) =
    (∫ t in Set.Ici (0 : ℝ), P t) + ∫ t in Set.Ici (0 : ℝ), N t
  calc
    (∫ t : ℝ, F t) =
        (∫ t in Set.Iic (0 : ℝ), F t) + ∫ t in Set.Ioi (0 : ℝ), F t := hsplit.symm
    _ = (∫ t in Set.Ici (0 : ℝ), N t) + ∫ t in Set.Ici (0 : ℝ), P t := by
      rw [hnegative, hpositive]
    _ = (∫ t in Set.Ici (0 : ℝ), P t) + ∫ t in Set.Ici (0 : ℝ), N t := by
      rw [add_comm]

def weightedStopLossKernel (x t : ℝ) : ℝ :=
  t * positivePart (x - t)

theorem integrableOn_weightedStopLossKernel (x : ℝ) :
    IntegrableOn (weightedStopLossKernel x) (Set.Ici 0) volume := by
  have hcontinuous : Continuous (weightedStopLossKernel x) := by
    unfold weightedStopLossKernel positivePart
    fun_prop
  have hcompact : IntegrableOn (weightedStopLossKernel x)
      (Set.Icc 0 (max x 0)) volume :=
    hcontinuous.integrableOn_Icc
  apply hcompact.of_forall_diff_eq_zero measurableSet_Ici
  intro t ht
  have hnotle : ¬t ≤ max x 0 := fun htle => ht.2 ⟨ht.1, htle⟩
  have hhigh : max x 0 ≤ t := (lt_of_not_ge hnotle).le
  have hxt : x ≤ t := (le_max_left x 0).trans hhigh
  unfold weightedStopLossKernel
  rw [show positivePart (x - t) = 0 by
    simp [positivePart, max_eq_right (sub_nonpos.mpr hxt)]]
  exact mul_zero t

theorem weightedStopLossKernel_integral (x : ℝ) :
    (∫ t in Set.Ici (0 : ℝ), weightedStopLossKernel x t) = positivePart x ^ 3 / 6 := by
  by_cases hx : 0 ≤ x
  · have hrestrict : (∫ t in Set.Ici (0 : ℝ), weightedStopLossKernel x t) =
        ∫ t in Set.Icc 0 x, weightedStopLossKernel x t := by
      apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ici
      · intro t ht
        exact ht.1
      · intro t ht
        have hnotle : ¬t ≤ x := fun htx => ht.2 ⟨ht.1, htx⟩
        have hxt : x ≤ t := (lt_of_not_ge hnotle).le
        unfold weightedStopLossKernel
        rw [show positivePart (x - t) = 0 by
          simp [positivePart, max_eq_right (sub_nonpos.mpr hxt)]]
        exact mul_zero t
    have hinterval : (∫ t in Set.Icc 0 x, weightedStopLossKernel x t) =
        ∫ t in 0..x, weightedStopLossKernel x t := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hx]
    have hinside : (∫ t in 0..x, weightedStopLossKernel x t) =
        ∫ t in 0..x, x * t - t ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      unfold weightedStopLossKernel
      rw [show positivePart (x - t) = x - t by
        simp [positivePart, max_eq_left (sub_nonneg.mpr ht.2)]]
      ring
    have hlinear : IntervalIntegrable (fun t : ℝ => x * t) volume 0 x :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 x
    have hsquare : IntervalIntegrable (fun t : ℝ => t ^ 2) volume 0 x :=
      (continuous_id.pow 2).intervalIntegrable 0 x
    calc
      (∫ t in Set.Ici (0 : ℝ), weightedStopLossKernel x t) =
          ∫ t in 0..x, x * t - t ^ 2 := by rw [hrestrict, hinterval, hinside]
      _ = (∫ t in 0..x, x * t) - ∫ t in 0..x, t ^ 2 := by
        rw [intervalIntegral.integral_sub hlinear hsquare]
      _ = positivePart x ^ 3 / 6 := by
        rw [intervalIntegral.integral_const_mul, integral_id, integral_pow]
        simp only [positivePart, max_eq_left hx]
        norm_num
        ring
  · have hxnonpos : x ≤ 0 := le_of_not_ge hx
    have hzero : (∫ t in Set.Ici (0 : ℝ), weightedStopLossKernel x t) = 0 := by
      calc
        (∫ t in Set.Ici (0 : ℝ), weightedStopLossKernel x t) =
            ∫ _t in Set.Ici (0 : ℝ), (0 : ℝ) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
          have hxt : x ≤ t := hxnonpos.trans ht
          unfold weightedStopLossKernel
          rw [show positivePart (x - t) = 0 by
            simp [positivePart, max_eq_right (sub_nonpos.mpr hxt)]]
          exact mul_zero t
        _ = 0 := by simp
    rw [hzero]
    simp [positivePart, max_eq_right hxnonpos]

theorem weighted_positiveStopLoss_integral_eq
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    (∫ t in Set.Ici (0 : ℝ), t * positiveStopLoss mu t) =
      positiveMoment mu 3 / 6 := by
  let tau : Measure ℝ := volume.restrict (Set.Ici 0)
  let K : ℝ × ℝ → ℝ := fun q => weightedStopLossKernel q.2 q.1
  let G : ℝ → ℝ := fun x => ∫ t, ‖K (t, x)‖ ∂tau
  have hKstrong : StronglyMeasurable K := by
    dsimp [K]
    unfold weightedStopLossKernel positivePart
    fun_prop
  have hsection (x : ℝ) : Integrable (fun t => K (t, x)) tau := by
    simpa only [tau, K] using integrableOn_weightedStopLossKernel x
  have hGformula (x : ℝ) : G x = (1 / 6 : ℝ) * positivePart x ^ 3 := by
    have hnormIntegral : (∫ t in Set.Ici (0 : ℝ), |K (t, x)|) =
        ∫ t in Set.Ici (0 : ℝ), K (t, x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact abs_of_nonneg (mul_nonneg ht (positivePart_nonneg _))
    dsimp [G, tau]
    rw [hnormIntegral]
    change (∫ t in Set.Ici (0 : ℝ), weightedStopLossKernel x t) =
      (1 / 6 : ℝ) * positivePart x ^ 3
    rw [weightedStopLossKernel_integral]
    ring
  have hGintegrable : Integrable G mu := by
    have hcube := integrable_positivePart_cube hX
    have hscaled := hcube.const_mul (1 / 6 : ℝ)
    exact hscaled.congr (ae_of_all mu fun x => (hGformula x).symm)
  have hKintegrable : Integrable K (tau.prod mu) := by
    apply (integrable_prod_iff' hKstrong.aestronglyMeasurable).2
    constructor
    · exact ae_of_all mu hsection
    · simpa only [G] using hGintegrable
  have hinner (t : ℝ) : (∫ x, K (t, x) ∂mu) =
      t * positiveStopLoss mu t := by
    dsimp [K, weightedStopLossKernel, positiveStopLoss]
    rw [integral_const_mul]
  have hswap : (∫ t, ∫ x, K (t, x) ∂mu ∂tau) =
      ∫ x, ∫ t, K (t, x) ∂tau ∂mu := by
    exact integral_integral_swap hKintegrable
  change (∫ t, t * positiveStopLoss mu t ∂tau) = positiveMoment mu 3 / 6
  calc
    (∫ t, t * positiveStopLoss mu t ∂tau) =
        ∫ t, ∫ x, K (t, x) ∂mu ∂tau := by
      apply integral_congr_ae
      exact ae_of_all tau fun t => (hinner t).symm
    _ = ∫ x, ∫ t, K (t, x) ∂tau ∂mu := hswap
    _ = ∫ x, (1 / 6 : ℝ) * positivePart x ^ 3 ∂mu := by
      apply integral_congr_ae
      exact ae_of_all mu fun x => by
        change (∫ t in Set.Ici (0 : ℝ), weightedStopLossKernel x t) =
          (1 / 6 : ℝ) * positivePart x ^ 3
        rw [weightedStopLossKernel_integral]
        ring
    _ = (1 / 6 : ℝ) * ∫ x, positivePart x ^ 3 ∂mu := by
      rw [integral_const_mul]
    _ = positiveMoment mu 3 / 6 := by
      unfold positiveMoment
      ring

theorem weighted_negativeStopLoss_integral_eq
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    (∫ t in Set.Ici (0 : ℝ), t * negativeStopLoss mu t) =
      negativeMoment mu 3 / 6 := by
  let reflect : ℝ → ℝ := fun x => -x
  let reflectedLaw : Measure ℝ := mu.map reflect
  have hreflectMeasurable : AEMeasurable reflect mu := by
    dsimp [reflect]
    fun_prop
  letI : IsProbabilityMeasure reflectedLaw := by
    dsimp [reflectedLaw]
    exact Measure.isProbabilityMeasure_map hreflectMeasurable
  have hReflected : MemLp (id : ℝ → ℝ) 3 reflectedLaw := by
    apply (memLp_map_measure_iff aestronglyMeasurable_id hreflectMeasurable).2
    simpa only [Function.comp_apply, id_eq, reflect] using hX.neg
  have hstop (t : ℝ) : positiveStopLoss reflectedLaw t = negativeStopLoss mu t := by
    unfold positiveStopLoss negativeStopLoss
    dsimp [reflectedLaw]
    rw [integral_map hreflectMeasurable (by
      apply Continuous.aestronglyMeasurable
      unfold positivePart
      fun_prop)]
  have hmoment : positiveMoment reflectedLaw 3 = negativeMoment mu 3 := by
    unfold positiveMoment negativeMoment
    dsimp [reflectedLaw]
    rw [integral_map hreflectMeasurable (by
      apply Continuous.aestronglyMeasurable
      unfold positivePart
      fun_prop)]
    apply integral_congr_ae
    exact ae_of_all mu fun x => by rfl
  have hidentity := weighted_positiveStopLoss_integral_eq reflectedLaw hReflected
  simp_rw [hstop] at hidentity
  rw [hmoment] at hidentity
  exact hidentity

theorem integrable_weightedStopLossKernel_joint
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    Integrable (fun q : ℝ × ℝ => weightedStopLossKernel q.2 q.1)
      ((volume.restrict (Set.Ici 0)).prod mu) := by
  let tau : Measure ℝ := volume.restrict (Set.Ici 0)
  let K : ℝ × ℝ → ℝ := fun q => weightedStopLossKernel q.2 q.1
  let G : ℝ → ℝ := fun x => ∫ t, ‖K (t, x)‖ ∂tau
  have hKstrong : StronglyMeasurable K := by
    dsimp [K]
    unfold weightedStopLossKernel positivePart
    fun_prop
  have hsection (x : ℝ) : Integrable (fun t => K (t, x)) tau := by
    simpa only [tau, K] using integrableOn_weightedStopLossKernel x
  have hGformula (x : ℝ) : G x = (1 / 6 : ℝ) * positivePart x ^ 3 := by
    have hnormIntegral : (∫ t in Set.Ici (0 : ℝ), |K (t, x)|) =
        ∫ t in Set.Ici (0 : ℝ), K (t, x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact abs_of_nonneg (mul_nonneg ht (positivePart_nonneg _))
    dsimp [G, tau]
    rw [hnormIntegral]
    change (∫ t in Set.Ici (0 : ℝ), weightedStopLossKernel x t) =
      (1 / 6 : ℝ) * positivePart x ^ 3
    rw [weightedStopLossKernel_integral]
    ring
  have hGintegrable : Integrable G mu := by
    have hscaled := (integrable_positivePart_cube hX).const_mul (1 / 6 : ℝ)
    exact hscaled.congr (ae_of_all mu fun x => (hGformula x).symm)
  change Integrable K (tau.prod mu)
  apply (integrable_prod_iff' hKstrong.aestronglyMeasurable).2
  constructor
  · exact ae_of_all mu hsection
  · simpa only [G] using hGintegrable

theorem integrable_weighted_positiveStopLoss
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    Integrable (fun t : ℝ => t * positiveStopLoss mu t)
      (volume.restrict (Set.Ici 0)) := by
  have hmarginal := (integrable_weightedStopLossKernel_joint mu hX).integral_prod_left
  apply hmarginal.congr
  exact ae_of_all (volume.restrict (Set.Ici 0)) fun t => by
    change (∫ x, weightedStopLossKernel x t ∂mu) = t * positiveStopLoss mu t
    unfold weightedStopLossKernel positiveStopLoss
    rw [integral_const_mul]

theorem integrable_weighted_negativeStopLoss
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    Integrable (fun t : ℝ => t * negativeStopLoss mu t)
      (volume.restrict (Set.Ici 0)) := by
  let reflect : ℝ → ℝ := fun x => -x
  let reflectedLaw : Measure ℝ := mu.map reflect
  have hreflectMeasurable : AEMeasurable reflect mu := by
    dsimp [reflect]
    fun_prop
  letI : IsProbabilityMeasure reflectedLaw := by
    dsimp [reflectedLaw]
    exact Measure.isProbabilityMeasure_map hreflectMeasurable
  have hReflected : MemLp (id : ℝ → ℝ) 3 reflectedLaw := by
    apply (memLp_map_measure_iff aestronglyMeasurable_id hreflectMeasurable).2
    simpa only [Function.comp_apply, id_eq, reflect] using hX.neg
  have hstop (t : ℝ) : positiveStopLoss reflectedLaw t = negativeStopLoss mu t := by
    unfold positiveStopLoss negativeStopLoss
    dsimp [reflectedLaw]
    rw [integral_map hreflectMeasurable (by
      apply Continuous.aestronglyMeasurable
      unfold positivePart
      fun_prop)]
  have hintegrable := integrable_weighted_positiveStopLoss reflectedLaw hReflected
  apply hintegrable.congr
  exact ae_of_all (volume.restrict (Set.Ici 0)) fun t => by
    change t * positiveStopLoss reflectedLaw t = t * negativeStopLoss mu t
    rw [hstop]

theorem integrable_positiveStopLoss_sq_add_weighted
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0) :
    Integrable (fun t : ℝ => positiveStopLoss mu t ^ 2 + t * positiveStopLoss mu t)
      (volume.restrict (Set.Ici 0)) := by
  have hfull := integrable_full_stopLoss_integrand mu hX hmean
  have hrestricted : IntegrableOn
      (fun t : ℝ => positiveStopLoss mu t * (t + positiveStopLoss mu t))
      (Set.Ici 0) volume := hfull.integrableOn
  apply hrestricted.congr
  exact ae_of_all (volume.restrict (Set.Ici 0)) fun t => by ring

theorem integrable_negativeStopLoss_sq_add_weighted
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0) :
    Integrable (fun t : ℝ => negativeStopLoss mu t ^ 2 + t * negativeStopLoss mu t)
      (volume.restrict (Set.Ici 0)) := by
  let reflect : ℝ → ℝ := fun x => -x
  let reflectedLaw : Measure ℝ := mu.map reflect
  have hreflectMeasurable : AEMeasurable reflect mu := by
    dsimp [reflect]
    fun_prop
  letI : IsProbabilityMeasure reflectedLaw := by
    dsimp [reflectedLaw]
    exact Measure.isProbabilityMeasure_map hreflectMeasurable
  have hReflected : MemLp (id : ℝ → ℝ) 3 reflectedLaw := by
    apply (memLp_map_measure_iff aestronglyMeasurable_id hreflectMeasurable).2
    simpa only [Function.comp_apply, id_eq, reflect] using hX.neg
  have hmeanReflected : ∫ x : ℝ, x ∂reflectedLaw = 0 := by
    calc
      (∫ x : ℝ, x ∂reflectedLaw) = ∫ x, reflect x ∂mu := by
        dsimp [reflectedLaw]
        rw [integral_map hreflectMeasurable (by fun_prop)]
      _ = -(∫ x : ℝ, x ∂mu) := by
        dsimp [reflect]
        rw [integral_neg]
      _ = 0 := by rw [hmean, neg_zero]
  have hstop (t : ℝ) : positiveStopLoss reflectedLaw t = negativeStopLoss mu t := by
    unfold positiveStopLoss negativeStopLoss
    dsimp [reflectedLaw]
    rw [integral_map hreflectMeasurable (by
      apply Continuous.aestronglyMeasurable
      unfold positivePart
      fun_prop)]
  have hintegrable :=
    integrable_positiveStopLoss_sq_add_weighted reflectedLaw hReflected hmeanReflected
  apply hintegrable.congr
  exact ae_of_all (volume.restrict (Set.Ici 0)) fun t => by
    change positiveStopLoss reflectedLaw t ^ 2 + t * positiveStopLoss reflectedLaw t =
      negativeStopLoss mu t ^ 2 + t * negativeStopLoss mu t
    rw [hstop]

theorem integrable_positiveStopLoss_sq
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0) :
    Integrable (fun t : ℝ => positiveStopLoss mu t ^ 2)
      (volume.restrict (Set.Ici 0)) := by
  have hdifference := (integrable_positiveStopLoss_sq_add_weighted mu hX hmean).sub
    (integrable_weighted_positiveStopLoss mu hX)
  apply hdifference.congr
  exact ae_of_all (volume.restrict (Set.Ici 0)) fun t => by
    change (positiveStopLoss mu t ^ 2 + t * positiveStopLoss mu t) -
      t * positiveStopLoss mu t = positiveStopLoss mu t ^ 2
    ring

theorem integrable_negativeStopLoss_sq
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0) :
    Integrable (fun t : ℝ => negativeStopLoss mu t ^ 2)
      (volume.restrict (Set.Ici 0)) := by
  have hdifference := (integrable_negativeStopLoss_sq_add_weighted mu hX hmean).sub
    (integrable_weighted_negativeStopLoss mu hX)
  apply hdifference.congr
  exact ae_of_all (volume.restrict (Set.Ici 0)) fun t => by
    change (negativeStopLoss mu t ^ 2 + t * negativeStopLoss mu t) -
      t * negativeStopLoss mu t = negativeStopLoss mu t ^ 2
    ring

theorem symmetrizedThirdAbsoluteMoment_eq_full_stopLoss_integral
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0) :
    symmetrizedThirdAbsoluteMoment mu =
      12 * ∫ t : ℝ, positiveStopLoss mu t * (t + positiveStopLoss mu t) := by
  rw [symmetrizedThirdAbsoluteMoment_eq_kernel_integral mu hX]
  have hintegrand (t : ℝ) :
      (∫ p : ℝ × ℝ, symmetrizationKernel p.1 p.2 t ∂mu.prod mu) =
        2 * (positiveStopLoss mu t * (t + positiveStopLoss mu t)) := by
    rw [integral_symmetrizationKernel_prod mu hX t,
      reverseStopLoss_eq_add_positiveStopLoss mu hX hmean t]
    ring
  calc
    6 * ∫ t : ℝ, ∫ p : ℝ × ℝ, symmetrizationKernel p.1 p.2 t ∂mu.prod mu =
        6 * ∫ t : ℝ, 2 * (positiveStopLoss mu t * (t + positiveStopLoss mu t)) := by
      congr 1
      apply integral_congr_ae
      exact ae_of_all volume hintegrand
    _ = 12 * ∫ t : ℝ, positiveStopLoss mu t * (t + positiveStopLoss mu t) := by
      rw [integral_const_mul]
      ring

/-- Route B equation (2.1): exact stop-loss decomposition of the symmetrized third moment. -/
theorem symmetrizedThirdAbsoluteMoment_stopLoss_identity
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0) :
    symmetrizedThirdAbsoluteMoment mu = 2 * thirdAbsoluteMoment mu +
      12 * ∫ t in Set.Ici (0 : ℝ),
        positiveStopLoss mu t ^ 2 + negativeStopLoss mu t ^ 2 := by
  let tau : Measure ℝ := volume.restrict (Set.Ici 0)
  have hpositiveSquare := integrable_positiveStopLoss_sq mu hX hmean
  have hnegativeSquare := integrable_negativeStopLoss_sq mu hX hmean
  have hpositiveWeighted := integrable_weighted_positiveStopLoss mu hX
  have hnegativeWeighted := integrable_weighted_negativeStopLoss mu hX
  have hpositiveSplit :
      (∫ t in Set.Ici (0 : ℝ),
        positiveStopLoss mu t ^ 2 + t * positiveStopLoss mu t) =
        (∫ t, positiveStopLoss mu t ^ 2 ∂tau) +
          ∫ t, t * positiveStopLoss mu t ∂tau := by
    exact integral_add hpositiveSquare hpositiveWeighted
  have hnegativeSplit :
      (∫ t in Set.Ici (0 : ℝ),
        negativeStopLoss mu t ^ 2 + t * negativeStopLoss mu t) =
        (∫ t, negativeStopLoss mu t ^ 2 ∂tau) +
          ∫ t, t * negativeStopLoss mu t ∂tau := by
    exact integral_add hnegativeSquare hnegativeWeighted
  have hsquareSum :
      (∫ t in Set.Ici (0 : ℝ),
        positiveStopLoss mu t ^ 2 + negativeStopLoss mu t ^ 2) =
        (∫ t, positiveStopLoss mu t ^ 2 ∂tau) +
          ∫ t, negativeStopLoss mu t ^ 2 ∂tau := by
    exact integral_add hpositiveSquare hnegativeSquare
  rw [symmetrizedThirdAbsoluteMoment_eq_full_stopLoss_integral mu hX hmean,
    full_stopLoss_integral_eq_positive_negative_halves mu hX hmean,
    hpositiveSplit, hnegativeSplit,
    weighted_positiveStopLoss_integral_eq mu hX,
    weighted_negativeStopLoss_integral_eq mu hX,
    hsquareSum]
  rw [← third_absolute_part_moments_add mu hX]
  ring

theorem combined_stopLoss_sq_integral_le_firstMoment
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    3 * ∫ t in Set.Ici (0 : ℝ),
      positiveStopLoss mu t ^ 2 + negativeStopLoss mu t ^ 2 ≤
        positiveMoment mu 1 := by
  let tau : Measure ℝ := volume.restrict (Set.Ici 0)
  have hpositive := positive_stopLoss_sq_integral_le mu hX
  have hnegative := negative_stopLoss_sq_integral_le mu hX
  have hfirstEq := centered_first_part_moments_eq mu hX hmean
  rw [← hfirstEq] at hnegative
  have hsecondParts := second_part_moments_add mu hX
  rw [hsecond] at hsecondParts
  have hpositiveSquare := integrable_positiveStopLoss_sq mu hX hmean
  have hnegativeSquare := integrable_negativeStopLoss_sq mu hX hmean
  have hsquareSum :
      (∫ t in Set.Ici (0 : ℝ),
        positiveStopLoss mu t ^ 2 + negativeStopLoss mu t ^ 2) =
        (∫ t, positiveStopLoss mu t ^ 2 ∂tau) +
          ∫ t, negativeStopLoss mu t ^ 2 ∂tau :=
    integral_add hpositiveSquare hnegativeSquare
  have hcombined := add_le_add hpositive hnegative
  have hrhs : positiveMoment mu 1 * positiveMoment mu 2 +
      positiveMoment mu 1 * negativeMoment mu 2 = positiveMoment mu 1 := by
    calc
      positiveMoment mu 1 * positiveMoment mu 2 +
          positiveMoment mu 1 * negativeMoment mu 2 =
          positiveMoment mu 1 * (positiveMoment mu 2 + negativeMoment mu 2) := by ring
      _ = positiveMoment mu 1 := by rw [hsecondParts, mul_one]
  rw [hrhs] at hcombined
  rw [hsquareSum]
  linarith

theorem symmetrizedThirdAbsoluteMoment_excess_le_firstMoment
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    symmetrizedThirdAbsoluteMoment mu - 2 * thirdAbsoluteMoment mu ≤
      4 * positiveMoment mu 1 := by
  have hidentity := symmetrizedThirdAbsoluteMoment_stopLoss_identity mu hX hmean
  have hhardy := combined_stopLoss_sq_integral_le_firstMoment mu hX hmean hsecond
  linarith

theorem symmetrizedThirdAbsoluteMoment_lower
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0) :
    2 * thirdAbsoluteMoment mu ≤ symmetrizedThirdAbsoluteMoment mu := by
  have hidentity := symmetrizedThirdAbsoluteMoment_stopLoss_identity mu hX hmean
  have hintegralNonneg : 0 ≤ ∫ t in Set.Ici (0 : ℝ),
      positiveStopLoss mu t ^ 2 + negativeStopLoss mu t ^ 2 :=
    integral_nonneg fun t => add_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

theorem symmetrizedThirdAbsoluteMoment_excess_le_absMoment
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    symmetrizedThirdAbsoluteMoment mu - 2 * thirdAbsoluteMoment mu ≤
      2 * ∫ x : ℝ, |x| ∂mu := by
  have hexcess := symmetrizedThirdAbsoluteMoment_excess_le_firstMoment
    mu hX hmean hsecond
  have hfirstEq := centered_first_part_moments_eq mu hX hmean
  have habsParts := first_absolute_part_moments_add mu hX
  linarith

theorem moment_discriminant_eq_four_mul
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) :
    thirdAbsoluteMoment mu ^ 2 - rawThirdMoment mu ^ 2 =
      4 * (positiveMoment mu 3 * negativeMoment mu 3) := by
  have hsum := third_absolute_part_moments_add mu hX
  have hdifference := third_raw_part_moments_sub mu hX
  unfold rawThirdMoment
  rw [← hsum, ← hdifference]
  ring

theorem symmetrizedThirdAbsoluteMoment_excess_le_discriminant
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    symmetrizedThirdAbsoluteMoment mu - 2 * thirdAbsoluteMoment mu ≤
      2 * Real.sqrt (thirdAbsoluteMoment mu ^ 2 - rawThirdMoment mu ^ 2) := by
  have hexcess := symmetrizedThirdAbsoluteMoment_excess_le_firstMoment
    mu hX hmean hsecond
  have hfirstSqrt := positive_firstMoment_le_sqrt_third_product
    mu hX hmean hsecond
  have hscaled : 4 * positiveMoment mu 1 ≤
      4 * Real.sqrt (positiveMoment mu 3 * negativeMoment mu 3) :=
    mul_le_mul_of_nonneg_left hfirstSqrt (by norm_num)
  have hdisc := moment_discriminant_eq_four_mul mu hX
  have hsqrtIdentity :
      4 * Real.sqrt (positiveMoment mu 3 * negativeMoment mu 3) =
        2 * Real.sqrt (thirdAbsoluteMoment mu ^ 2 - rawThirdMoment mu ^ 2) := by
    rw [hdisc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show Real.sqrt (4 : ℝ) = 2 by
      exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)]
    ring
  exact hexcess.trans (hscaled.trans_eq hsqrtIdentity)

theorem symmetrizationRatio_lower
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    1 ≤ symmetrizationRatio mu := by
  have hrho := thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPositive : 0 < thirdAbsoluteMoment mu := lt_of_lt_of_le zero_lt_one hrho
  have hlower := symmetrizedThirdAbsoluteMoment_lower mu hX hmean
  unfold symmetrizationRatio
  exact (le_div_iff₀ (mul_pos (by norm_num) hrhoPositive)).2 (by
    simpa only [one_mul] using hlower)

theorem symmetrizationRatio_upper_absMoment
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    symmetrizationRatio mu ≤
      1 + (∫ x : ℝ, |x| ∂mu) / thirdAbsoluteMoment mu := by
  have hrho := thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPositive : 0 < thirdAbsoluteMoment mu := lt_of_lt_of_le zero_lt_one hrho
  have hexcess := symmetrizedThirdAbsoluteMoment_excess_le_absMoment
    mu hX hmean hsecond
  unfold symmetrizationRatio
  apply (div_le_iff₀ (mul_pos (by norm_num) hrhoPositive)).2
  field_simp
  linarith

theorem symmetrizationRatio_upper
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    symmetrizationRatio mu ≤ 1 + 1 / thirdAbsoluteMoment mu := by
  have hratio := symmetrizationRatio_upper_absMoment mu hX hmean hsecond
  have hrho := thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPositive : 0 < thirdAbsoluteMoment mu := lt_of_lt_of_le zero_lt_one hrho
  have habs := first_absolute_moment_le_one mu hX hsecond
  have hdivision : (∫ x : ℝ, |x| ∂mu) / thirdAbsoluteMoment mu ≤
      1 / thirdAbsoluteMoment mu :=
    (div_le_div_iff_of_pos_right hrhoPositive).2 habs
  linarith

theorem symmetrizationRatio_le_two
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    symmetrizationRatio mu ≤ 2 := by
  have hratio := symmetrizationRatio_upper mu hX hmean hsecond
  have hrho := thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPositive : 0 < thirdAbsoluteMoment mu := lt_of_lt_of_le zero_lt_one hrho
  have hinv : 1 / thirdAbsoluteMoment mu ≤ 1 := by
    exact (div_le_one hrhoPositive).2 hrho
  linarith

theorem symmetrizationRatio_moment_circle
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    (symmetrizationRatio mu - 1) ^ 2 +
      (rawThirdMoment mu / thirdAbsoluteMoment mu) ^ 2 ≤ 1 := by
  let rho := thirdAbsoluteMoment mu
  let m := symmetrizedThirdAbsoluteMoment mu
  let kappa := rawThirdMoment mu
  have hrho := thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPositive : 0 < rho := by dsimp [rho]; linarith
  have hdenPositive : 0 < 4 * rho ^ 2 := by positivity
  have hexcessNonneg : 0 ≤ m - 2 * rho := by
    dsimp [m, rho]
    linarith [symmetrizedThirdAbsoluteMoment_lower mu hX hmean]
  have hdiscNonneg : 0 ≤ rho ^ 2 - kappa ^ 2 := by
    dsimp [rho, kappa]
    rw [moment_discriminant_eq_four_mul mu hX]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (positiveMoment_nonneg mu 3) (negativeMoment_nonneg mu 3))
  have hexcess := symmetrizedThirdAbsoluteMoment_excess_le_discriminant
    mu hX hmean hsecond
  change m - 2 * rho ≤ 2 * Real.sqrt (rho ^ 2 - kappa ^ 2) at hexcess
  have hsquared : (m - 2 * rho) ^ 2 ≤ 4 * (rho ^ 2 - kappa ^ 2) := by
    calc
      (m - 2 * rho) ^ 2 ≤
          (2 * Real.sqrt (rho ^ 2 - kappa ^ 2)) ^ 2 := by
        simpa only [pow_two] using mul_self_le_mul_self hexcessNonneg hexcess
      _ = 4 * (rho ^ 2 - kappa ^ 2) := by
        rw [mul_pow, Real.sq_sqrt hdiscNonneg]
        ring
  have hratioIdentity : symmetrizationRatio mu - 1 =
      (m - 2 * rho) / (2 * rho) := by
    dsimp [symmetrizationRatio, m, rho]
    field_simp
  rw [hratioIdentity]
  change ((m - 2 * rho) / (2 * rho)) ^ 2 + (kappa / rho) ^ 2 ≤ 1
  have hfraction : ((m - 2 * rho) / (2 * rho)) ^ 2 + (kappa / rho) ^ 2 =
      ((m - 2 * rho) ^ 2 + 4 * kappa ^ 2) / (4 * rho ^ 2) := by
    field_simp
    ring
  rw [hfraction]
  apply (div_le_iff₀ hdenPositive).2
  nlinarith

end

end BerryEsseen
