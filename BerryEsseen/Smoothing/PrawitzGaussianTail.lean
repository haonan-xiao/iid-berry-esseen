import BerryEsseen.Smoothing.PrawitzE1
import BerryEsseen.Smoothing.ExplicitSmoothing
import BerryEsseen.Smoothing.PrawitzDbound
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gaussian-tail representation for Route B

This module closes the analytic change-of-variables step between the improper Gaussian tail in
`routeBU` and the shifted exponential integral certified by `PrawitzE1`.  The result is stated
first for a general positive quadratic coefficient and then specialized to Route B's smoothing
frequency.
-/

open Filter MeasureTheory Set Real

namespace BerryEsseen

noncomputable section

def routeBE1StandardIntegrand (u : ℝ) : ℝ :=
  Real.exp (-u) / u

theorem routeBE1StandardIntegrand_continuousOn {x : ℝ} (hx : 0 < x) :
    ContinuousOn routeBE1StandardIntegrand (Set.Ici x) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro u hu
  change x ≤ u at hu
  linarith

theorem routeBE1StandardIntegrand_integrableOn_Ioi {x : ℝ} (hx : 0 < x) :
    IntegrableOn routeBE1StandardIntegrand (Set.Ioi x) := by
  have hg : IntegrableOn (fun u : ℝ => (1 / x) * Real.exp (-u)) (Set.Ioi x) :=
    (integrableOn_exp_neg_Ioi x).const_mul (1 / x)
  have hmeas : AEStronglyMeasurable routeBE1StandardIntegrand
      (volume.restrict (Set.Ioi x)) :=
    ContinuousOn.aestronglyMeasurable
      ((routeBE1StandardIntegrand_continuousOn hx).mono Set.Ioi_subset_Ici_self)
      measurableSet_Ioi
  refine hg.mono' hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  change x < u at hu
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · unfold routeBE1StandardIntegrand
    calc
      Real.exp (-u) / u ≤ Real.exp (-u) / x := by
        exact div_le_div_of_nonneg_left (Real.exp_pos _).le hx hu.le
      _ = (1 / x) * Real.exp (-u) := by ring
  · exact div_nonneg (Real.exp_pos _).le (le_trans hx.le hu.le)

theorem routeBE1StandardIntegrand_integrableOn_Ici {x : ℝ} (hx : 0 < x) :
    IntegrableOn routeBE1StandardIntegrand (Set.Ici x) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact routeBE1StandardIntegrand_integrableOn_Ioi hx

/-- The shifted definition used by `E1up` equals the standard exponential-integral tail. -/
theorem routeBE1_eq_integral_Ioi {x : ℝ} (hx : 0 < x) :
    routeBE1 x = ∫ u in Set.Ioi x, routeBE1StandardIntegrand u := by
  have hshift :
      (∫ y in Set.Ioi (0 : ℝ),
          (routeBE1StandardIntegrand ∘ (fun y : ℝ => x + y)) y * 1) =
        ∫ u in Set.Ioi (x + 0), routeBE1StandardIntegrand u := by
    refine MeasureTheory.integral_comp_mul_deriv_Ioi
      (f := fun y : ℝ => x + y) (f' := fun _ : ℝ => 1)
      (g := routeBE1StandardIntegrand) (a := 0) ?_ ?_ ?_ ?_ ?_ ?_
    · fun_prop
    · simpa only [id_eq] using
        (Filter.Tendsto.add_atTop tendsto_const_nhds Filter.tendsto_id :
          Tendsto (fun y : ℝ => x + id y) atTop atTop)
    · intro y hy
      simpa using ((hasDerivAt_const y x).add (hasDerivAt_id y)).hasDerivWithinAt
    · simpa only [Set.image_const_add_Ioi, add_zero] using
        (routeBE1StandardIntegrand_continuousOn hx).mono Set.Ioi_subset_Ici_self
    · simpa only [Set.image_const_add_Ici, add_zero] using
        routeBE1StandardIntegrand_integrableOn_Ici hx
    · have hbase : IntegrableOn (routeBE1Integrand x) (Set.Ici (0 : ℝ)) := by
        rw [integrableOn_Ici_iff_integrableOn_Ioi]
        exact routeBE1Integrand_integrableOn_Ioi hx
      have hscaled := hbase.const_mul (Real.exp (-x))
      simpa only [Function.comp_apply, mul_one, routeBE1StandardIntegrand,
        routeBE1Integrand, show ∀ y : ℝ, -(x + y) = -x + -y by intro y; ring,
        Real.exp_add, mul_div_assoc] using hscaled
  unfold routeBE1
  rw [← MeasureTheory.integral_const_mul]
  calc
    (∫ y in Set.Ioi (0 : ℝ), Real.exp (-x) * routeBE1Integrand x y) =
        ∫ y in Set.Ioi (0 : ℝ),
          (routeBE1StandardIntegrand ∘ (fun y : ℝ => x + y)) y * 1 := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      simp only [Function.comp_apply, mul_one, routeBE1StandardIntegrand,
        routeBE1Integrand]
      rw [show -(x + y) = -x + -y by ring, Real.exp_add]
      ring
    _ = ∫ u in Set.Ioi x, routeBE1StandardIntegrand u := by
      simpa only [add_zero] using hshift

def routeBQuadraticGaussianTailIntegrand (a t : ℝ) : ℝ :=
  Real.exp (-(a * t ^ 2)) / t

theorem routeBQuadraticGaussianTailIntegrand_integrableOn_Ici
    {a t₀ : ℝ} (ha : 0 < a) (ht₀ : 0 < t₀) :
    IntegrableOn (routeBQuadraticGaussianTailIntegrand a) (Set.Ici t₀) := by
  have hg : IntegrableOn
      (fun t : ℝ => (1 / t₀) * Real.exp (-a * t ^ 2)) (Set.Ici t₀) :=
    (integrable_exp_neg_mul_sq ha).integrableOn.const_mul (1 / t₀)
  have hmeas : AEStronglyMeasurable (routeBQuadraticGaussianTailIntegrand a)
      (volume.restrict (Set.Ici t₀)) :=
    ContinuousOn.aestronglyMeasurable
      (by
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro t ht
        change t₀ ≤ t at ht
        linarith)
      measurableSet_Ici
  refine hg.mono' hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ici] with t ht
  change t₀ ≤ t at ht
  have htPos : 0 < t := ht₀.trans_le ht
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · unfold routeBQuadraticGaussianTailIntegrand
    calc
      Real.exp (-(a * t ^ 2)) / t ≤ Real.exp (-(a * t ^ 2)) / t₀ := by
        exact div_le_div_of_nonneg_left (Real.exp_pos _).le ht₀ ht
      _ = (1 / t₀) * Real.exp (-a * t ^ 2) := by ring
  · exact div_nonneg (Real.exp_pos _).le htPos.le

/-- Quadratic substitution `u = a t²` for the positive Gaussian tail. -/
theorem integral_routeBQuadraticGaussianTail_eq_routeBE1
    {a t₀ : ℝ} (ha : 0 < a) (ht₀ : 0 < t₀) :
    (∫ t in Set.Ici t₀, routeBQuadraticGaussianTailIntegrand a t) =
      routeBE1 (a * t₀ ^ 2) / 2 := by
  have hx : 0 < a * t₀ ^ 2 := mul_pos ha (sq_pos_of_pos ht₀)
  let f : ℝ → ℝ := fun t => a * t ^ 2
  let f' : ℝ → ℝ := fun t => 2 * a * t
  have hstrict : StrictMonoOn f (Set.Ici t₀) := by
    intro s hs t ht hst
    change t₀ ≤ s at hs
    change t₀ ≤ t at ht
    have hsPos : 0 < s := ht₀.trans_le hs
    have hsumPos : 0 < t + s := add_pos (hsPos.trans hst) hsPos
    have hdiffPos : 0 < t - s := sub_pos.mpr hst
    have hsqDiff : 0 < t ^ 2 - s ^ 2 := by
      nlinarith [mul_pos hdiffPos hsumPos]
    change a * s ^ 2 < a * t ^ 2
    nlinarith [mul_pos ha hsqDiff]
  have hmono : MonotoneOn f (Set.Ici t₀) := hstrict.monotoneOn
  have htailInt := routeBQuadraticGaussianTailIntegrand_integrableOn_Ici ha ht₀
  have hcompInt : IntegrableOn
      (fun t => (routeBE1StandardIntegrand ∘ f) t * f' t) (Set.Ici t₀) := by
    have htwice := htailInt.const_mul 2
    refine IntegrableOn.congr_fun htwice ?_ measurableSet_Ici
    intro t ht
    change t₀ ≤ t at ht
    have htPos : 0 < t := ht₀.trans_le ht
    dsimp only [f, f', Function.comp_apply]
    unfold routeBE1StandardIntegrand routeBQuadraticGaussianTailIntegrand
    field_simp [ha.ne', htPos.ne']
    <;> ring
  have hsubst :
      (∫ t in Set.Ioi t₀, (routeBE1StandardIntegrand ∘ f) t * f' t) =
        ∫ u in Set.Ioi (f t₀), routeBE1StandardIntegrand u := by
    refine MeasureTheory.integral_comp_mul_deriv_Ioi
      (f := f) (f' := f') (g := routeBE1StandardIntegrand) (a := t₀)
      ?_ ?_ ?_ ?_ ?_ hcompInt
    · dsimp only [f]
      fun_prop
    · dsimp only [f]
      have hsq : Tendsto (fun t : ℝ => t * t) atTop atTop :=
        Filter.tendsto_id.atTop_mul_atTop₀ Filter.tendsto_id
      exact Filter.Tendsto.const_mul_atTop ha (by simpa only [pow_two] using hsq)
    · intro t ht
      dsimp only [f, f']
      have hderiv := (hasDerivAt_pow 2 t).const_mul a
      convert hderiv.hasDerivWithinAt using 1 <;> norm_num <;> ring
    · exact (routeBE1StandardIntegrand_continuousOn hx).mono
        (hstrict.image_Ioi_subset.trans Set.Ioi_subset_Ici_self)
    · exact (routeBE1StandardIntegrand_integrableOn_Ici hx).mono_set
        hmono.image_Ici_subset
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have htwice :
      2 * (∫ t in Set.Ioi t₀, routeBQuadraticGaussianTailIntegrand a t) =
        routeBE1 (a * t₀ ^ 2) := by
    calc
      2 * (∫ t in Set.Ioi t₀, routeBQuadraticGaussianTailIntegrand a t) =
          ∫ t in Set.Ioi t₀, 2 * routeBQuadraticGaussianTailIntegrand a t := by
        rw [MeasureTheory.integral_const_mul]
      _ = ∫ t in Set.Ioi t₀,
          (routeBE1StandardIntegrand ∘ f) t * f' t := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change t₀ < t at ht
        have htPos : 0 < t := ht₀.trans ht
        dsimp only [f, f', Function.comp_apply]
        unfold routeBE1StandardIntegrand routeBQuadraticGaussianTailIntegrand
        field_simp [ha.ne', htPos.ne']
        <;> ring
      _ = ∫ u in Set.Ioi (f t₀), routeBE1StandardIntegrand u := hsubst
      _ = routeBE1 (a * t₀ ^ 2) := by
        dsimp only [f]
        exact (routeBE1_eq_integral_Ioi hx).symm
  linarith

/-- The quadratic coefficient used by the exact checker's Gaussian-tail argument. -/
def routeBTailCoefficient (n : ℕ) (rho z : ℝ) : ℝ :=
  2 * (n : ℝ) * Real.pi ^ 2 / routeBDboundW rho z ^ 2

def routeBTailArgument (n : ℕ) (rho z : ℝ) : ℝ :=
  routeBTailCoefficient n rho z * prawitzSplit ^ 2

theorem routeBTailCoefficient_pos
    {n : ℕ} (hn : 0 < n) {rho z : ℝ} (hrho : 0 < rho) (hz : 0 ≤ z) :
    0 < routeBTailCoefficient n rho z := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw : 0 < routeBDboundW rho z := by
    unfold routeBDboundW
    positivity
  unfold routeBTailCoefficient
  positivity

theorem routeBSmoothingT_sq_div_two_eq_routeBTailCoefficient
    {n : ℕ} (hn : 0 < n) {rho z : ℝ} (hrho : 0 < rho) (hz : 0 ≤ z) :
    routeBSmoothingT n rho (routeBDboundR rho z) ^ 2 / 2 =
      routeBTailCoefficient n rho z := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hw : 0 < routeBDboundW rho z := by
    unfold routeBDboundW
    positivity
  unfold routeBSmoothingT routeBSmoothingScale routeBDboundR routeBTailCoefficient
  field_simp [hrho.ne', hsqrt.ne', hw.ne']
  rw [Real.sq_sqrt hnR.le]

theorem routeBPowerGaussianTail_eq_routeBE1
    {n : ℕ} (hn : 0 < n) {rho z : ℝ} (hrho : 0 < rho) (hz : 0 ≤ z) :
    (∫ t in Set.Ici prawitzSplit,
        routeBPowerGaussianEnvelope n rho (routeBDboundR rho z) t / t) =
      routeBE1 (routeBTailArgument n rho z) / 2 := by
  have hr : 0 < routeBDboundR rho z := by
    unfold routeBDboundR routeBDboundW
    positivity
  have hcoeff := routeBSmoothingT_sq_div_two_eq_routeBTailCoefficient hn hrho hz
  have hgeneral := integral_routeBQuadraticGaussianTail_eq_routeBE1
    (routeBTailCoefficient_pos hn hrho hz)
    (by norm_num [prawitzSplit] : (0 : ℝ) < prawitzSplit)
  calc
    (∫ t in Set.Ici prawitzSplit,
        routeBPowerGaussianEnvelope n rho (routeBDboundR rho z) t / t) =
        ∫ t in Set.Ici prawitzSplit,
          routeBQuadraticGaussianTailIntegrand (routeBTailCoefficient n rho z) t := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
      intro t ht
      change routeBPowerGaussianEnvelope n rho (routeBDboundR rho z) t / t = _
      rw [routeBPowerGaussianEnvelope_eq_smoothing_gaussian hn hrho hr]
      unfold routeBQuadraticGaussianTailIntegrand
      congr 2
      rw [← hcoeff]
      ring
    _ = routeBE1 (routeBTailArgument n rho z) / 2 := by
      simpa only [routeBTailArgument] using hgeneral

/-- The normalized fourth term in `routeBU`, in the exact algebraic form evaluated by the
checker after its call to `E1up`. -/
theorem routeB_normalizedGaussianTail_eq
    {n : ℕ} (hn : 0 < n) {rho z : ℝ} (hrho : 0 < rho) (hz : 0 ≤ z) :
    Real.sqrt (n : ℝ) / rho *
        ((1 / Real.pi) * ∫ t in Set.Ici prawitzSplit,
          routeBPowerGaussianEnvelope n rho (routeBDboundR rho z) t / t) =
      Real.sqrt (n : ℝ) / rho *
        (routeBE1 (routeBTailArgument n rho z) / (2 * Real.pi)) := by
  rw [routeBPowerGaussianTail_eq_routeBE1 hn hrho hz]
  ring

end

end BerryEsseen
