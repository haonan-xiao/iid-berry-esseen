import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

/-!
# Verified exponential-integral upper rule

This module formalizes the analytic argument behind `E1up` in the Route B checker.  It defines the
shifted representation of the exponential integral, proves that its integrand is nonnegative,
decreasing, convex, and integrable, proves a generic composite-trapezoid upper rule for convex
functions, and bounds the omitted interval `[24, ∞)` by `exp (-24) / (x + 24)`.  The resulting
theorem is the real-valued specification implemented by the dyadic checker module.
-/

open Finset MeasureTheory intervalIntegral Set Real

namespace BerryEsseen

noncomputable section

def routeBE1Integrand (x y : ℝ) : ℝ := Real.exp (-y) / (x + y)

/-- Shifted representation `E₁(x) = exp(-x) ∫₀∞ exp(-y)/(x+y) dy`. -/
def routeBE1 (x : ℝ) : ℝ :=
  Real.exp (-x) * ∫ y in Set.Ioi 0, routeBE1Integrand x y

theorem routeBE1Integrand_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    0 ≤ routeBE1Integrand x y := by
  exact div_nonneg (Real.exp_pos _).le (add_nonneg hx.le hy)

theorem routeBE1Integrand_antitone {x : ℝ} (hx : 0 < x) :
    AntitoneOn (routeBE1Integrand x) (Set.Ici 0) := by
  intro a ha b hb hab
  change 0 ≤ a at ha
  change 0 ≤ b at hb
  unfold routeBE1Integrand
  have hxa : 0 < x + a := by linarith
  have hden : 1 / (x + b) ≤ 1 / (x + a) :=
    one_div_le_one_div_of_le hxa (by linarith)
  have hexp : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul hexp (by simpa only [one_div] using hden)
    (inv_nonneg.mpr (by linarith)) (Real.exp_pos _).le

theorem routeBE1Integrand_convexOn {x : ℝ} (hx : 0 < x) :
    ConvexOn ℝ (Set.Ici 0) (routeBE1Integrand x) := by
  have hexp : ConvexOn ℝ (Set.Ici 0) (fun y : ℝ => Real.exp (-y)) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro a ha b hb ca cb hca hcb hsum
    have h := convexOn_exp.2 (Set.mem_univ (-a)) (Set.mem_univ (-b)) hca hcb hsum
    simp only [smul_eq_mul] at h ⊢
    rw [show -(ca * a + cb * b) = ca * (-a) + cb * (-b) by ring]
    exact h
  have hinv : ConvexOn ℝ (Set.Ici 0) (fun y : ℝ => (x + y)⁻¹) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro a ha b hb ca cb hca hcb hsum
    change 0 ≤ a at ha
    change 0 ≤ b at hb
    have hxa : 0 < x + a := by linarith
    have hxb : 0 < x + b := by linarith
    have h := (convexOn_zpow (-1 : ℤ)).2 hxa hxb hca hcb hsum
    have harg : ca • (x + a) + cb • (x + b) = x + (ca * a + cb * b) := by
      simp only [smul_eq_mul]
      nlinarith
    rw [harg] at h
    simpa only [zpow_neg_one, smul_eq_mul] using h
  have hexpAnti : AntitoneOn (fun y : ℝ => Real.exp (-y)) (Set.Ici 0) := by
    intro a ha b hb hab
    exact Real.exp_le_exp.mpr (neg_le_neg hab)
  have hinvAnti : AntitoneOn (fun y : ℝ => (x + y)⁻¹) (Set.Ici 0) := by
    intro a ha b hb hab
    change 0 ≤ a at ha
    change 0 ≤ b at hb
    exact inv_anti₀ (by linarith) (by linarith)
  simpa only [routeBE1Integrand, div_eq_mul_inv] using
    hexp.mul hinv (fun _ _ => (Real.exp_pos _).le)
      (fun y hy => (inv_pos.mpr (by change 0 ≤ y at hy; linarith)).le)
      (hexpAnti.monovaryOn hinvAnti)

/-- The endpoint chord of a convex function upper-bounds its integral. -/
theorem intervalIntegral_le_trapezoid_of_convexOn
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ConvexOn ℝ (Set.Icc a b) f)
    (hint : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x) ≤ (b - a) / 2 * (f a + f b) := by
  rcases hab.eq_or_lt with rfl | hablt
  · simp
  let g : ℝ → ℝ := fun x =>
    ((b - x) / (b - a)) * f a + ((x - a) / (b - a)) * f b
  have hpoint : ∀ x ∈ Set.Icc a b, f x ≤ g x := by
    intro x hx
    have hca : 0 ≤ (b - x) / (b - a) := div_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hab)
    have hcb : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hab)
    have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
      field_simp [(sub_pos.mpr hablt).ne']
      ring
    have hcombo := hf.2 (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
      hca hcb hsum
    have hxcombo : ((b - x) / (b - a)) • a + ((x - a) / (b - a)) • b = x := by
      simp only [smul_eq_mul]
      field_simp [(sub_pos.mpr hablt).ne']
      ring
    rw [hxcombo] at hcombo
    simpa only [g, smul_eq_mul] using hcombo
  calc
    (∫ x in a..b, f x) ≤ ∫ x in a..b, g x := by
      exact intervalIntegral.integral_mono_on hab hint
        ((by fun_prop : Continuous g).intervalIntegrable a b) hpoint
    _ = (b - a) / 2 * (f a + f b) := by
      change (∫ x in a..b,
        ((b - x) / (b - a)) * f a + ((x - a) / (b - a)) * f b) = _
      have hleft : (∫ x in a..b, (b - x) / (b - a)) = (b - a) / 2 := by
        rw [intervalIntegral.integral_div,
          intervalIntegral.integral_sub _root_.intervalIntegrable_const intervalIntegrable_id,
          intervalIntegral.integral_const, integral_id]
        simp only [smul_eq_mul]
        field_simp [(sub_pos.mpr hablt).ne']
        ring
      have hright : (∫ x in a..b, (x - a) / (b - a)) = (b - a) / 2 := by
        rw [intervalIntegral.integral_div,
          intervalIntegral.integral_sub intervalIntegrable_id _root_.intervalIntegrable_const,
          intervalIntegral.integral_const, integral_id]
        simp only [smul_eq_mul]
        field_simp [(sub_pos.mpr hablt).ne']
        ring
      rw [intervalIntegral.integral_add
        ((by fun_prop : Continuous (fun x : ℝ => ((b - x) / (b - a)) * f a)).intervalIntegrable a b)
        ((by fun_prop : Continuous (fun x : ℝ => ((x - a) / (b - a)) * f b)).intervalIntegrable a b),
        intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
        hleft, hright]
      ring

/-- A composite trapezoidal rule upper-bounds a convex integrand. -/
theorem intervalIntegral_le_composite_trapezoid_of_convexOn
    {f : ℝ → ℝ} {a b : ℝ} {N : ℕ} (hab : a ≤ b) (hN : 0 < N)
    (hf : ConvexOn ℝ (Set.Icc a b) f)
    (hint : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x) ≤ trapezoidal_integral f N a b := by
  let h : ℝ := (b - a) / N
  let p : ℕ → ℝ := fun k => a + k * h
  have hh0 : 0 ≤ h := div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg N)
  have hp0 : p 0 = a := by simp [p]
  have hpN : p N = b := by
    dsimp [p, h]
    field_simp [Nat.cast_ne_zero.mpr hN.ne']
    ring
  have hpmono : ∀ k, p k ≤ p (k + 1) := by
    intro k
    simp only [p, add_le_add_iff_left, Nat.cast_add, Nat.cast_one]
    nlinarith
  have hpk : ∀ k < N, a ≤ p k ∧ p (k + 1) ≤ b := by
    intro k hk
    constructor
    · simp only [p, le_add_iff_nonneg_right]
      positivity
    · have hkN : (k + 1 : ℕ) ≤ N := Nat.succ_le_iff.mpr hk
      simp only [p]
      calc
        a + (k + 1 : ℕ) * h ≤ a + N * h := by
          gcongr
        _ = b := hpN
  have hcellInt : ∀ k < N, IntervalIntegrable f volume (p k) (p (k + 1)) := by
    intro k hk
    have hleft : p k ∈ Set.uIcc a b :=
      Set.mem_uIcc_of_le (hpk k hk).1 ((hpmono k).trans (hpk k hk).2)
    have hright : p (k + 1) ∈ Set.uIcc a b :=
      Set.mem_uIcc_of_le ((hpk k hk).1.trans (hpmono k)) (hpk k hk).2
    exact IntervalIntegrable.mono hint
      (Set.uIcc_subset_uIcc hleft hright) le_rfl
  calc
    (∫ x in a..b, f x) = ∑ k ∈ Finset.range N, ∫ x in p k..p (k + 1), f x := by
      rw [intervalIntegral.sum_integral_adjacent_intervals hcellInt, hp0, hpN]
    _ ≤ ∑ k ∈ Finset.range N,
        trapezoidal_integral f 1 (p k) (p (k + 1)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN := Finset.mem_range.mp hk
      have hconvCell : ConvexOn ℝ (Set.Icc (p k) (p (k + 1))) f :=
        hf.subset (Set.Icc_subset_Icc (hpk k hkN).1 (hpk k hkN).2)
          (convex_Icc _ _)
      simpa [trapezoidal_integral_one] using
        intervalIntegral_le_trapezoid_of_convexOn (hpmono k) hconvCell (hcellInt k hkN)
    _ = trapezoidal_integral f N a b := by
      rw [show b = a + N * h by symm; exact hpN]
      simpa only [p, Nat.cast_add, Nat.cast_one] using sum_trapezoidal_integral_adjacent_intervals
        (f := f) (a := a) (h := h) hN

theorem routeBE1Integrand_continuousOn {x : ℝ} (hx : 0 < x) :
    ContinuousOn (routeBE1Integrand x) (Set.Ici 0) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro y hy
  change 0 ≤ y at hy
  linarith

theorem routeBE1Integrand_integrableOn_Ioi {x : ℝ} (hx : 0 < x) :
    IntegrableOn (routeBE1Integrand x) (Set.Ioi 0) := by
  have hg : IntegrableOn (fun y : ℝ => (1 / x) * Real.exp (-y)) (Set.Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).const_mul (1 / x)
  have hmeas : AEStronglyMeasurable (routeBE1Integrand x)
      (volume.restrict (Set.Ioi 0)) :=
    ContinuousOn.aestronglyMeasurable
      ((routeBE1Integrand_continuousOn hx).mono Set.Ioi_subset_Ici_self)
      measurableSet_Ioi
  refine hg.mono' hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
  change 0 < y at hy
  rw [Real.norm_eq_abs, abs_of_nonneg (routeBE1Integrand_nonneg hx hy.le)]
  unfold routeBE1Integrand
  calc
    Real.exp (-y) / (x + y) ≤ Real.exp (-y) / x := by
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hx (by linarith)
    _ = (1 / x) * Real.exp (-y) := by ring

theorem routeBE1Integrand_antitone_parameter {x₀ x y : ℝ}
    (hx₀ : 0 < x₀) (hxx : x₀ ≤ x) (hy : 0 ≤ y) :
    routeBE1Integrand x y ≤ routeBE1Integrand x₀ y := by
  unfold routeBE1Integrand
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by linarith) (by linarith)

/-- The shifted exponential integral is decreasing in its positive parameter. -/
theorem routeBE1_antitoneOn : AntitoneOn routeBE1 (Set.Ioi 0) := by
  intro x₀ hx₀ x hx hxx
  change 0 < x₀ at hx₀
  change 0 < x at hx
  have hInt : (∫ y in Set.Ioi 0, routeBE1Integrand x y) ≤
      ∫ y in Set.Ioi 0, routeBE1Integrand x₀ y := by
    apply MeasureTheory.integral_mono_ae
      (routeBE1Integrand_integrableOn_Ioi hx)
      (routeBE1Integrand_integrableOn_Ioi hx₀)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    exact routeBE1Integrand_antitone_parameter hx₀ hxx hy.le
  have hIntNonneg : 0 ≤ ∫ y in Set.Ioi 0, routeBE1Integrand x y := by
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    exact routeBE1Integrand_nonneg hx hy.le
  unfold routeBE1
  exact mul_le_mul (Real.exp_le_exp.mpr (neg_le_neg hxx)) hInt
    hIntNonneg (Real.exp_pos _).le

theorem routeBE1Integrand_tail_le {x : ℝ} (hx : 0 < x) :
    (∫ y in Set.Ioi 24, routeBE1Integrand x y) ≤
      Real.exp (-24) / (x + 24) := by
  have hf : IntegrableOn (routeBE1Integrand x) (Set.Ioi 24) :=
    (routeBE1Integrand_integrableOn_Ioi hx).mono_set (Set.Ioi_subset_Ioi (by norm_num))
  have hg : IntegrableOn (fun y : ℝ => (1 / (x + 24)) * Real.exp (-y)) (Set.Ioi 24) :=
    (integrableOn_exp_neg_Ioi 24).const_mul (1 / (x + 24))
  calc
    (∫ y in Set.Ioi 24, routeBE1Integrand x y) ≤
        ∫ y in Set.Ioi 24, (1 / (x + 24)) * Real.exp (-y) := by
      apply MeasureTheory.integral_mono_ae hf hg
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
      change 24 < y at hy
      unfold routeBE1Integrand
      rw [div_eq_mul_inv]
      have hinv : (x + y)⁻¹ ≤ (x + 24)⁻¹ := inv_anti₀ (by linarith) (by linarith)
      calc
        Real.exp (-y) * (x + y)⁻¹ ≤ Real.exp (-y) * (x + 24)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le
        _ = 1 / (x + 24) * Real.exp (-y) := by ring
    _ = Real.exp (-24) / (x + 24) := by
      rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi]
      ring

/-- Real-valued specification of the checker expression `E1up`. -/
def routeBE1CheckerUpper (x : ℝ) : ℝ :=
  Real.exp (-x) *
    (trapezoidal_integral (routeBE1Integrand x) (24 * 32) 0 24 +
      Real.exp (-24) / (x + 24))

theorem routeBE1_le_checkerUpper {x : ℝ} (hx : 0 < x) :
    routeBE1 x ≤ routeBE1CheckerUpper x := by
  have hfinite : (∫ y in (0 : ℝ)..24, routeBE1Integrand x y) ≤
      trapezoidal_integral (routeBE1Integrand x) (24 * 32) 0 24 := by
    apply intervalIntegral_le_composite_trapezoid_of_convexOn (by norm_num) (by norm_num)
    · exact (routeBE1Integrand_convexOn hx).subset Set.Icc_subset_Ici_self (convex_Icc _ _)
    · exact ((routeBE1Integrand_continuousOn hx).mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc
        (by norm_num)
  have hsplit :
      (∫ y in (0 : ℝ)..24, routeBE1Integrand x y) +
          (∫ y in Set.Ioi 24, routeBE1Integrand x y) =
        ∫ y in Set.Ioi 0, routeBE1Integrand x y := by
    exact intervalIntegral.integral_interval_add_Ioi
      (routeBE1Integrand_integrableOn_Ioi hx)
      ((routeBE1Integrand_integrableOn_Ioi hx).mono_set
        (Set.Ioi_subset_Ioi (by norm_num)))
  unfold routeBE1 routeBE1CheckerUpper
  rw [← hsplit]
  gcongr
  exact routeBE1Integrand_tail_le hx

end

end BerryEsseen
