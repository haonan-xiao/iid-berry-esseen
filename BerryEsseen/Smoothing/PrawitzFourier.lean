import BerryEsseen.Smoothing.PrawitzMajorant
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import StatLean.HypothesisTesting.ForMathlib.EsseenSmoothing

/-!
# Fourier infrastructure for the Prawitz majorant

This file builds the ordinary-function part of equation (4.4).  In
particular, it exposes the Fejer kernel as a public continuous complex-valued
function, proves its exact Fourier transform, and proves the integer-shift
partition of unity used to identify the real-space and Fourier-space forms of
Vaaler's approximant.
-/

open Filter MeasureTheory Set
open scoped FourierTransform Real Topology

namespace BerryEsseen

noncomputable section

/-- The complexification of the removable squared-sinc kernel `prawitzJ`. -/
def prawitzJC (x : ℝ) : ℂ := (prawitzJ x : ℝ)

@[simp]
theorem prawitzJC_neg (x : ℝ) : prawitzJC (-x) = prawitzJC x := by
  rw [prawitzJC, prawitzJC, prawitzJ_neg]

theorem prawitzJ_eq_sinc (x : ℝ) :
    prawitzJ x = Real.sinc (Real.pi * x) ^ 2 := by
  by_cases hx : x = 0
  · simp [prawitzJ, hx]
  · rw [prawitzJ_eq_sincSq hx, Real.sinc_of_ne_zero]
    exact mul_ne_zero Real.pi_ne_zero hx

theorem continuous_prawitzJ : Continuous prawitzJ := by
  rw [funext prawitzJ_eq_sinc]
  fun_prop

theorem continuous_prawitzJC : Continuous prawitzJC := by
  unfold prawitzJC
  exact Complex.continuous_ofReal.comp continuous_prawitzJ

theorem integrable_prawitzJC : Integrable prawitzJC := by
  let raw : ℝ → ℂ := fun x =>
    ((((Real.sin (Real.pi * x) / (Real.pi * x)) ^ 2 : ℝ) : ℂ))
  have hraw : Integrable raw := by
    exact (MeasureTheory.Integrable.comp_mul_left'
      StatLean.HypothesisTesting.integrable_sin_div_sq Real.pi_ne_zero).ofReal
  have hae : prawitzJC =ᵐ[volume] raw := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    simp only [prawitzJC, raw]
    rw [prawitzJ_eq_sincSq hx0]
  exact hraw.congr hae.symm

/-- The Fejer/triangle Fourier pair, now stated for the removable kernel used
by this development. -/
theorem fourier_prawitzJC :
    FourierTransform.fourier prawitzJC = fun t : ℝ =>
      ((StatLean.HypothesisTesting.tent t : ℝ) : ℂ) := by
  let raw : ℝ → ℂ := fun x =>
    ((((Real.sin (Real.pi * x) / (Real.pi * x)) ^ 2 : ℝ) : ℂ))
  have hraw := StatLean.HypothesisTesting.fourier_sqSincC
  change FourierTransform.fourier raw = fun t : ℝ =>
    ((StatLean.HypothesisTesting.tent t : ℝ) : ℂ) at hraw
  have hae : prawitzJC =ᵐ[volume] raw := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    simp only [prawitzJC, raw]
    rw [prawitzJ_eq_sincSq hx0]
  funext t
  rw [Real.fourier_congr_ae hae t]
  exact congrFun hraw t

private theorem prawitzJ_le_inv_sq {x : ℝ} (hx : x ≠ 0) :
    prawitzJ x ≤ (x ^ 2)⁻¹ := by
  rw [prawitzJ_eq_sincSq hx]
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hnum : Real.sin (Real.pi * x) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  have hdenom : 0 < Real.pi ^ 2 * x ^ 2 := mul_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_ne_zero hx)
  rw [div_pow]
  calc
    Real.sin (Real.pi * x) ^ 2 / (Real.pi * x) ^ 2 ≤
        1 / (Real.pi * x) ^ 2 := by gcongr
    _ ≤ 1 / x ^ 2 := by
      apply one_div_le_one_div_of_le (sq_pos_of_ne_zero hx)
      have hpiSq : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_pos]
      calc
        x ^ 2 = 1 * x ^ 2 := by ring
        _ ≤ Real.pi ^ 2 * x ^ 2 :=
          mul_le_mul_of_nonneg_right hpiSq (sq_nonneg x)
        _ = (Real.pi * x) ^ 2 := by ring
    _ = (x ^ 2)⁻¹ := by rw [one_div]

private theorem prawitzJC_isBigO_invSq :
    prawitzJC =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [(isCompact_Icc (a := (-1 : ℝ)) (b := 1)).compl_mem_cocompact] with x hx
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    exact hx (by norm_num)
  have hJ := prawitzJ_le_inv_sq hx0
  have hrpow : |x| ^ (2 : ℝ) = |x| ^ (2 : ℕ) :=
    Real.rpow_natCast |x| 2
  rw [prawitzJC, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (prawitzJ_nonneg x), one_mul]
  rw [Real.rpow_neg (abs_nonneg x)]
  calc
    prawitzJ x ≤ (x ^ 2)⁻¹ := hJ
    _ = (|x| ^ 2)⁻¹ := by rw [sq_abs]
    _ ≤ ‖(|x| ^ (2 : ℝ))⁻¹‖ := by
      rw [hrpow]
      exact Real.le_norm_self _

private theorem summable_fourier_prawitzJC_int :
    Summable (fun n : ℤ => FourierTransform.fourier prawitzJC (n : ℝ)) := by
  apply summable_of_hasFiniteSupport
  refine (Set.finite_singleton 0).subset ?_
  intro n hn
  simp only [Function.mem_support, Set.mem_singleton_iff] at hn ⊢
  by_contra hn0
  have habs : (1 : ℝ) ≤ |(n : ℝ)| := by
    exact_mod_cast Int.one_le_abs hn0
  have htent : StatLean.HypothesisTesting.tent (n : ℝ) = 0 :=
    StatLean.HypothesisTesting.tent_of_one_le_abs habs
  apply hn
  rw [fourier_prawitzJC]
  simp [htent]

/-- Poisson summation for the Fejer kernel.  This is the partial-fraction
identity needed to identify the two definitions of Vaaler's approximant. -/
theorem tsum_prawitzJ_add_int (x : ℝ) :
    ∑' n : ℤ, prawitzJ (x + n) = 1 := by
  have hpoisson := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    continuous_prawitzJC one_lt_two prawitzJC_isBigO_invSq
    summable_fourier_prawitzJC_int x
  rw [fourier_prawitzJC] at hpoisson
  have hcomplex : (∑' n : ℤ, prawitzJC (x + n)) = (1 : ℂ) := by
    calc
      (∑' n : ℤ, prawitzJC (x + n)) =
          ∑' n : ℤ, ((StatLean.HypothesisTesting.tent (n : ℝ) : ℝ) : ℂ) *
            fourier n (x : UnitAddCircle) := hpoisson
      _ = ((StatLean.HypothesisTesting.tent (0 : ℝ) : ℝ) : ℂ) *
          fourier 0 (x : UnitAddCircle) := by
        have hzero : ∀ n : ℤ, n ≠ 0 →
            ((StatLean.HypothesisTesting.tent (n : ℝ) : ℝ) : ℂ) *
              fourier n (x : UnitAddCircle) = 0 := by
          intro n hn
          have habs : (1 : ℝ) ≤ |(n : ℝ)| := by
            exact_mod_cast Int.one_le_abs hn
          have htent : StatLean.HypothesisTesting.tent (n : ℝ) = 0 :=
            StatLean.HypothesisTesting.tent_of_one_le_abs habs
          simp [htent]
        simpa only [Int.cast_zero] using
          (tsum_eq_single (L := SummationFilter.unconditional ℤ) 0 hzero)
      _ = 1 := by
        simp [StatLean.HypothesisTesting.tent_zero]
  apply Complex.ofReal_inj.mp
  calc
    (((∑' n : ℤ, prawitzJ (x + n)) : ℝ) : ℂ) =
        ∑' n : ℤ, ((prawitzJ (x + n) : ℝ) : ℂ) :=
      Complex.ofReal_tsum _
    _ = ∑' n : ℤ, prawitzJC (x + n) := by rfl
    _ = (1 : ℂ) := hcomplex

/-- The integer-shift partition of unity in the orientation used by the
bilateral Prawitz series. -/
theorem tsum_prawitzJ_sub_int (x : ℝ) :
    ∑' m : ℤ, prawitzJ (x - m) = 1 := by
  calc
    (∑' m : ℤ, prawitzJ (x - m)) =
        ∑' n : ℤ, prawitzJ (x + n) := by
      simpa only [Equiv.neg_apply, Int.cast_neg, sub_eq_add_neg, neg_neg] using
        (Equiv.neg ℤ).tsum_eq (fun n : ℤ => prawitzJ (x + n))
    _ = 1 := tsum_prawitzJ_add_int x

theorem summable_prawitzJ_sub_int (x : ℝ) :
    Summable (fun m : ℤ => prawitzJ (x - m)) := by
  by_contra h
  have hz := tsum_eq_zero_of_not_summable h
  rw [tsum_prawitzJ_sub_int] at hz
  norm_num at hz

theorem prawitzS_add_int (x : ℝ) (m : ℤ) :
    prawitzS (x + m) = prawitzS x := by
  unfold prawitzS
  have harg : Real.pi * (x + (m : ℝ)) =
      Real.pi * x + (m : ℝ) * Real.pi := by ring
  rw [harg, Real.sin_add_int_mul_pi]
  have hsignSq : (((-1 : ℝ) ^ m) ^ 2) = 1 := by
    rw [← sq_abs, abs_neg_one_zpow]
    norm_num
  rw [mul_div_assoc, mul_pow, hsignSq, one_mul]

/-- Positive integer translates of `J`; these are the positive-index terms
in the signed bilateral series. -/
def prawitzLeftShiftSeries (x : ℝ) : ℝ :=
  ∑' m : ℕ, prawitzJ (x - ((m : ℝ) + 1))

/-- Negative integer translates of `J`; these are the negative-index terms
in the signed bilateral series. -/
def prawitzRightShiftSeries (x : ℝ) : ℝ :=
  ∑' m : ℕ, prawitzJ (x + ((m : ℝ) + 1))

theorem summable_prawitzLeftShiftSeries (x : ℝ) :
    Summable (fun m : ℕ => prawitzJ (x - ((m : ℝ) + 1))) := by
  have h := summable_prawitzJ_sub_int x
  have hinj : Function.Injective (fun m : ℕ => (m : ℤ) + 1) := by
    intro a b hab
    apply Int.ofNat_injective
    exact add_right_cancel hab
  refine (h.comp_injective hinj).congr ?_
  intro m
  simp only [Function.comp_apply, Int.cast_add, Int.cast_natCast, Int.cast_one]

theorem summable_prawitzRightShiftSeries (x : ℝ) :
    Summable (fun m : ℕ => prawitzJ (x + ((m : ℝ) + 1))) := by
  have h := summable_prawitzJ_sub_int x
  have hinj : Function.Injective (fun m : ℕ => -((m : ℤ) + 1)) := by
    intro a b hab
    apply Int.ofNat_injective
    exact add_right_cancel (neg_injective hab)
  refine (h.comp_injective hinj).congr ?_
  intro m
  simp only [Function.comp_apply, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
  ring

/-- Ordinary real-space form of the signed-shift part of Vaaler's
approximant. -/
def prawitzShiftH (x : ℝ) : ℝ :=
  prawitzLeftShiftSeries x - prawitzRightShiftSeries x +
    2 * prawitzS x / x

theorem prawitzRightShiftSeries_eq_tail {x : ℝ} (hx : 0 < x) :
    prawitzRightShiftSeries x = prawitzS x * prawitzTailSeries x := by
  unfold prawitzRightShiftSeries prawitzTailSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  have hxm : x + ((m : ℝ) + 1) ≠ 0 := by positivity
  have hS : prawitzS (x + ((m : ℝ) + 1)) = prawitzS x := by
    convert prawitzS_add_int x ((m : ℤ) + 1) using 1 <;> norm_num
  rw [prawitzJ, if_neg hxm, hS]
  ring

theorem prawitz_shift_partition (x : ℝ) :
    prawitzLeftShiftSeries x + prawitzJ x + prawitzRightShiftSeries x = 1 := by
  let f : ℤ → ℝ := fun m => prawitzJ (x - m)
  have hpos : Summable (fun n : ℕ => f ((n : ℤ) + 1)) := by
    simpa only [f, Int.cast_add, Int.cast_natCast, Int.cast_one] using
      summable_prawitzLeftShiftSeries x
  have hneg : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := by
    simpa only [f, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      sub_neg_eq_add] using summable_prawitzRightShiftSeries x
  have hsplit := tsum_of_add_one_of_neg_add_one hpos hneg
  have htotal : ∑' m : ℤ, f m = 1 := by
    simpa only [f] using tsum_prawitzJ_sub_int x
  rw [htotal] at hsplit
  simpa only [f, prawitzLeftShiftSeries, prawitzRightShiftSeries, Int.cast_add,
    Int.cast_natCast, Int.cast_one, Int.cast_zero, sub_zero, Int.cast_neg,
    sub_neg_eq_add] using hsplit.symm

theorem prawitzShiftH_of_pos {x : ℝ} (hx : 0 < x) :
    prawitzShiftH x = prawitzPositiveH x := by
  have hpartition := prawitz_shift_partition x
  have hright := prawitzRightShiftSeries_eq_tail hx
  have hx0 : x ≠ 0 := hx.ne'
  have hJ : prawitzJ x = prawitzS x / x ^ 2 := by
    rw [prawitzJ, if_neg hx0]
  rw [hright, hJ] at hpartition
  rw [prawitzShiftH, prawitzPositiveH, hright]
  linear_combination hpartition

theorem prawitzLeftShiftSeries_neg (x : ℝ) :
    prawitzLeftShiftSeries (-x) = prawitzRightShiftSeries x := by
  unfold prawitzLeftShiftSeries prawitzRightShiftSeries
  apply tsum_congr
  intro m
  rw [show -x - ((m : ℝ) + 1) = -(x + ((m : ℝ) + 1)) by ring,
    prawitzJ_neg]

theorem prawitzRightShiftSeries_neg (x : ℝ) :
    prawitzRightShiftSeries (-x) = prawitzLeftShiftSeries x := by
  unfold prawitzLeftShiftSeries prawitzRightShiftSeries
  apply tsum_congr
  intro m
  rw [show -x + ((m : ℝ) + 1) = -(x - ((m : ℝ) + 1)) by ring,
    prawitzJ_neg]

theorem prawitzShiftH_neg (x : ℝ) :
    prawitzShiftH (-x) = -prawitzShiftH x := by
  rw [prawitzShiftH, prawitzShiftH, prawitzLeftShiftSeries_neg,
    prawitzRightShiftSeries_neg, prawitzS_neg]
  ring

theorem prawitzShiftH_zero : prawitzShiftH 0 = 0 := by
  have h := prawitzShiftH_neg 0
  simp only [neg_zero] at h
  linarith

/-- Identification of the real-space Vaaler approximant with its signed
integer-shift representation.  This is the bridge needed before Abel
regularization can be performed on the Fourier side. -/
theorem prawitzShiftH_eq_prawitzH (x : ℝ) :
    prawitzShiftH x = prawitzH x := by
  obtain hx | rfl | hx := lt_trichotomy x 0
  · have hpos : 0 < -x := neg_pos.mpr hx
    calc
      prawitzShiftH x = -prawitzShiftH (-x) := by
        rw [prawitzShiftH_neg]
        simp
      _ = -prawitzPositiveH (-x) := by rw [prawitzShiftH_of_pos hpos]
      _ = prawitzH x := (prawitzH_of_neg hx).symm
  · rw [prawitzShiftH_zero, prawitzH_zero]
  · rw [prawitzShiftH_of_pos hx, prawitzH_of_pos hx]

/-- The unit complex phase occurring in the Fourier transform of integer
translates of `J`. -/
def prawitzPhaseUnit (t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))

@[simp]
theorem norm_prawitzPhaseUnit (t : ℝ) : ‖prawitzPhaseUnit t‖ = 1 := by
  rw [prawitzPhaseUnit,
    show 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
      (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) by
        push_cast
        ring,
    Complex.norm_exp_ofReal_mul_I]

theorem prawitzPhaseUnit_neg (t : ℝ) :
    prawitzPhaseUnit (-t) = (prawitzPhaseUnit t)⁻¹ := by
  rw [prawitzPhaseUnit, prawitzPhaseUnit,
    show 2 * (Real.pi : ℂ) * Complex.I * ((-t : ℝ) : ℂ) =
      -(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) by
        push_cast
        ring,
    Complex.exp_neg]

theorem prawitzPhaseUnit_nat_mul (m : ℕ) (t : ℝ) :
    prawitzPhaseUnit ((m : ℝ) * t) = prawitzPhaseUnit t ^ m := by
  rw [prawitzPhaseUnit, prawitzPhaseUnit,
    show 2 * (Real.pi : ℂ) * Complex.I * (((m : ℝ) * t : ℝ) : ℂ) =
      (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) by
        push_cast
        ring,
    Complex.exp_nat_mul]

/-- Fourier translation formula for the Fejer kernel, stated in the phase
normalization used by the Abel series below. -/
theorem fourier_prawitzJC_add (a t : ℝ) :
    FourierTransform.fourier (fun x : ℝ => prawitzJC (x + a)) t =
      prawitzPhaseUnit (a * t) *
        ((StatLean.HypothesisTesting.tent t : ℝ) : ℂ) := by
  have h := congrFun
    (Fourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℝ) prawitzJC a) t
  have hphase : ((Real.fourierChar (a * t) : Circle) : ℂ) =
      prawitzPhaseUnit (a * t) := by
    rw [Real.fourierChar_apply, prawitzPhaseUnit]
    congr 1
    push_cast
    ring
  have hfourier (f : ℝ → ℂ) :
      Fourier.fourierIntegral Real.fourierChar volume f t =
        FourierTransform.fourier f t := by
    rw [Real.fourier_real_eq]
    rfl
  rw [hfourier, hfourier] at h
  rw [fourier_prawitzJC] at h
  simpa only [Function.comp_apply, Circle.smul_def, hphase] using h

theorem fourier_prawitzJC_sub_nat (m : ℕ) (t : ℝ) :
    FourierTransform.fourier
        (fun x : ℝ => prawitzJC (x - ((m : ℝ) + 1))) t =
      (prawitzPhaseUnit t)⁻¹ ^ (m + 1) *
        ((StatLean.HypothesisTesting.tent t : ℝ) : ℂ) := by
  have h := fourier_prawitzJC_add (-((m : ℝ) + 1)) t
  rw [show -((m : ℝ) + 1) * t =
      -(((m + 1 : ℕ) : ℝ) * t) by
        push_cast
        ring,
    prawitzPhaseUnit_neg, prawitzPhaseUnit_nat_mul, ← inv_pow] at h
  simpa only [sub_eq_add_neg] using h

theorem fourier_prawitzJC_add_nat (m : ℕ) (t : ℝ) :
    FourierTransform.fourier
        (fun x : ℝ => prawitzJC (x + ((m : ℝ) + 1))) t =
      prawitzPhaseUnit t ^ (m + 1) *
        ((StatLean.HypothesisTesting.tent t : ℝ) : ℂ) := by
  have h := fourier_prawitzJC_add ((m : ℝ) + 1) t
  rw [show ((m : ℝ) + 1) * t =
      (((m + 1 : ℕ) : ℝ) * t) by norm_num,
    prawitzPhaseUnit_nat_mul] at h
  exact h

private theorem prawitzPhaseUnit_ne_one {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    prawitzPhaseUnit t ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have him := congrArg Complex.im hn
  norm_num [Complex.mul_re, Complex.mul_im] at him
  have hnt : (n : ℝ) = t := by
    nlinarith [Real.pi_pos]
  have hnpos : (0 : ℤ) < n := by exact_mod_cast (hnt.symm ▸ ht0)
  have hnlt : n < (1 : ℤ) := by exact_mod_cast (hnt.symm ▸ ht1)
  omega

/-- Abel-regularized signed geometric phase.  At `r<1` it is the sum of
the absolutely convergent positive and negative shift series. -/
def prawitzAbelPhase (r t : ℝ) : ℂ :=
  let z := prawitzPhaseUnit t
  ((r : ℂ) * z⁻¹) / (1 - (r : ℂ) * z⁻¹) -
    ((r : ℂ) * z) / (1 - (r : ℂ) * z)

/-- For `0 ≤ r < 1`, the Abel phase is the absolutely convergent signed
geometric series attached to the positive and negative integer shifts. -/
theorem prawitzAbelPhase_eq_tsum {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    prawitzAbelPhase r t =
      ∑' m : ℕ,
        (((r : ℂ) * (prawitzPhaseUnit t)⁻¹) ^ (m + 1) -
          ((r : ℂ) * prawitzPhaseUnit t) ^ (m + 1)) := by
  have hminus : ‖(r : ℂ) * (prawitzPhaseUnit t)⁻¹‖ < 1 := by
    simpa only [norm_mul, norm_inv, norm_prawitzPhaseUnit, inv_one, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hplus : ‖(r : ℂ) * prawitzPhaseUnit t‖ < 1 := by
    simpa only [norm_mul, norm_prawitzPhaseUnit, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hminusShift :
      Summable (fun m : ℕ =>
        ((r : ℂ) * (prawitzPhaseUnit t)⁻¹) ^ (m + 1)) := by
    simpa only [pow_succ'] using
      (summable_geometric_of_norm_lt_one hminus).mul_left
        ((r : ℂ) * (prawitzPhaseUnit t)⁻¹)
  have hplusShift :
      Summable (fun m : ℕ =>
        ((r : ℂ) * prawitzPhaseUnit t) ^ (m + 1)) := by
    simpa only [pow_succ'] using
      (summable_geometric_of_norm_lt_one hplus).mul_left
        ((r : ℂ) * prawitzPhaseUnit t)
  calc
    prawitzAbelPhase r t =
        ((r : ℂ) * (prawitzPhaseUnit t)⁻¹) /
            (1 - (r : ℂ) * (prawitzPhaseUnit t)⁻¹) -
          ((r : ℂ) * prawitzPhaseUnit t) /
            (1 - (r : ℂ) * prawitzPhaseUnit t) := by rfl
    _ = (∑' m : ℕ,
          ((r : ℂ) * (prawitzPhaseUnit t)⁻¹) ^ (m + 1)) -
        ∑' m : ℕ, ((r : ℂ) * prawitzPhaseUnit t) ^ (m + 1) := by
      rw [div_eq_mul_inv, div_eq_mul_inv,
        ← tsum_geometric_of_norm_lt_one hminus,
        ← tsum_geometric_of_norm_lt_one hplus,
        geom_series_mul_shift _ hminus, geom_series_mul_shift _ hplus]
    _ = ∑' m : ℕ,
        (((r : ℂ) * (prawitzPhaseUnit t)⁻¹) ^ (m + 1) -
          ((r : ℂ) * prawitzPhaseUnit t) ^ (m + 1)) :=
      (hminusShift.tsum_sub hplusShift).symm

/-- The geometric Abel phase, multiplied by the tent transform of `J`, is
exactly the weighted sum of the Fourier transforms of the signed integer
translates.  This is the frequency-side form in which the Abel parameter is
used below. -/
theorem prawitzAbelPhase_mul_tent_eq_tsum_fourier_shifts
    {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    prawitzAbelPhase r t *
        ((StatLean.HypothesisTesting.tent t : ℝ) : ℂ) =
      ∑' m : ℕ, ((r : ℂ) ^ (m + 1)) *
        (FourierTransform.fourier
            (fun x : ℝ => prawitzJC (x - ((m : ℝ) + 1))) t -
          FourierTransform.fourier
            (fun x : ℝ => prawitzJC (x + ((m : ℝ) + 1))) t) := by
  rw [prawitzAbelPhase_eq_tsum hr0 hr1, ← tsum_mul_right]
  apply tsum_congr
  intro m
  rw [fourier_prawitzJC_sub_nat, fourier_prawitzJC_add_nat,
    mul_pow, mul_pow]
  ring

theorem prawitzAbelPhase_one {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    prawitzAbelPhase 1 t =
      -Complex.I * Complex.cot ((Real.pi : ℂ) * (t : ℂ)) := by
  let z := prawitzPhaseUnit t
  have hz : z ≠ 0 := by
    exact Complex.exp_ne_zero _
  have hz1 : z ≠ 1 := prawitzPhaseUnit_ne_one ht0 ht1
  have hzinv1 : 1 - z⁻¹ ≠ 0 := by
    exact sub_ne_zero.mpr (inv_ne_one.mpr hz1).symm
  have honez : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have hnegonez : (-1 : ℂ) + z ≠ 0 := by
    simpa only [sub_eq_add_neg, add_comm] using (sub_ne_zero.mpr hz1)
  have hcot := Complex.cot_pi_eq_exp_ratio (t : ℂ)
  change Complex.cot ((Real.pi : ℂ) * (t : ℂ)) =
    (z + 1) / (Complex.I * (1 - z)) at hcot
  rw [prawitzAbelPhase, show prawitzPhaseUnit t = z by rfl, hcot]
  norm_num only [Complex.ofReal_one, one_mul]
  field_simp [hz, hz1, hzinv1, honez, hnegonez, Complex.I_ne_zero]
  have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hratio : (1 - z) / (z - 1) = (-1 : ℂ) := by
    exact (div_eq_iff hzsub).2 (by ring)
  rw [hratio]
  ring

theorem tendsto_prawitzAbelPhase_one {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Tendsto (fun r : ℝ => prawitzAbelPhase r t) (nhds 1)
      (nhds (-Complex.I * Complex.cot ((Real.pi : ℂ) * (t : ℂ)))) := by
  have hz1 : prawitzPhaseUnit t ≠ 1 := prawitzPhaseUnit_ne_one ht0 ht1
  have hdenomInv : 1 - ((1 : ℂ) * (prawitzPhaseUnit t)⁻¹) ≠ 0 := by
    have hzinv : (prawitzPhaseUnit t)⁻¹ ≠ 1 := inv_ne_one.mpr hz1
    simpa only [one_mul] using (sub_ne_zero.mpr hzinv.symm)
  have hdenom : 1 - ((1 : ℂ) * prawitzPhaseUnit t) ≠ 0 := by
    simpa only [one_mul] using (sub_ne_zero.mpr hz1.symm)
  have hcont : ContinuousAt (fun r : ℝ => prawitzAbelPhase r t) 1 := by
    dsimp only [prawitzAbelPhase]
    let cr : ℝ → ℂ := fun r => (r : ℂ)
    have hcr : ContinuousAt cr 1 := Complex.continuous_ofReal.continuousAt
    have hnumInv : ContinuousAt (fun r : ℝ => cr r * (prawitzPhaseUnit t)⁻¹) 1 :=
      hcr.mul continuousAt_const
    have hnum : ContinuousAt (fun r : ℝ => cr r * prawitzPhaseUnit t) 1 :=
      hcr.mul continuousAt_const
    exact (hnumInv.div (continuousAt_const.sub hnumInv) hdenomInv).sub
      (hnum.div (continuousAt_const.sub hnum) hdenom)
  rw [← prawitzAbelPhase_one ht0 ht1]
  exact hcont.tendsto

/-- On the open positive frequency band, the Abel-regularized shift
transform converges to the cotangent term in Prawitz's formula. -/
theorem tendsto_prawitzAbelPhase_mul_tent {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    Tendsto
      (fun r : ℝ => prawitzAbelPhase r t *
        ((StatLean.HypothesisTesting.tent t : ℝ) : ℂ))
      (nhds 1)
      (nhds (-Complex.I * (((1 - t : ℝ) : ℂ)) *
        Complex.cot ((Real.pi : ℂ) * (t : ℂ)))) := by
  have htent : StatLean.HypothesisTesting.tent t = 1 - t :=
    StatLean.HypothesisTesting.tent_of_mem_Icc_zero_one ⟨ht0.le, ht1.le⟩
  convert (tendsto_prawitzAbelPhase_one ht0 ht1).mul_const
    (((StatLean.HypothesisTesting.tent t : ℝ) : ℂ)) using 1
  rw [htent]
  push_cast
  ring

theorem prawitzAbelPhase_neg (r t : ℝ) :
    prawitzAbelPhase r (-t) = -prawitzAbelPhase r t := by
  rw [prawitzAbelPhase, prawitzAbelPhase, prawitzPhaseUnit_neg]
  rw [inv_inv]
  ring

theorem continuous_prawitzAbelPhase {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (prawitzAbelPhase r) := by
  have hz : Continuous prawitzPhaseUnit := by
    unfold prawitzPhaseUnit
    fun_prop
  have hzinv : Continuous (fun t : ℝ => (prawitzPhaseUnit t)⁻¹) :=
    hz.inv₀ (fun t => Complex.exp_ne_zero _)
  have hminus : Continuous
      (fun t : ℝ => (r : ℂ) * (prawitzPhaseUnit t)⁻¹) :=
    continuous_const.mul hzinv
  have hplus : Continuous
      (fun t : ℝ => (r : ℂ) * prawitzPhaseUnit t) :=
    continuous_const.mul hz
  have hminusDenom : ∀ t : ℝ,
      1 - (r : ℂ) * (prawitzPhaseUnit t)⁻¹ ≠ 0 := by
    intro t hzero
    have heq : (r : ℂ) * (prawitzPhaseUnit t)⁻¹ = 1 :=
      (sub_eq_zero.mp hzero).symm
    have hn := congrArg norm heq
    simp only [norm_mul, norm_inv, norm_prawitzPhaseUnit, inv_one, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, norm_one] at hn
    linarith
  have hplusDenom : ∀ t : ℝ,
      1 - (r : ℂ) * prawitzPhaseUnit t ≠ 0 := by
    intro t hzero
    have heq : (r : ℂ) * prawitzPhaseUnit t = 1 :=
      (sub_eq_zero.mp hzero).symm
    have hn := congrArg norm heq
    simp only [norm_mul, norm_prawitzPhaseUnit, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0, norm_one] at hn
    linarith
  unfold prawitzAbelPhase
  exact (hminus.div (continuous_const.sub hminus) hminusDenom).sub
    (hplus.div (continuous_const.sub hplus) hplusDenom)

/-- The inverse-frequency form of the Abel-regularized signed shift series.
The reflection `-t` is required because Mathlib's Fourier transform squared
reflects the real-space function. -/
def prawitzAbelShiftPreimage (r t : ℝ) : ℂ :=
  ((StatLean.HypothesisTesting.tent t : ℝ) : ℂ) *
    prawitzAbelPhase r (-t)

theorem continuous_prawitzAbelShiftPreimage {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (prawitzAbelShiftPreimage r) := by
  unfold prawitzAbelShiftPreimage
  exact (Complex.continuous_ofReal.comp
    StatLean.HypothesisTesting.continuous_tent).mul
      ((continuous_prawitzAbelPhase hr0 hr1).comp continuous_neg)

theorem hasCompactSupport_prawitzAbelShiftPreimage (r : ℝ) :
    HasCompactSupport (prawitzAbelShiftPreimage r) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro t ht
  rw [prawitzAbelShiftPreimage,
    StatLean.HypothesisTesting.tent_eq_zero_of_notMem ht]
  simp

theorem integrable_prawitzAbelShiftPreimage {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Integrable (prawitzAbelShiftPreimage r) :=
  (continuous_prawitzAbelShiftPreimage hr0 hr1).integrable_of_hasCompactSupport
    (hasCompactSupport_prawitzAbelShiftPreimage r)

/-! ## Fourier inversion of the Abel-regularized shift component -/

/-- The physical-space Abel sum of the signed integer translates of `J`.
This is the regularized shift component of `prawitzShiftH`; the removable
correction `2 S(x) / x` is added separately below. -/
def prawitzAbelShiftSeries (r x : ℝ) : ℂ :=
  ∑' m : ℕ, ((r : ℂ) ^ (m + 1)) *
    (prawitzJC (x - ((m : ℝ) + 1)) -
      prawitzJC (x + ((m : ℝ) + 1)))

private def prawitzAbelRightFrequencyTerm (r : ℝ) (m : ℕ) (t : ℝ) : ℂ :=
  ((r : ℂ) ^ (m + 1)) *
    FourierTransform.fourier
      (fun x : ℝ => prawitzJC (x + ((m : ℝ) + 1))) t

private def prawitzAbelLeftFrequencyTerm (r : ℝ) (m : ℕ) (t : ℝ) : ℂ :=
  ((r : ℂ) ^ (m + 1)) *
    FourierTransform.fourier
      (fun x : ℝ => prawitzJC (x - ((m : ℝ) + 1))) t

private def prawitzAbelFrequencyTerm (r : ℝ) (m : ℕ) (t : ℝ) : ℂ :=
  prawitzAbelRightFrequencyTerm r m t -
    prawitzAbelLeftFrequencyTerm r m t

private theorem integrable_fourier_prawitzJC_add_nat (m : ℕ) :
    Integrable (FourierTransform.fourier
      (fun x : ℝ => prawitzJC (x + ((m : ℝ) + 1)))) := by
  rw [funext (fourier_prawitzJC_add_nat m)]
  have hcont : Continuous (fun t : ℝ =>
      prawitzPhaseUnit t ^ (m + 1) *
        ((StatLean.HypothesisTesting.tent t : ℝ) : ℂ)) := by
    have hz : Continuous prawitzPhaseUnit := by
      unfold prawitzPhaseUnit
      fun_prop
    exact (hz.pow _).mul (Complex.continuous_ofReal.comp
      StatLean.HypothesisTesting.continuous_tent)
  have hcompact : HasCompactSupport (fun t : ℝ =>
      prawitzPhaseUnit t ^ (m + 1) *
        ((StatLean.HypothesisTesting.tent t : ℝ) : ℂ)) := by
    apply HasCompactSupport.intro
      (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    intro t ht
    rw [StatLean.HypothesisTesting.tent_eq_zero_of_notMem ht]
    simp
  exact hcont.integrable_of_hasCompactSupport hcompact

private theorem integrable_fourier_prawitzJC_sub_nat (m : ℕ) :
    Integrable (FourierTransform.fourier
      (fun x : ℝ => prawitzJC (x - ((m : ℝ) + 1)))) := by
  rw [funext (fourier_prawitzJC_sub_nat m)]
  have hcont : Continuous (fun t : ℝ =>
      (prawitzPhaseUnit t)⁻¹ ^ (m + 1) *
        ((StatLean.HypothesisTesting.tent t : ℝ) : ℂ)) := by
    have hz : Continuous prawitzPhaseUnit := by
      unfold prawitzPhaseUnit
      fun_prop
    exact ((hz.inv₀ (fun t => Complex.exp_ne_zero _)).pow _).mul
      (Complex.continuous_ofReal.comp
        StatLean.HypothesisTesting.continuous_tent)
  have hcompact : HasCompactSupport (fun t : ℝ =>
      (prawitzPhaseUnit t)⁻¹ ^ (m + 1) *
        ((StatLean.HypothesisTesting.tent t : ℝ) : ℂ)) := by
    apply HasCompactSupport.intro
      (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    intro t ht
    rw [StatLean.HypothesisTesting.tent_eq_zero_of_notMem ht]
    simp
  exact hcont.integrable_of_hasCompactSupport hcompact

private theorem integrable_prawitzAbelRightFrequencyTerm
    (r : ℝ) (m : ℕ) :
    Integrable (prawitzAbelRightFrequencyTerm r m) :=
  (integrable_fourier_prawitzJC_add_nat m).const_mul _

private theorem integrable_prawitzAbelLeftFrequencyTerm
    (r : ℝ) (m : ℕ) :
    Integrable (prawitzAbelLeftFrequencyTerm r m) :=
  (integrable_fourier_prawitzJC_sub_nat m).const_mul _

private theorem integrable_prawitzAbelFrequencyTerm
    (r : ℝ) (m : ℕ) :
    Integrable (prawitzAbelFrequencyTerm r m) :=
  (integrable_prawitzAbelRightFrequencyTerm r m).sub
    (integrable_prawitzAbelLeftFrequencyTerm r m)

private theorem integral_norm_prawitzAbelRightFrequencyTerm
    {r : ℝ} (hr0 : 0 ≤ r) (m : ℕ) :
    (∫ t : ℝ, ‖prawitzAbelRightFrequencyTerm r m t‖) =
      r ^ (m + 1) *
        ∫ t : ℝ, StatLean.HypothesisTesting.tent t := by
  simp_rw [prawitzAbelRightFrequencyTerm, fourier_prawitzJC_add_nat,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0, norm_prawitzPhaseUnit, one_pow, one_mul,
    abs_of_nonneg (StatLean.HypothesisTesting.tent_nonneg _)]
  exact MeasureTheory.integral_const_mul _ _

private theorem integral_norm_prawitzAbelLeftFrequencyTerm
    {r : ℝ} (hr0 : 0 ≤ r) (m : ℕ) :
    (∫ t : ℝ, ‖prawitzAbelLeftFrequencyTerm r m t‖) =
      r ^ (m + 1) *
        ∫ t : ℝ, StatLean.HypothesisTesting.tent t := by
  simp_rw [prawitzAbelLeftFrequencyTerm, fourier_prawitzJC_sub_nat,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0, norm_inv, norm_prawitzPhaseUnit, inv_one,
    one_pow, one_mul,
    abs_of_nonneg (StatLean.HypothesisTesting.tent_nonneg _)]
  exact MeasureTheory.integral_const_mul _ _

private theorem summable_integral_norm_prawitzAbelRightFrequencyTerm
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun m : ℕ =>
      ∫ t : ℝ, ‖prawitzAbelRightFrequencyTerm r m t‖) := by
  have hgeom : Summable (fun m : ℕ => r ^ (m + 1)) := by
    simpa only [pow_succ'] using
      (summable_geometric_of_lt_one hr0 hr1).mul_left r
  simpa only [integral_norm_prawitzAbelRightFrequencyTerm hr0] using
    hgeom.mul_right (∫ t : ℝ, StatLean.HypothesisTesting.tent t)

private theorem summable_integral_norm_prawitzAbelLeftFrequencyTerm
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun m : ℕ =>
      ∫ t : ℝ, ‖prawitzAbelLeftFrequencyTerm r m t‖) := by
  have hgeom : Summable (fun m : ℕ => r ^ (m + 1)) := by
    simpa only [pow_succ'] using
      (summable_geometric_of_lt_one hr0 hr1).mul_left r
  simpa only [integral_norm_prawitzAbelLeftFrequencyTerm hr0] using
    hgeom.mul_right (∫ t : ℝ, StatLean.HypothesisTesting.tent t)

private theorem summable_integral_norm_prawitzAbelFrequencyTerm
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun m : ℕ =>
      ∫ t : ℝ, ‖prawitzAbelFrequencyTerm r m t‖) := by
  apply Summable.of_nonneg_of_le
    (fun m => integral_nonneg (fun t => norm_nonneg _))
  · intro m
    calc
      (∫ t : ℝ, ‖prawitzAbelFrequencyTerm r m t‖) ≤
          ∫ t : ℝ,
            ‖prawitzAbelRightFrequencyTerm r m t‖ +
              ‖prawitzAbelLeftFrequencyTerm r m t‖ := by
        apply MeasureTheory.integral_mono
          (integrable_prawitzAbelFrequencyTerm r m).norm
          ((integrable_prawitzAbelRightFrequencyTerm r m).norm.add
            (integrable_prawitzAbelLeftFrequencyTerm r m).norm)
        intro t
        exact norm_sub_le _ _
      _ = (∫ t : ℝ, ‖prawitzAbelRightFrequencyTerm r m t‖) +
          ∫ t : ℝ, ‖prawitzAbelLeftFrequencyTerm r m t‖ := by
        exact integral_add
          (integrable_prawitzAbelRightFrequencyTerm r m).norm
          (integrable_prawitzAbelLeftFrequencyTerm r m).norm
  · exact (summable_integral_norm_prawitzAbelRightFrequencyTerm hr0 hr1).add
      (summable_integral_norm_prawitzAbelLeftFrequencyTerm hr0 hr1)

private theorem prawitzAbelShiftPreimage_eq_tsum
    {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    prawitzAbelShiftPreimage r t =
      ∑' m : ℕ, prawitzAbelFrequencyTerm r m t := by
  rw [prawitzAbelShiftPreimage, prawitzAbelPhase_eq_tsum hr0 hr1,
    ← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [prawitzAbelFrequencyTerm, prawitzAbelRightFrequencyTerm,
    prawitzAbelLeftFrequencyTerm, fourier_prawitzJC_add_nat,
    fourier_prawitzJC_sub_nat, prawitzPhaseUnit_neg, inv_inv,
    mul_pow, mul_pow]
  ring

private theorem fourier_fourier_prawitzJC_add_nat
    (m : ℕ) (x : ℝ) :
    FourierTransform.fourier
        (FourierTransform.fourier
          (fun y : ℝ => prawitzJC (y + ((m : ℝ) + 1)))) x =
      prawitzJC (x - ((m : ℝ) + 1)) := by
  let a : ℝ := (m : ℝ) + 1
  let f : ℝ → ℂ := fun y => prawitzJC (y + a)
  have hfcont : Continuous f := by
    dsimp only [f]
    exact continuous_prawitzJC.comp (continuous_id.add continuous_const)
  have hfint : Integrable f := by
    dsimp only [f]
    exact integrable_prawitzJC.comp_add_right a
  have hFint : Integrable (FourierTransform.fourier f) := by
    dsimp only [f, a]
    exact integrable_fourier_prawitzJC_add_nat m
  have hinv := hfcont.fourierInv_fourier_eq hfint hFint
  change FourierTransform.fourier (FourierTransform.fourier f) x = _
  calc
    FourierTransform.fourier (FourierTransform.fourier f) x =
        FourierTransform.fourierInv (FourierTransform.fourier f) (-x) := by
      rw [Real.fourierInv_eq_fourier_neg]
      simp
    _ = f (-x) := congrFun hinv (-x)
    _ = prawitzJC (x - ((m : ℝ) + 1)) := by
      change prawitzJC (-x + a) = _
      rw [show -x + a = -(x - ((m : ℝ) + 1)) by
        dsimp only [a]
        ring,
        prawitzJC_neg]

private theorem fourier_fourier_prawitzJC_sub_nat
    (m : ℕ) (x : ℝ) :
    FourierTransform.fourier
        (FourierTransform.fourier
          (fun y : ℝ => prawitzJC (y - ((m : ℝ) + 1)))) x =
      prawitzJC (x + ((m : ℝ) + 1)) := by
  let a : ℝ := (m : ℝ) + 1
  let f : ℝ → ℂ := fun y => prawitzJC (y - a)
  have hfcont : Continuous f := by
    dsimp only [f]
    exact continuous_prawitzJC.comp (continuous_id.sub continuous_const)
  have hfint : Integrable f := by
    dsimp only [f]
    exact integrable_prawitzJC.comp_sub_right a
  have hFint : Integrable (FourierTransform.fourier f) := by
    dsimp only [f, a]
    exact integrable_fourier_prawitzJC_sub_nat m
  have hinv := hfcont.fourierInv_fourier_eq hfint hFint
  change FourierTransform.fourier (FourierTransform.fourier f) x = _
  calc
    FourierTransform.fourier (FourierTransform.fourier f) x =
        FourierTransform.fourierInv (FourierTransform.fourier f) (-x) := by
      rw [Real.fourierInv_eq_fourier_neg]
      simp
    _ = f (-x) := congrFun hinv (-x)
    _ = prawitzJC (x + ((m : ℝ) + 1)) := by
      change prawitzJC (-x - a) = _
      rw [show -x - a = -(x + ((m : ℝ) + 1)) by
        dsimp only [a]
        ring,
        prawitzJC_neg]

private theorem fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    FourierTransform.fourier (fun t : ℝ => c * f t) x =
      c * FourierTransform.fourier f x := by
  rw [Real.fourier_eq, Real.fourier_eq]
  calc
    (∫ t : ℝ, Real.fourierChar (-(inner ℝ t x)) • (c * f t)) =
        ∫ t : ℝ, c * (Real.fourierChar (-(inner ℝ t x)) • f t) := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [Circle.smul_def, smul_eq_mul]
      ring
    _ = c * ∫ t : ℝ, Real.fourierChar (-(inner ℝ t x)) • f t :=
      MeasureTheory.integral_const_mul _ _

private theorem fourier_sub_of_integrable
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    FourierTransform.fourier (fun t : ℝ => f t - g t) x =
      FourierTransform.fourier f x - FourierTransform.fourier g x := by
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
  simp_rw [smul_sub]
  exact integral_sub ((Real.fourierIntegral_convergent_iff x).2 hf)
    ((Real.fourierIntegral_convergent_iff x).2 hg)

private theorem fourier_prawitzAbelFrequencyTerm
    (r : ℝ) (m : ℕ) (x : ℝ) :
    FourierTransform.fourier (prawitzAbelFrequencyTerm r m) x =
      ((r : ℂ) ^ (m + 1)) *
        (prawitzJC (x - ((m : ℝ) + 1)) -
          prawitzJC (x + ((m : ℝ) + 1))) := by
  rw [show prawitzAbelFrequencyTerm r m = fun t : ℝ =>
      prawitzAbelRightFrequencyTerm r m t -
        prawitzAbelLeftFrequencyTerm r m t by rfl,
    fourier_sub_of_integrable
      (integrable_prawitzAbelRightFrequencyTerm r m)
      (integrable_prawitzAbelLeftFrequencyTerm r m)]
  rw [show prawitzAbelRightFrequencyTerm r m = fun t : ℝ =>
      ((r : ℂ) ^ (m + 1)) *
        FourierTransform.fourier
          (fun y : ℝ => prawitzJC (y + ((m : ℝ) + 1))) t by rfl,
    show prawitzAbelLeftFrequencyTerm r m = fun t : ℝ =>
      ((r : ℂ) ^ (m + 1)) *
        FourierTransform.fourier
          (fun y : ℝ => prawitzJC (y - ((m : ℝ) + 1))) t by rfl,
    fourier_const_mul, fourier_const_mul,
    fourier_fourier_prawitzJC_add_nat,
    fourier_fourier_prawitzJC_sub_nat]
  ring

private theorem summable_prawitzAbelRightFrequencyTerm
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    Summable (fun m : ℕ => prawitzAbelRightFrequencyTerm r m t) := by
  have hplus : ‖(r : ℂ) * prawitzPhaseUnit t‖ < 1 := by
    simpa only [norm_mul, norm_prawitzPhaseUnit, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hshift : Summable (fun m : ℕ =>
      ((r : ℂ) * prawitzPhaseUnit t) ^ (m + 1)) := by
    simpa only [pow_succ'] using
      (summable_geometric_of_norm_lt_one hplus).mul_left
        ((r : ℂ) * prawitzPhaseUnit t)
  refine (hshift.mul_right
    (((StatLean.HypothesisTesting.tent t : ℝ) : ℂ))).congr ?_
  intro m
  rw [prawitzAbelRightFrequencyTerm, fourier_prawitzJC_add_nat,
    mul_pow]
  ring

private theorem summable_prawitzAbelLeftFrequencyTerm
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    Summable (fun m : ℕ => prawitzAbelLeftFrequencyTerm r m t) := by
  have hminus : ‖(r : ℂ) * (prawitzPhaseUnit t)⁻¹‖ < 1 := by
    simpa only [norm_mul, norm_inv, norm_prawitzPhaseUnit, inv_one, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hshift : Summable (fun m : ℕ =>
      ((r : ℂ) * (prawitzPhaseUnit t)⁻¹) ^ (m + 1)) := by
    simpa only [pow_succ'] using
      (summable_geometric_of_norm_lt_one hminus).mul_left
        ((r : ℂ) * (prawitzPhaseUnit t)⁻¹)
  refine (hshift.mul_right
    (((StatLean.HypothesisTesting.tent t : ℝ) : ℂ))).congr ?_
  intro m
  rw [prawitzAbelLeftFrequencyTerm, fourier_prawitzJC_sub_nat,
    mul_pow]
  ring

private theorem summable_prawitzAbelFrequencyTerm
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    Summable (fun m : ℕ => prawitzAbelFrequencyTerm r m t) := by
  exact (summable_prawitzAbelRightFrequencyTerm hr0 hr1 t).sub
    (summable_prawitzAbelLeftFrequencyTerm hr0 hr1 t)

/-- For every Abel parameter `0 ≤ r < 1`, the ordinary Fourier transform of
the compactly supported frequency representative is exactly the Abel-weighted
signed shift series.  No distributional or principal-value transform is used. -/
theorem fourier_prawitzAbelShiftPreimage
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    FourierTransform.fourier (prawitzAbelShiftPreimage r) x =
      prawitzAbelShiftSeries r x := by
  let F : ℕ → ℝ → ℂ := fun m t =>
    Real.fourierChar (-(inner ℝ t x)) •
      prawitzAbelFrequencyTerm r m t
  have hFint : ∀ m : ℕ, Integrable (F m) := by
    intro m
    exact (Real.fourierIntegral_convergent_iff x).2
      (integrable_prawitzAbelFrequencyTerm r m)
  have hFnorm : Summable (fun m : ℕ => ∫ t : ℝ, ‖F m t‖) := by
    have heq : (fun m : ℕ => ∫ t : ℝ, ‖F m t‖) =
        (fun m : ℕ => ∫ t : ℝ,
          ‖prawitzAbelFrequencyTerm r m t‖) := by
      funext m
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [F]
      rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
    rw [heq]
    exact summable_integral_norm_prawitzAbelFrequencyTerm hr0 hr1
  have hswap :=
    (MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hFnorm).tsum_eq
  rw [Real.fourier_eq]
  calc
    (∫ t : ℝ, Real.fourierChar (-(inner ℝ t x)) •
        prawitzAbelShiftPreimage r t) =
        ∫ t : ℝ, ∑' m : ℕ, F m t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [prawitzAbelShiftPreimage_eq_tsum hr0 hr1]
      exact ((summable_prawitzAbelFrequencyTerm hr0 hr1 t).hasSum.const_smul
        (Real.fourierChar (-(inner ℝ t x)))).tsum_eq.symm
    _ = ∑' m : ℕ, ∫ t : ℝ, F m t := hswap.symm
    _ = ∑' m : ℕ,
        FourierTransform.fourier (prawitzAbelFrequencyTerm r m) x := by
      apply tsum_congr
      intro m
      rfl
    _ = prawitzAbelShiftSeries r x := by
      unfold prawitzAbelShiftSeries
      apply tsum_congr
      intro m
      exact fourier_prawitzAbelFrequencyTerm r m x

private theorem summable_prawitzShiftDifference (x : ℝ) :
    Summable (fun m : ℕ =>
      prawitzJC (x - ((m : ℝ) + 1)) -
        prawitzJC (x + ((m : ℝ) + 1))) := by
  have hleft : Summable (fun m : ℕ =>
      prawitzJC (x - ((m : ℝ) + 1))) := by
    apply Summable.of_norm
    simpa only [prawitzJC, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (prawitzJ_nonneg _)] using
        summable_prawitzLeftShiftSeries x
  have hright : Summable (fun m : ℕ =>
      prawitzJC (x + ((m : ℝ) + 1))) := by
    apply Summable.of_norm
    simpa only [prawitzJC, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (prawitzJ_nonneg _)] using
        summable_prawitzRightShiftSeries x
  exact hleft.sub hright

private theorem tsum_prawitzShiftDifference (x : ℝ) :
    (∑' m : ℕ,
      (prawitzJC (x - ((m : ℝ) + 1)) -
        prawitzJC (x + ((m : ℝ) + 1)))) =
      (((prawitzLeftShiftSeries x - prawitzRightShiftSeries x : ℝ) : ℂ)) := by
  have hleft : Summable (fun m : ℕ =>
      prawitzJC (x - ((m : ℝ) + 1))) := by
    apply Summable.of_norm
    simpa only [prawitzJC, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (prawitzJ_nonneg _)] using
        summable_prawitzLeftShiftSeries x
  have hright : Summable (fun m : ℕ =>
      prawitzJC (x + ((m : ℝ) + 1))) := by
    apply Summable.of_norm
    simpa only [prawitzJC, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (prawitzJ_nonneg _)] using
        summable_prawitzRightShiftSeries x
  rw [hleft.tsum_sub hright]
  unfold prawitzLeftShiftSeries prawitzRightShiftSeries prawitzJC
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_tsum]
  push_cast
  rfl

theorem prawitzJ_le_one (x : ℝ) : prawitzJ x ≤ 1 := by
  rw [prawitzJ_eq_sinc]
  have h := Real.abs_sinc_le_one (Real.pi * x)
  rcases abs_le.mp h with ⟨hl, hu⟩
  nlinarith

theorem abs_prawitzH_le_two (x : ℝ) : |prawitzH x| ≤ 2 := by
  have hsign : |Real.sign x| ≤ 1 := by
    obtain hx | rfl | hx := lt_trichotomy x 0
    · rw [Real.sign_of_neg hx]
      norm_num
    · simp
    · rw [Real.sign_of_pos hx]
      norm_num
  calc
    |prawitzH x| = |Real.sign x - (Real.sign x - prawitzH x)| := by ring_nf
    _ ≤ |Real.sign x| + |Real.sign x - prawitzH x| := abs_sub _ _
    _ ≤ 1 + prawitzJ x :=
      add_le_add hsign (abs_sign_sub_prawitzH_le_J x)
    _ ≤ 2 := by linarith [prawitzJ_le_one x]

theorem prawitzLeftShiftSeries_nonneg (x : ℝ) :
    0 ≤ prawitzLeftShiftSeries x := by
  unfold prawitzLeftShiftSeries
  exact tsum_nonneg (fun m => prawitzJ_nonneg _)

theorem prawitzRightShiftSeries_nonneg (x : ℝ) :
    0 ≤ prawitzRightShiftSeries x := by
  unfold prawitzRightShiftSeries
  exact tsum_nonneg (fun m => prawitzJ_nonneg _)

theorem prawitzShiftSeries_sum_le_one (x : ℝ) :
    prawitzLeftShiftSeries x + prawitzRightShiftSeries x ≤ 1 := by
  have hpartition := prawitz_shift_partition x
  linarith [prawitzJ_nonneg x]

theorem abs_prawitzShiftSeriesDifference_le_one (x : ℝ) :
    |prawitzLeftShiftSeries x - prawitzRightShiftSeries x| ≤ 1 := by
  calc
    |prawitzLeftShiftSeries x - prawitzRightShiftSeries x| ≤
        |prawitzLeftShiftSeries x| + |prawitzRightShiftSeries x| :=
      abs_sub _ _
    _ = prawitzLeftShiftSeries x + prawitzRightShiftSeries x := by
      rw [abs_of_nonneg (prawitzLeftShiftSeries_nonneg x),
        abs_of_nonneg (prawitzRightShiftSeries_nonneg x)]
    _ ≤ 1 := prawitzShiftSeries_sum_le_one x

theorem abs_prawitzCorrection_le_three (x : ℝ) :
    |2 * prawitzS x / x| ≤ 3 := by
  have hidentity : 2 * prawitzS x / x =
      prawitzH x -
        (prawitzLeftShiftSeries x - prawitzRightShiftSeries x) := by
    have h := prawitzShiftH_eq_prawitzH x
    unfold prawitzShiftH at h
    linarith
  rw [hidentity]
  calc
    |prawitzH x -
        (prawitzLeftShiftSeries x - prawitzRightShiftSeries x)| ≤
        |prawitzH x| +
          |prawitzLeftShiftSeries x - prawitzRightShiftSeries x| :=
      abs_sub _ _
    _ ≤ 2 + 1 := add_le_add (abs_prawitzH_le_two x)
      (abs_prawitzShiftSeriesDifference_le_one x)
    _ = 3 := by norm_num

/-- Uniform physical-space bound for the Abel shift series. -/
theorem norm_prawitzAbelShiftSeries_le_one
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (x : ℝ) :
    ‖prawitzAbelShiftSeries r x‖ ≤ 1 := by
  let d : ℕ → ℂ := fun m =>
    ((r : ℂ) ^ (m + 1)) *
      (prawitzJC (x - ((m : ℝ) + 1)) -
        prawitzJC (x + ((m : ℝ) + 1)))
  let b : ℕ → ℝ := fun m =>
    prawitzJ (x - ((m : ℝ) + 1)) +
      prawitzJ (x + ((m : ℝ) + 1))
  have hleft := summable_prawitzLeftShiftSeries x
  have hright := summable_prawitzRightShiftSeries x
  have hb : Summable b := by
    simpa only [b] using hleft.add hright
  have hdNorm : Summable (fun m : ℕ => ‖d m‖) := by
    refine Summable.of_nonneg_of_le (f := b) (fun m => norm_nonneg _) ?_ hb
    intro m
    dsimp only [d, b]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    have hrpow : r ^ (m + 1) ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hr0 hr1 (m + 1)
    calc
      r ^ (m + 1) *
          ‖prawitzJC (x - ((m : ℝ) + 1)) -
            prawitzJC (x + ((m : ℝ) + 1))‖ ≤
          1 *
            (‖prawitzJC (x - ((m : ℝ) + 1))‖ +
              ‖prawitzJC (x + ((m : ℝ) + 1))‖) := by
        gcongr
        exact norm_sub_le _ _
      _ = prawitzJ (x - ((m : ℝ) + 1)) +
          prawitzJ (x + ((m : ℝ) + 1)) := by
        dsimp only [prawitzJC]
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (prawitzJ_nonneg _), Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (prawitzJ_nonneg _)]
        ring
  calc
    ‖prawitzAbelShiftSeries r x‖ = ‖∑' m : ℕ, d m‖ := by rfl
    _ ≤ ∑' m : ℕ, ‖d m‖ := norm_tsum_le_tsum_norm hdNorm
    _ ≤ ∑' m : ℕ, b m := by
      exact hdNorm.tsum_le_tsum (fun m => by
        dsimp only [d, b]
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hr0]
        have hrpow : r ^ (m + 1) ≤ 1 := by
          simpa only [one_pow] using pow_le_pow_left₀ hr0 hr1 (m + 1)
        calc
          r ^ (m + 1) *
              ‖prawitzJC (x - ((m : ℝ) + 1)) -
                prawitzJC (x + ((m : ℝ) + 1))‖ ≤
              1 *
                (‖prawitzJC (x - ((m : ℝ) + 1))‖ +
                  ‖prawitzJC (x + ((m : ℝ) + 1))‖) := by
            gcongr
            exact norm_sub_le _ _
          _ = b m := by
            dsimp only [b, prawitzJC]
            rw [Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (prawitzJ_nonneg _), Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg (prawitzJ_nonneg _)]
            ring)
        hb
    _ = prawitzLeftShiftSeries x + prawitzRightShiftSeries x := by
      unfold b prawitzLeftShiftSeries prawitzRightShiftSeries
      exact hleft.tsum_add hright
    _ ≤ 1 := prawitzShiftSeries_sum_le_one x

/-- Abel's limit theorem identifies the regularized physical series with the
unweighted signed shift series as `r` approaches `1` from the left. -/
theorem tendsto_prawitzAbelShiftSeries (x : ℝ) :
    Tendsto (fun r : ℝ => prawitzAbelShiftSeries r x) (𝓝[<] (1 : ℝ))
      (𝓝 (((prawitzLeftShiftSeries x -
        prawitzRightShiftSeries x : ℝ) : ℂ))) := by
  let d : ℕ → ℂ := fun m =>
    prawitzJC (x - ((m : ℝ) + 1)) -
      prawitzJC (x + ((m : ℝ) + 1))
  have hd : Summable d := by
    simpa only [d] using summable_prawitzShiftDifference x
  have hpartial : Tendsto (fun n : ℕ => ∑ m ∈ Finset.range n, d m)
      atTop (𝓝 (∑' m : ℕ, d m)) := hd.hasSum.tendsto_sum_nat
  have habelComplex :=
    Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hpartial
  have habelReal : Tendsto
      (fun r : ℝ => ∑' m : ℕ, d m * (r : ℂ) ^ m)
      (𝓝[<] (1 : ℝ)) (𝓝 (∑' m : ℕ, d m)) := by
    exact habelComplex.comp Filter.tendsto_map
  have hr : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[<] (1 : ℝ))
      (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.mono_left inf_le_left
  have hseries (r : ℝ) :
      prawitzAbelShiftSeries r x =
        (r : ℂ) * ∑' m : ℕ, d m * (r : ℂ) ^ m := by
    unfold prawitzAbelShiftSeries
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    dsimp only [d]
    rw [pow_succ]
    ring
  have hmul := hr.mul habelReal
  simpa only [hseries, one_mul, d, tsum_prawitzShiftDifference] using hmul

/-! ## The compact-frequency representative of `2 S(x) / x` -/

/-- The inverse-frequency representative of the removable correction
`2 S(x) / x`.  Endpoints and the value at zero are immaterial to its
Lebesgue integral; the two half intervals make measurability and the
ordinary (non-principal-value) Fourier calculation explicit. -/
def prawitzCorrectionPreimage (t : ℝ) : ℂ :=
  Set.indicator (Set.Ioc (0 : ℝ) 1)
      (fun _ : ℝ => Complex.I / (Real.pi : ℂ)) t +
    Set.indicator (Set.Ioc (-1 : ℝ) 0)
      (fun _ : ℝ => -Complex.I / (Real.pi : ℂ)) t

theorem integrable_prawitzCorrectionPreimage :
    Integrable prawitzCorrectionPreimage := by
  have hpos : Integrable
      (Set.indicator (Set.Ioc (0 : ℝ) 1)
        (fun _ : ℝ => Complex.I / (Real.pi : ℂ))) := by
    exact (integrable_indicator_iff measurableSet_Ioc).2
      (integrableOn_const measure_Ioc_lt_top.ne : IntegrableOn
        (fun _ : ℝ => Complex.I / (Real.pi : ℂ)) (Set.Ioc (0 : ℝ) 1))
  have hneg : Integrable
      (Set.indicator (Set.Ioc (-1 : ℝ) 0)
        (fun _ : ℝ => -Complex.I / (Real.pi : ℂ))) := by
    exact (integrable_indicator_iff measurableSet_Ioc).2
      (integrableOn_const measure_Ioc_lt_top.ne : IntegrableOn
        (fun _ : ℝ => -Complex.I / (Real.pi : ℂ)) (Set.Ioc (-1 : ℝ) 0))
  exact hpos.add hneg

private theorem intervalIntegral_cexp_linear {a : ℂ} (ha : a ≠ 0) (p q : ℝ) :
    (∫ t in p..q, Complex.exp (a * (t : ℂ))) =
      (Complex.exp (a * (q : ℂ)) - Complex.exp (a * (p : ℂ))) / a := by
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => Complex.exp (a * (s : ℂ)) / a)
      (Complex.exp (a * (t : ℂ))) t := by
    intro t
    have ht : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      simpa using Complex.ofRealCLM.hasDerivAt (x := t)
    have hraw := ((ht.const_mul a).cexp).div_const a
    convert hraw using 1 <;> field_simp [ha] <;> ring
  have hint : IntervalIntegrable
      (fun t : ℝ => Complex.exp (a * (t : ℂ))) volume p q := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    (∫ t in p..q, Complex.exp (a * (t : ℂ))) =
        Complex.exp (a * (q : ℂ)) / a -
          Complex.exp (a * (p : ℂ)) / a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hderiv t) hint
    _ = (Complex.exp (a * (q : ℂ)) -
          Complex.exp (a * (p : ℂ))) / a := by ring

private theorem fourier_indicator_const_Ioc {p q : ℝ} (hpq : p ≤ q)
    (c : ℂ) (x : ℝ) :
    FourierTransform.fourier
        (Set.indicator (Set.Ioc p q) (fun _ : ℝ => c)) x =
      c * (∫ t in p..q,
        Complex.exp ((((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I) * (t : ℂ))) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [show (fun t : ℝ =>
      Complex.exp (((( -2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I)) *
        Set.indicator (Set.Ioc p q) (fun _ : ℝ => c) t) =
      Set.indicator (Set.Ioc p q) (fun t : ℝ =>
        c * Complex.exp ((((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I) * (t : ℂ))) by
        funext t
        by_cases ht : t ∈ Set.Ioc p q
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
          have hexp :
              Complex.exp ((((-2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I)) =
                Complex.exp ((((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I) *
                  (t : ℂ)) := by
            congr 1
            push_cast
            ring
          rw [hexp]
          ring
        · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hpq]
  exact intervalIntegral.integral_const_mul c _

/-- The ordinary Fourier transform of the compactly supported correction
frequency is the removable real-space function `2 S(x) / x`.  This is the
classical principal-value identity in the direction that only uses an `L¹`
frequency function. -/
theorem fourier_prawitzCorrectionPreimage (x : ℝ) :
    FourierTransform.fourier prawitzCorrectionPreimage x =
      (((2 * prawitzS x / x : ℝ) : ℂ)) := by
  let fpos : ℝ → ℂ := Set.indicator (Set.Ioc (0 : ℝ) 1)
    (fun _ : ℝ => Complex.I / (Real.pi : ℂ))
  let fneg : ℝ → ℂ := Set.indicator (Set.Ioc (-1 : ℝ) 0)
    (fun _ : ℝ => -Complex.I / (Real.pi : ℂ))
  have hpos : Integrable fpos := by
    dsimp only [fpos]
    exact (integrable_indicator_iff measurableSet_Ioc).2
      (integrableOn_const measure_Ioc_lt_top.ne : IntegrableOn
        (fun _ : ℝ => Complex.I / (Real.pi : ℂ)) (Set.Ioc (0 : ℝ) 1))
  have hneg : Integrable fneg := by
    dsimp only [fneg]
    exact (integrable_indicator_iff measurableSet_Ioc).2
      (integrableOn_const measure_Ioc_lt_top.ne : IntegrableOn
        (fun _ : ℝ => -Complex.I / (Real.pi : ℂ)) (Set.Ioc (-1 : ℝ) 0))
  have hposPhase : Integrable
      (fun v : ℝ => Real.fourierChar (-(inner ℝ v x)) • fpos v) :=
    (Real.fourierIntegral_convergent_iff x).2 hpos
  have hnegPhase : Integrable
      (fun v : ℝ => Real.fourierChar (-(inner ℝ v x)) • fneg v) :=
    (Real.fourierIntegral_convergent_iff x).2 hneg
  have hadd : FourierTransform.fourier prawitzCorrectionPreimage x =
      FourierTransform.fourier fpos x + FourierTransform.fourier fneg x := by
    change FourierTransform.fourier (fpos + fneg) x = _
    rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
    simp_rw [Pi.add_apply, smul_add]
    exact integral_add hposPhase hnegPhase
  rw [hadd]
  change FourierTransform.fourier
      (Set.indicator (Set.Ioc (0 : ℝ) 1)
        (fun _ : ℝ => Complex.I / (Real.pi : ℂ))) x +
      FourierTransform.fourier
      (Set.indicator (Set.Ioc (-1 : ℝ) 0)
        (fun _ : ℝ => -Complex.I / (Real.pi : ℂ))) x = _
  rw [fourier_indicator_const_Ioc (by norm_num : (0 : ℝ) ≤ 1),
    fourier_indicator_const_Ioc (by norm_num : (-1 : ℝ) ≤ 0)]
  by_cases hx : x = 0
  · subst x
    simp [prawitzS]
    ring
  · let a : ℂ := (((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    have ha : a ≠ 0 := by
      dsimp only [a]
      apply mul_ne_zero
      · exact Complex.ofReal_ne_zero.mpr
          (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx)
      · exact Complex.I_ne_zero
    have hposInt := intervalIntegral_cexp_linear ha (0 : ℝ) 1
    have hnegInt := intervalIntegral_cexp_linear ha (-1 : ℝ) 0
    change Complex.I / (Real.pi : ℂ) *
          (∫ t in (0 : ℝ)..1, Complex.exp (a * (t : ℂ))) +
        (-Complex.I / (Real.pi : ℂ)) *
          (∫ t in (-1 : ℝ)..0, Complex.exp (a * (t : ℂ))) = _
    rw [hposInt, hnegInt]
    have hexpSum : Complex.exp a + Complex.exp (-a) =
        (((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ)) := by
      have haNeg : a = (((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I) := by
        dsimp only [a]
        push_cast
        ring
      have hnega : -a = ((((2 * Real.pi * x) : ℝ) : ℂ) * Complex.I) := by
        dsimp only [a]
        push_cast
        ring
      rw [hnega, haNeg, Complex.exp_mul_I, Complex.exp_mul_I]
      push_cast
      rw [Complex.cos_neg, Complex.sin_neg]
      ring
    have htrig : 1 - Real.cos (2 * Real.pi * x) =
        2 * Real.sin (Real.pi * x) ^ 2 := by
      rw [show 2 * Real.pi * x = Real.pi * x + Real.pi * x by ring,
        Real.cos_add]
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]
    have haValue : a = -((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
      dsimp only [a]
      push_cast
      ring
    norm_num only [Complex.ofReal_one, Complex.ofReal_zero, Complex.ofReal_neg,
      mul_one, mul_zero, Complex.exp_zero, mul_neg]
    calc
      Complex.I / (Real.pi : ℂ) * ((Complex.exp a - 1) / a) +
          (-Complex.I / (Real.pi : ℂ)) * ((1 - Complex.exp (-a)) / a) =
          (Complex.I / ((Real.pi : ℂ) * a)) *
            (Complex.exp a + Complex.exp (-a) - 2) := by ring
      _ = ((((1 - Real.cos (2 * Real.pi * x)) /
          (Real.pi ^ 2 * x) : ℝ) : ℂ)) := by
        rw [hexpSum, haValue]
        push_cast
        field_simp [Real.pi_ne_zero, hx, Complex.I_ne_zero]
        ring
      _ = (((2 * prawitzS x / x : ℝ) : ℂ)) := by
        rw [htrig, prawitzS]
        push_cast
        field_simp [Real.pi_ne_zero, hx]

/-! ## A public frequency representative for the tent function -/

/-- The complexification of the compactly supported tent function. -/
def prawitzTentC (t : ℝ) : ℂ :=
  ((StatLean.HypothesisTesting.tent t : ℝ) : ℂ)

theorem continuous_prawitzTentC : Continuous prawitzTentC :=
  Complex.continuous_ofReal.comp
    StatLean.HypothesisTesting.continuous_tent

theorem hasCompactSupport_prawitzTentC : HasCompactSupport prawitzTentC :=
  HasCompactSupport.intro
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun t ht => by
      simp [prawitzTentC,
        StatLean.HypothesisTesting.tent_eq_zero_of_notMem ht]

theorem integrable_prawitzTentC : Integrable prawitzTentC :=
  continuous_prawitzTentC.integrable_of_hasCompactSupport
    hasCompactSupport_prawitzTentC

/-- The second half of the Fejer/triangle Fourier pair, stated for the public
tent representative used by the Prawitz sandwich. -/
theorem fourier_prawitzTentC (x : ℝ) :
    FourierTransform.fourier prawitzTentC x = prawitzJC x := by
  have hFint : Integrable (FourierTransform.fourier prawitzJC) := by
    rw [fourier_prawitzJC]
    exact integrable_prawitzTentC
  have hinv := continuous_prawitzJC.fourierInv_fourier_eq
    integrable_prawitzJC hFint
  calc
    FourierTransform.fourier prawitzTentC x =
        FourierTransform.fourier
          (FourierTransform.fourier prawitzJC) x := by
      rw [fourier_prawitzJC]
      rfl
    _ = FourierTransform.fourierInv
        (FourierTransform.fourier prawitzJC) (-x) := by
      rw [Real.fourierInv_eq_fourier_neg]
      simp
    _ = prawitzJC (-x) := congrFun hinv (-x)
    _ = prawitzJC x := prawitzJC_neg x

theorem norm_prawitzJC_le_one (x : ℝ) : ‖prawitzJC x‖ ≤ 1 := by
  rw [prawitzJC, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (prawitzJ_nonneg x)]
  exact prawitzJ_le_one x

/-! ## The complete Abel representative of Prawitz's approximant -/

/-- The ordinary `L¹` frequency representative obtained by adding the compact
correction to the Abel-regularized shift component. -/
def prawitzAbelHPreimage (r t : ℝ) : ℂ :=
  prawitzAbelShiftPreimage r t + prawitzCorrectionPreimage t

theorem integrable_prawitzAbelHPreimage {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Integrable (prawitzAbelHPreimage r) :=
  (integrable_prawitzAbelShiftPreimage hr0 hr1).add
    integrable_prawitzCorrectionPreimage

private theorem fourier_add_of_integrable
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    FourierTransform.fourier (fun t : ℝ => f t + g t) x =
      FourierTransform.fourier f x + FourierTransform.fourier g x := by
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
  simp_rw [smul_add]
  exact integral_add ((Real.fourierIntegral_convergent_iff x).2 hf)
    ((Real.fourierIntegral_convergent_iff x).2 hg)

/-- The full Abel representative transforms to the weighted signed shifts plus
the removable correction. -/
theorem fourier_prawitzAbelHPreimage
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    FourierTransform.fourier (prawitzAbelHPreimage r) x =
      prawitzAbelShiftSeries r x + (((2 * prawitzS x / x : ℝ) : ℂ)) := by
  change FourierTransform.fourier (fun t : ℝ =>
    prawitzAbelShiftPreimage r t + prawitzCorrectionPreimage t) x = _
  rw [fourier_add_of_integrable
      (integrable_prawitzAbelShiftPreimage hr0 hr1)
      integrable_prawitzCorrectionPreimage,
    fourier_prawitzAbelShiftPreimage hr0 hr1,
    fourier_prawitzCorrectionPreimage]

/-- A uniform bound for the physical-space transforms of the full Abel
representatives.  This supplies the dominating function used when the Abel
parameter tends to one inside a finite-measure integral. -/
theorem norm_fourier_prawitzAbelHPreimage_le_four
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    ‖FourierTransform.fourier (prawitzAbelHPreimage r) x‖ ≤ 4 := by
  rw [fourier_prawitzAbelHPreimage hr0 hr1]
  calc
    ‖prawitzAbelShiftSeries r x + (((2 * prawitzS x / x : ℝ) : ℂ))‖ ≤
        ‖prawitzAbelShiftSeries r x‖ +
          ‖(((2 * prawitzS x / x : ℝ) : ℂ))‖ := norm_add_le _ _
    _ ≤ 1 + 3 := by
      gcongr
      · exact norm_prawitzAbelShiftSeries_le_one hr0 hr1.le x
      · rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_prawitzCorrection_le_three x
    _ = 4 := by norm_num

/-! ## Ordinary representatives of the Vaaler upper and lower corrections -/

/-- The nonconstant part of the Abel-regularized upper majorant.  Its Fourier
transform tends to `(J - H) / 2`; the remaining constant `1 / 2` is handled
directly at the probability-integral level. -/
def prawitzAbelUpperPreimage (r t : ℝ) : ℂ :=
  (1 / 2 : ℂ) *
    (prawitzTentC t - prawitzAbelHPreimage r t)

/-- The nonconstant part of the Abel-regularized lower minorant. -/
def prawitzAbelLowerPreimage (r t : ℝ) : ℂ :=
  (1 / 2 : ℂ) *
    (-prawitzAbelHPreimage r t - prawitzTentC t)

theorem integrable_prawitzAbelUpperPreimage
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Integrable (prawitzAbelUpperPreimage r) :=
  (integrable_prawitzTentC.sub
    (integrable_prawitzAbelHPreimage hr0 hr1)).const_mul _

theorem integrable_prawitzAbelLowerPreimage
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Integrable (prawitzAbelLowerPreimage r) :=
  ((integrable_prawitzAbelHPreimage hr0 hr1).neg.sub
    integrable_prawitzTentC).const_mul _

theorem fourier_prawitzAbelUpperPreimage
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    FourierTransform.fourier (prawitzAbelUpperPreimage r) x =
      (1 / 2 : ℂ) *
        (prawitzJC x -
          FourierTransform.fourier (prawitzAbelHPreimage r) x) := by
  unfold prawitzAbelUpperPreimage
  rw [fourier_const_mul,
    fourier_sub_of_integrable integrable_prawitzTentC
      (integrable_prawitzAbelHPreimage hr0 hr1),
    fourier_prawitzTentC]

theorem fourier_prawitzAbelLowerPreimage
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    FourierTransform.fourier (prawitzAbelLowerPreimage r) x =
      (1 / 2 : ℂ) *
        (-FourierTransform.fourier (prawitzAbelHPreimage r) x -
          prawitzJC x) := by
  have hnegInt : Integrable (fun t : ℝ =>
      -prawitzAbelHPreimage r t) :=
    (integrable_prawitzAbelHPreimage hr0 hr1).neg
  have hnegFourier :
      FourierTransform.fourier
          (fun t : ℝ => -prawitzAbelHPreimage r t) x =
        -FourierTransform.fourier (prawitzAbelHPreimage r) x := by
    simpa using fourier_const_mul (-1 : ℂ)
      (prawitzAbelHPreimage r) x
  unfold prawitzAbelLowerPreimage
  rw [fourier_const_mul,
    fourier_sub_of_integrable hnegInt integrable_prawitzTentC,
    hnegFourier, fourier_prawitzTentC]

theorem norm_fourier_prawitzAbelUpperPreimage_le_three
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    ‖FourierTransform.fourier (prawitzAbelUpperPreimage r) x‖ ≤ 3 := by
  rw [fourier_prawitzAbelUpperPreimage hr0 hr1, norm_mul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  calc
    1 / 2 *
        ‖prawitzJC x -
          FourierTransform.fourier (prawitzAbelHPreimage r) x‖ ≤
        1 / 2 *
          (‖prawitzJC x‖ +
            ‖FourierTransform.fourier (prawitzAbelHPreimage r) x‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ 1 / 2 * (1 + 4) := by
      gcongr
      · exact norm_prawitzJC_le_one x
      · exact norm_fourier_prawitzAbelHPreimage_le_four hr0 hr1 x
    _ ≤ 3 := by norm_num

theorem norm_fourier_prawitzAbelLowerPreimage_le_three
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    ‖FourierTransform.fourier (prawitzAbelLowerPreimage r) x‖ ≤ 3 := by
  rw [fourier_prawitzAbelLowerPreimage hr0 hr1, norm_mul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  calc
    1 / 2 *
        ‖-FourierTransform.fourier (prawitzAbelHPreimage r) x -
          prawitzJC x‖ ≤
        1 / 2 *
          (‖FourierTransform.fourier (prawitzAbelHPreimage r) x‖ +
            ‖prawitzJC x‖) := by
      gcongr
      simpa only [norm_neg] using
        norm_sub_le
          (-FourierTransform.fourier (prawitzAbelHPreimage r) x)
          (prawitzJC x)
    _ ≤ 1 / 2 * (4 + 1) := by
      gcongr
      · exact norm_fourier_prawitzAbelHPreimage_le_four hr0 hr1 x
      · exact norm_prawitzJC_le_one x
    _ ≤ 3 := by norm_num

/-- Pointwise, the Fourier transforms of the ordinary Abel representatives
converge from within `r < 1` to the real-space Prawitz approximant `H`.
This is the precise ordinary-function replacement for the distributional
boundary formula in the source notes. -/
theorem tendsto_fourier_prawitzAbelHPreimage (x : ℝ) :
    Tendsto
      (fun r : ℝ =>
        FourierTransform.fourier (prawitzAbelHPreimage r) x)
      (𝓝[<] (1 : ℝ)) (𝓝 (((prawitzH x : ℝ) : ℂ))) := by
  have hbase := (tendsto_prawitzAbelShiftSeries x).add_const
    (((2 * prawitzS x / x : ℝ) : ℂ))
  have htarget :
      (((prawitzLeftShiftSeries x - prawitzRightShiftSeries x : ℝ) : ℂ)) +
          (((2 * prawitzS x / x : ℝ) : ℂ)) =
        ((prawitzH x : ℝ) : ℂ) := by
    rw [← prawitzShiftH_eq_prawitzH]
    unfold prawitzShiftH
    push_cast
    ring
  have heq :
      (fun r : ℝ => prawitzAbelShiftSeries r x +
        (((2 * prawitzS x / x : ℝ) : ℂ))) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun r : ℝ =>
        FourierTransform.fourier (prawitzAbelHPreimage r) x) := by
    filter_upwards [nhdsWithin_le_nhds
        (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      self_mem_nhdsWithin] with r hr0 hr1
    exact (fourier_prawitzAbelHPreimage hr0 hr1 x).symm
  rw [← htarget]
  exact Filter.Tendsto.congr' heq hbase

theorem tendsto_fourier_prawitzAbelUpperPreimage (x : ℝ) :
    Tendsto
      (fun r : ℝ =>
        FourierTransform.fourier (prawitzAbelUpperPreimage r) x)
      (𝓝[<] (1 : ℝ))
      (𝓝 ((1 / 2 : ℂ) *
        (prawitzJC x - ((prawitzH x : ℝ) : ℂ)))) := by
  have hhalf : Tendsto (fun _ : ℝ => (1 / 2 : ℂ))
      (𝓝[<] (1 : ℝ)) (𝓝 (1 / 2 : ℂ)) := tendsto_const_nhds
  have hJ : Tendsto (fun _ : ℝ => prawitzJC x)
      (𝓝[<] (1 : ℝ)) (𝓝 (prawitzJC x)) := tendsto_const_nhds
  have hbase := hhalf.mul
    (hJ.sub (tendsto_fourier_prawitzAbelHPreimage x))
  have heq :
      (fun r : ℝ => (1 / 2 : ℂ) *
        (prawitzJC x -
          FourierTransform.fourier (prawitzAbelHPreimage r) x))
        =ᶠ[𝓝[<] (1 : ℝ)]
      (fun r : ℝ =>
        FourierTransform.fourier (prawitzAbelUpperPreimage r) x) := by
    filter_upwards [nhdsWithin_le_nhds
        (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      self_mem_nhdsWithin] with r hr0 hr1
    exact (fourier_prawitzAbelUpperPreimage hr0 hr1 x).symm
  exact Filter.Tendsto.congr' heq hbase

theorem tendsto_fourier_prawitzAbelLowerPreimage (x : ℝ) :
    Tendsto
      (fun r : ℝ =>
        FourierTransform.fourier (prawitzAbelLowerPreimage r) x)
      (𝓝[<] (1 : ℝ))
      (𝓝 ((1 / 2 : ℂ) *
        (-((prawitzH x : ℝ) : ℂ) - prawitzJC x))) := by
  have hhalf : Tendsto (fun _ : ℝ => (1 / 2 : ℂ))
      (𝓝[<] (1 : ℝ)) (𝓝 (1 / 2 : ℂ)) := tendsto_const_nhds
  have hJ : Tendsto (fun _ : ℝ => prawitzJC x)
      (𝓝[<] (1 : ℝ)) (𝓝 (prawitzJC x)) := tendsto_const_nhds
  have hbase := hhalf.mul
    ((tendsto_fourier_prawitzAbelHPreimage x).neg.sub hJ)
  have heq :
      (fun r : ℝ => (1 / 2 : ℂ) *
        (-FourierTransform.fourier (prawitzAbelHPreimage r) x -
          prawitzJC x))
        =ᶠ[𝓝[<] (1 : ℝ)]
      (fun r : ℝ =>
        FourierTransform.fourier (prawitzAbelLowerPreimage r) x) := by
    filter_upwards [nhdsWithin_le_nhds
        (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      self_mem_nhdsWithin] with r hr0 hr1
    exact (fourier_prawitzAbelLowerPreimage hr0 hr1 x).symm
  exact Filter.Tendsto.congr' heq hbase

end

end BerryEsseen
