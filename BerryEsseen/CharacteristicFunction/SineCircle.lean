import BerryEsseen.CharacteristicFunction.MomentGeometry
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The sine-remainder circle

This module formalizes Route B equation (2.5).  The first layer isolates the
sharp scalar estimate behind the centered two-point laws; the measure-mixture
argument is built on top of that estimate.
-/

open MeasureTheory

namespace BerryEsseen

noncomputable section

/-- The derivative numerator of `sinc` has the sharp cubic bound used in the
two-point sine circle. -/
theorem abs_mul_cos_sub_sin_le_cube_div_three (z : ℝ) (hz : 0 ≤ z) :
    |z * Real.cos z - Real.sin z| ≤ z ^ 3 / 3 := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => Real.sin s - s * Real.cos s) (t * Real.sin t) t := by
    intro t
    convert (Real.hasDerivAt_sin t).sub
      ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t)) using 1
    simp only [id_eq]
    ring
  have hintegral :
      (∫ t : ℝ in (0 : ℝ)..z, t * Real.sin t) = Real.sin z - z * Real.cos z := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv t) ((continuous_id.mul Real.continuous_sin).intervalIntegrable 0 z)
  have hbound :
      ‖∫ t : ℝ in (0 : ℝ)..z, t * Real.sin t‖ ≤ ∫ t : ℝ in (0 : ℝ)..z, t ^ 2 := by
    refine intervalIntegral.norm_integral_le_of_norm_le hz (Filter.Eventually.of_forall ?_)
      ((continuous_id.pow 2).intervalIntegrable 0 z)
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt ht.1
    have hsin := Real.abs_sin_le_abs (x := t)
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht0, pow_two] using
      mul_le_mul_of_nonneg_left hsin ht0
  rw [hintegral] at hbound
  norm_num at hbound
  simpa [Real.norm_eq_abs, abs_sub_comm] using hbound

/-- `s ↦ sinc (sqrt s)`, the source proof's reparameterization by `z²`. -/
def sincSquare (s : ℝ) : ℝ := Real.sinc (Real.sqrt s)

/-- The derivative of `sincSquare` away from zero. -/
def sincSquareDerivative (s : ℝ) : ℝ :=
  (Real.sqrt s * Real.cos (Real.sqrt s) - Real.sin (Real.sqrt s)) /
    (2 * Real.sqrt s ^ 3)

theorem hasDerivAt_sinc_of_ne_zero {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt Real.sinc ((z * Real.cos z - Real.sin z) / z ^ 2) z := by
  have hdiv : HasDerivAt (fun w : ℝ => Real.sin w / w)
      ((Real.cos z * z - Real.sin z) / z ^ 2) z := by
    simpa only [id_eq, mul_one] using
      (Real.hasDerivAt_sin z).div (hasDerivAt_id z) hz
  have heq : Real.sinc =ᶠ[nhds z] fun w : ℝ => Real.sin w / w := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact Real.sinc_of_ne_zero hw
  convert hdiv.congr_of_eventuallyEq heq using 1
  ring

theorem hasDerivAt_sincSquare {s : ℝ} (hs : 0 < s) :
    HasDerivAt sincSquare (sincSquareDerivative s) s := by
  have hz : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hcomp := (hasDerivAt_sinc_of_ne_zero hz.ne').comp s
    (Real.hasDerivAt_sqrt hs.ne')
  unfold sincSquare sincSquareDerivative
  convert hcomp using 1
  field_simp [hz.ne']

theorem abs_sincSquareDerivative_le_one_sixth {s : ℝ} (hs : 0 < s) :
    |sincSquareDerivative s| ≤ (1 : ℝ) / 6 := by
  have hz : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hnum := abs_mul_cos_sub_sin_le_cube_div_three (Real.sqrt s) hz.le
  have hden : 0 < 2 * Real.sqrt s ^ 3 := by positivity
  unfold sincSquareDerivative
  rw [abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  nlinarith

theorem continuous_sincSquare : Continuous sincSquare := by
  exact Real.continuous_sinc.comp Real.continuous_sqrt

/-- The sharp Lipschitz estimate for `sinc` after reparameterization by the
square, corresponding to the derivative bound `1/6` in the source proof. -/
theorem abs_sinc_sub_sinc_le_sq_sub_of_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    |Real.sinc x - Real.sinc y| ≤ (y ^ 2 - x ^ 2) / 6 := by
  rcases hxy.eq_or_lt with rfl | hxy
  · simp
  have hab : x ^ 2 < y ^ 2 := by nlinarith
  have hderiv : ∀ s ∈ Set.Ioo (x ^ 2) (y ^ 2),
      HasDerivAt sincSquare (sincSquareDerivative s) s := by
    intro s hs
    exact hasDerivAt_sincSquare (lt_of_le_of_lt (sq_nonneg x) hs.1)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope sincSquare sincSquareDerivative
    hab continuous_sincSquare.continuousOn hderiv
  have hcpos : 0 < c := lt_of_le_of_lt (sq_nonneg x) hc.1
  have hderivBound := abs_sincSquareDerivative_le_one_sixth hcpos
  have heq : sincSquare (y ^ 2) - sincSquare (x ^ 2) =
      sincSquareDerivative c * (y ^ 2 - x ^ 2) := by
    exact ((eq_div_iff (sub_ne_zero.mpr hab.ne')).mp hslope).symm
  have hfunc : |sincSquare (y ^ 2) - sincSquare (x ^ 2)| ≤
      (y ^ 2 - x ^ 2) / 6 := by
    rw [heq, abs_mul,
      abs_of_nonneg (show 0 ≤ y ^ 2 - x ^ 2 by linarith)]
    calc
      |sincSquareDerivative c| * (y ^ 2 - x ^ 2) ≤
          ((1 : ℝ) / 6) * (y ^ 2 - x ^ 2) :=
        mul_le_mul_of_nonneg_right hderivBound (sub_nonneg.mpr hab.le)
      _ = (y ^ 2 - x ^ 2) / 6 := by ring
  simpa [sincSquare, Real.sqrt_sq hx, Real.sqrt_sq (hx.trans hxy.le), abs_sub_comm] using hfunc

theorem abs_sinc_sub_sinc_le_sq_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sinc x - Real.sinc y| ≤ |x ^ 2 - y ^ 2| / 6 := by
  rcases le_total x y with hxy | hyx
  · have h := abs_sinc_sub_sinc_le_sq_sub_of_le hx hxy
    have hsquares : x ^ 2 ≤ y ^ 2 := by nlinarith
    simpa [abs_of_nonpos (sub_nonpos.mpr hsquares)] using h
  · have h := abs_sinc_sub_sinc_le_sq_sub_of_le hy hyx
    have hsquares : y ^ 2 ≤ x ^ 2 := by nlinarith
    simpa [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hsquares)] using h

/-- The normalized stop-loss-square coordinate of a centered two-point law. -/
def twoPointEnergyRatio (x y : ℝ) : ℝ := 2 * x * y / (x ^ 2 + y ^ 2)

/-- The normalized sine coordinate of a centered two-point law. -/
def twoPointSineRatio (x y : ℝ) : ℝ :=
  -6 * (y * Real.sin x - x * Real.sin y) /
    (x * y * (x ^ 2 + y ^ 2))

/-- The scalar core of Route B's sine-remainder circle: every positive
centered two-point law contributes a vector in the Euclidean unit disk. -/
theorem twoPoint_energy_sine_circle {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    twoPointEnergyRatio x y ^ 2 + twoPointSineRatio x y ^ 2 ≤ 1 := by
  have hsinc := abs_sinc_sub_sinc_le_sq_sub hx.le hy.le
  have hxy : 0 < x * y := mul_pos hx hy
  have hsum : 0 < x ^ 2 + y ^ 2 := by positivity
  have hscale : 0 ≤ 6 * x * y := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsinc hscale
  have hleft :
      6 * x * y * |Real.sinc x - Real.sinc y| =
        6 * |y * Real.sin x - x * Real.sin y| := by
    rw [Real.sinc_of_ne_zero hx.ne', Real.sinc_of_ne_zero hy.ne']
    rw [show Real.sin x / x - Real.sin y / y =
        (y * Real.sin x - x * Real.sin y) / (x * y) by
      field_simp [hx.ne', hy.ne']
      ]
    rw [abs_div, abs_of_pos hxy]
    field_simp [hxy.ne']
  have hright :
      6 * x * y * (|x ^ 2 - y ^ 2| / 6) = x * y * |x ^ 2 - y ^ 2| := by
    ring
  rw [hleft, hright] at hscaled
  have hnum :
      |-6 * (y * Real.sin x - x * Real.sin y)| ≤
        x * y * |x ^ 2 - y ^ 2| := by
    simpa [abs_mul] using hscaled
  have hden : 0 < x * y * (x ^ 2 + y ^ 2) := mul_pos hxy hsum
  have hcoordinate :
      |twoPointSineRatio x y| ≤ |x ^ 2 - y ^ 2| / (x ^ 2 + y ^ 2) := by
    unfold twoPointSineRatio
    rw [abs_div, abs_of_pos hden]
    have hdiv := div_le_div_of_nonneg_right hnum hden.le
    calc
      |-6 * (y * Real.sin x - x * Real.sin y)| /
          (x * y * (x ^ 2 + y ^ 2)) ≤
          (x * y * |x ^ 2 - y ^ 2|) /
            (x * y * (x ^ 2 + y ^ 2)) := hdiv
      _ = |x ^ 2 - y ^ 2| / (x ^ 2 + y ^ 2) := by
        field_simp [hxy.ne', hsum.ne']
  have hcoordinateSq : twoPointSineRatio x y ^ 2 ≤
      (|x ^ 2 - y ^ 2| / (x ^ 2 + y ^ 2)) ^ 2 := by
    have hproduct := mul_nonneg
      (sub_nonneg.mpr hcoordinate)
      (add_nonneg (abs_nonneg (twoPointSineRatio x y))
        (by positivity : 0 ≤ |x ^ 2 - y ^ 2| / (x ^ 2 + y ^ 2)))
    rw [← sq_abs (twoPointSineRatio x y)]
    nlinarith
  have hcircleIdentity :
      twoPointEnergyRatio x y ^ 2 +
        (|x ^ 2 - y ^ 2| / (x ^ 2 + y ^ 2)) ^ 2 = 1 := by
    unfold twoPointEnergyRatio
    simp only [div_pow, sq_abs]
    field_simp [hsum.ne']
    ring
  calc
    twoPointEnergyRatio x y ^ 2 + twoPointSineRatio x y ^ 2 ≤
        twoPointEnergyRatio x y ^ 2 +
          (|x ^ 2 - y ^ 2| / (x ^ 2 + y ^ 2)) ^ 2 :=
      add_le_add_right hcoordinateSq _
    _ = 1 := hcircleIdentity

/-- `J_{a,b}` for the centered two-point law supported at `a` and `-b`. -/
def twoPointWeightedMoment (a b : ℝ) : ℝ :=
  a * b * (a ^ 2 + b ^ 2) / (6 * (a + b))

/-- `E_{a,b}`, the integrated sum of squared stop-loss transforms. -/
def twoPointStopLossEnergy (a b : ℝ) : ℝ :=
  a ^ 2 * b ^ 2 / (3 * (a + b))

/-- `H_{a,b}` at positive frequency `u`. -/
def twoPointSineMoment (u a b : ℝ) : ℝ :=
  (a * Real.sin (u * b) - b * Real.sin (u * a)) /
    ((a + b) * u ^ 3)

theorem twoPointStopLossEnergy_eq_weightedMoment_mul_ratio
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    twoPointStopLossEnergy a b =
      twoPointWeightedMoment a b * twoPointEnergyRatio a b := by
  have hab : 0 < a + b := add_pos ha hb
  have hsum : 0 < a ^ 2 + b ^ 2 := by positivity
  unfold twoPointStopLossEnergy twoPointWeightedMoment twoPointEnergyRatio
  field_simp [hab.ne', hsum.ne']
  ring

theorem twoPointSineMoment_eq_weightedMoment_mul_ratio
    {u a b : ℝ} (hu : 0 < u) (ha : 0 < a) (hb : 0 < b) :
    twoPointSineMoment u a b =
      twoPointWeightedMoment a b * twoPointSineRatio (u * a) (u * b) := by
  have hab : 0 < a + b := add_pos ha hb
  have hsum : 0 < (u * a) ^ 2 + (u * b) ^ 2 := by positivity
  unfold twoPointSineMoment twoPointWeightedMoment twoPointSineRatio
  field_simp [hu.ne', ha.ne', hb.ne', hab.ne', hsum.ne']
  ring

/-- Source equation preceding (2.6): the energy/sine vector of each centered
two-point component lies in its disk of radius `J_{a,b}`. -/
theorem twoPoint_moment_sine_circle {u a b : ℝ}
    (hu : 0 < u) (ha : 0 < a) (hb : 0 < b) :
    twoPointStopLossEnergy a b ^ 2 + twoPointSineMoment u a b ^ 2 ≤
      twoPointWeightedMoment a b ^ 2 := by
  have hcircle := twoPoint_energy_sine_circle (mul_pos hu ha) (mul_pos hu hb)
  have henergy := twoPointStopLossEnergy_eq_weightedMoment_mul_ratio ha hb
  have hsine := twoPointSineMoment_eq_weightedMoment_mul_ratio hu ha hb
  rw [henergy, hsine]
  calc
    (twoPointWeightedMoment a b * twoPointEnergyRatio a b) ^ 2 +
        (twoPointWeightedMoment a b * twoPointSineRatio (u * a) (u * b)) ^ 2 =
        twoPointWeightedMoment a b ^ 2 *
          (twoPointEnergyRatio (u * a) (u * b) ^ 2 +
            twoPointSineRatio (u * a) (u * b) ^ 2) := by
      have henergyScale : twoPointEnergyRatio a b =
          twoPointEnergyRatio (u * a) (u * b) := by
        unfold twoPointEnergyRatio
        field_simp [hu.ne', ha.ne', hb.ne']
      rw [henergyScale]
      ring
    _ ≤ twoPointWeightedMoment a b ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hcircle (sq_nonneg _)
    _ = twoPointWeightedMoment a b ^ 2 := by ring

/-- Abstract Jensen--Minkowski aggregation used by the mixture proof.  It is
stated for an arbitrary measure: if the component vectors lie in disks of
radius `J`, then their integral vector lies in the disk of radius `∫ J`; a
smaller nonnegative first coordinate may replace the integrated one. -/
theorem integral_energy_sine_circle
    {α : Type*} [MeasurableSpace α]
    (nu : Measure α) (E H J : α → ℝ) (E₀ : ℝ)
    (hE : Integrable E nu) (hH : Integrable H nu) (hJ : Integrable J nu)
    (hJNonneg : ∀ᵐ p ∂nu, 0 ≤ J p)
    (hcircle : ∀ᵐ p ∂nu, E p ^ 2 + H p ^ 2 ≤ J p ^ 2)
    (hE₀Nonneg : 0 ≤ E₀) (hE₀ : E₀ ≤ ∫ p, E p ∂nu) :
    E₀ ^ 2 + (∫ p, H p ∂nu) ^ 2 ≤ (∫ p, J p ∂nu) ^ 2 := by
  let Z : α → ℂ := fun p => (E p : ℂ) + Complex.I * (H p : ℂ)
  have hZ : Integrable Z nu := hE.ofReal.add (hH.ofReal.const_mul Complex.I)
  have hpointNorm : ∀ᵐ p ∂nu, ‖Z p‖ ≤ J p := by
    filter_upwards [hJNonneg, hcircle] with p hpJ hpCircle
    apply (sq_le_sq₀ (norm_nonneg (Z p)) hpJ).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    simpa [Z, pow_two] using hpCircle
  have hnorm : ‖∫ p, Z p ∂nu‖ ≤ ∫ p, J p ∂nu := by
    calc
      ‖∫ p, Z p ∂nu‖ ≤ ∫ p, ‖Z p‖ ∂nu :=
        MeasureTheory.norm_integral_le_integral_norm Z
      _ ≤ ∫ p, J p ∂nu := integral_mono_ae hZ.norm hJ hpointNorm
  have hJIntegralNonneg : 0 ≤ ∫ p, J p ∂nu := integral_nonneg_of_ae hJNonneg
  have hvectorSq :
      (∫ p, E p ∂nu) ^ 2 + (∫ p, H p ∂nu) ^ 2 ≤
        (∫ p, J p ∂nu) ^ 2 := by
    have hsquare := (sq_le_sq₀ (norm_nonneg (∫ p, Z p ∂nu)) hJIntegralNonneg).mpr hnorm
    have hre : (∫ p, Z p ∂nu).re = ∫ p, E p ∂nu := by
      simpa [Z] using (integral_re hZ).symm
    have him : (∫ p, Z p ∂nu).im = ∫ p, H p ∂nu := by
      simpa [Z] using (integral_im hZ).symm
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him] at hsquare
    simpa [pow_two] using hsquare
  have hEsquare : E₀ ^ 2 ≤ (∫ p, E p ∂nu) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hE₀Nonneg hE₀
  exact (add_le_add_left hEsquare _).trans hvectorSq

theorem integrableOn_sin_mul_positivePart (u a : ℝ) :
    IntegrableOn (fun t : ℝ => Real.sin (u * t) * positivePart (a - t))
      (Set.Ici 0) volume := by
  have hcontinuous : Continuous (fun t : ℝ => Real.sin (u * t) * positivePart (a - t)) := by
    unfold positivePart
    fun_prop
  have hcompact : IntegrableOn
      (fun t : ℝ => Real.sin (u * t) * positivePart (a - t))
      (Set.Icc 0 (max a 0)) volume := hcontinuous.integrableOn_Icc
  apply hcompact.of_forall_diff_eq_zero measurableSet_Ici
  intro t ht
  have hnotle : ¬t ≤ max a 0 := fun htle => ht.2 ⟨ht.1, htle⟩
  have hat : a ≤ t := (le_max_left a 0).trans (lt_of_not_ge hnotle).le
  rw [show positivePart (a - t) = 0 by
    simp [positivePart, max_eq_right (sub_nonpos.mpr hat)]]
  exact mul_zero _

/-- Exact sine transform of a one-sided stop-loss kernel. -/
theorem sin_mul_positivePart_integral {u a : ℝ} (hu : 0 < u) (ha : 0 ≤ a) :
    (∫ t in Set.Ici (0 : ℝ), Real.sin (u * t) * positivePart (a - t)) =
      a / u - Real.sin (u * a) / u ^ 2 := by
  let f : ℝ → ℝ := fun t => Real.sin (u * t) * positivePart (a - t)
  have hrestrict : (∫ t in Set.Ici (0 : ℝ), f t) = ∫ t in Set.Icc 0 a, f t := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ici
    · intro t ht
      exact ht.1
    · intro t ht
      have hnotle : ¬t ≤ a := fun hta => ht.2 ⟨ht.1, hta⟩
      have hat : a ≤ t := (lt_of_not_ge hnotle).le
      dsimp [f]
      rw [show positivePart (a - t) = 0 by
        simp [positivePart, max_eq_right (sub_nonpos.mpr hat)]]
      exact mul_zero _
  have hinterval : (∫ t in Set.Icc 0 a, f t) = ∫ t in 0..a, f t := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ha]
  have hinside : (∫ t in 0..a, f t) =
      ∫ t in 0..a, (a - t) * Real.sin (u * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le ha] at ht
    dsimp [f]
    rw [show positivePart (a - t) = a - t by
      simp [positivePart, max_eq_left (sub_nonneg.mpr ht.2)]]
    ring
  let F : ℝ → ℝ := fun t =>
    (t - a) * Real.cos (u * t) / u - Real.sin (u * t) / u ^ 2
  have hlinear (t : ℝ) : HasDerivAt (fun s : ℝ => u * s) u t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul u
  have hderiv (t : ℝ) : HasDerivAt F ((a - t) * Real.sin (u * t)) t := by
    have hcos := (Real.hasDerivAt_cos (u * t)).comp t (hlinear t)
    have hsin := (Real.hasDerivAt_sin (u * t)).comp t (hlinear t)
    dsimp [F]
    convert (((hasDerivAt_id t).sub (hasDerivAt_const t a)).mul hcos).div_const u |>.sub
      (hsin.div_const (u ^ 2)) using 1
    simp only [Pi.sub_apply, id_eq, Function.comp_apply]
    field_simp [hu.ne']
    ring
  have hpolyIntegrable : IntervalIntegrable
      (fun t : ℝ => (a - t) * Real.sin (u * t)) volume 0 a := by
    have hcontinuous : Continuous (fun t : ℝ => (a - t) * Real.sin (u * t)) := by
      fun_prop
    exact hcontinuous.intervalIntegrable 0 a
  have heval : (∫ t in 0..a, (a - t) * Real.sin (u * t)) = F a - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hpolyIntegrable
  calc
    (∫ t in Set.Ici (0 : ℝ), Real.sin (u * t) * positivePart (a - t)) =
        ∫ t in 0..a, (a - t) * Real.sin (u * t) := by
      rw [show (fun t => Real.sin (u * t) * positivePart (a - t)) = f by rfl,
        hrestrict, hinterval, hinside]
    _ = F a - F 0 := heval
    _ = a / u - Real.sin (u * a) / u ^ 2 := by
      dsimp [F]
      simp only [sub_self, zero_mul, mul_zero, Real.sin_zero, Real.cos_zero, zero_div,
        zero_sub, sub_zero]
      field_simp [hu.ne']
      ring

/-- Positive stop-loss transform of the centered two-point law on `{a,-b}`. -/
def twoPointPositiveStopLoss (a b t : ℝ) : ℝ :=
  b / (a + b) * positivePart (a - t)

/-- Negative stop-loss transform of the centered two-point law on `{a,-b}`. -/
def twoPointNegativeStopLoss (a b t : ℝ) : ℝ :=
  a / (a + b) * positivePart (b - t)

theorem twoPoint_stopLoss_energy_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Set.Ici (0 : ℝ),
      twoPointPositiveStopLoss a b t ^ 2 + twoPointNegativeStopLoss a b t ^ 2) =
        twoPointStopLossEnergy a b := by
  have hab : 0 < a + b := add_pos ha hb
  have hAIntegrable : IntegrableOn
      (fun t : ℝ => positivePart (a - t) * positivePart (a - t))
      (Set.Ici 0) volume := integrableOn_hardy_kernel (y := a) (z := a)
  have hBIntegrable : IntegrableOn
      (fun t : ℝ => positivePart (b - t) * positivePart (b - t))
      (Set.Ici 0) volume := integrableOn_hardy_kernel (y := b) (z := b)
  have hAIntegral :
      (∫ t in Set.Ici (0 : ℝ), positivePart (a - t) * positivePart (a - t)) =
        a ^ 3 / 3 := by
    have h := hardy_kernel_integral_eq_of_le ha.le (le_refl a)
    nlinarith
  have hBIntegral :
      (∫ t in Set.Ici (0 : ℝ), positivePart (b - t) * positivePart (b - t)) =
        b ^ 3 / 3 := by
    have h := hardy_kernel_integral_eq_of_le hb.le (le_refl b)
    nlinarith
  calc
    (∫ t in Set.Ici (0 : ℝ),
        twoPointPositiveStopLoss a b t ^ 2 + twoPointNegativeStopLoss a b t ^ 2) =
        ∫ t in Set.Ici (0 : ℝ),
          (b / (a + b)) ^ 2 *
              (positivePart (a - t) * positivePart (a - t)) +
            (a / (a + b)) ^ 2 *
              (positivePart (b - t) * positivePart (b - t)) := by
      apply integral_congr_ae
      filter_upwards with t
      unfold twoPointPositiveStopLoss twoPointNegativeStopLoss
      ring
    _ = (b / (a + b)) ^ 2 *
          (∫ t in Set.Ici (0 : ℝ), positivePart (a - t) * positivePart (a - t)) +
        (a / (a + b)) ^ 2 *
          (∫ t in Set.Ici (0 : ℝ), positivePart (b - t) * positivePart (b - t)) := by
      rw [integral_add (hAIntegrable.const_mul _) (hBIntegrable.const_mul _),
        integral_const_mul, integral_const_mul]
    _ = twoPointStopLossEnergy a b := by
      rw [hAIntegral, hBIntegral]
      unfold twoPointStopLossEnergy
      field_simp [hab.ne']

theorem twoPoint_weightedMoment_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Set.Ici (0 : ℝ),
      t * (twoPointPositiveStopLoss a b t + twoPointNegativeStopLoss a b t)) =
        twoPointWeightedMoment a b := by
  have hab : 0 < a + b := add_pos ha hb
  have hAIntegrable := integrableOn_weightedStopLossKernel a
  have hBIntegrable := integrableOn_weightedStopLossKernel b
  calc
    (∫ t in Set.Ici (0 : ℝ),
        t * (twoPointPositiveStopLoss a b t + twoPointNegativeStopLoss a b t)) =
        ∫ t in Set.Ici (0 : ℝ),
          (b / (a + b)) * weightedStopLossKernel a t +
            (a / (a + b)) * weightedStopLossKernel b t := by
      apply integral_congr_ae
      filter_upwards with t
      unfold twoPointPositiveStopLoss twoPointNegativeStopLoss weightedStopLossKernel
      ring
    _ = (b / (a + b)) *
          (∫ t in Set.Ici (0 : ℝ), weightedStopLossKernel a t) +
        (a / (a + b)) *
          (∫ t in Set.Ici (0 : ℝ), weightedStopLossKernel b t) := by
      rw [integral_add (hAIntegrable.const_mul _) (hBIntegrable.const_mul _),
        integral_const_mul, integral_const_mul]
    _ = twoPointWeightedMoment a b := by
      rw [weightedStopLossKernel_integral, weightedStopLossKernel_integral]
      simp only [positivePart, max_eq_left ha.le, max_eq_left hb.le]
      unfold twoPointWeightedMoment
      field_simp [hab.ne']

theorem twoPoint_sineMoment_integral {u a b : ℝ}
    (hu : 0 < u) (ha : 0 < a) (hb : 0 < b) :
    (1 / u) * (∫ t in Set.Ici (0 : ℝ),
      Real.sin (u * t) *
        (twoPointPositiveStopLoss a b t - twoPointNegativeStopLoss a b t)) =
          twoPointSineMoment u a b := by
  have hab : 0 < a + b := add_pos ha hb
  have hAIntegrable := integrableOn_sin_mul_positivePart u a
  have hBIntegrable := integrableOn_sin_mul_positivePart u b
  have hAIntegral := sin_mul_positivePart_integral hu ha.le
  have hBIntegral := sin_mul_positivePart_integral hu hb.le
  calc
    (1 / u) * (∫ t in Set.Ici (0 : ℝ),
        Real.sin (u * t) *
          (twoPointPositiveStopLoss a b t - twoPointNegativeStopLoss a b t)) =
        (1 / u) * (∫ t in Set.Ici (0 : ℝ),
          (b / (a + b)) * (Real.sin (u * t) * positivePart (a - t)) -
            (a / (a + b)) * (Real.sin (u * t) * positivePart (b - t))) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      unfold twoPointPositiveStopLoss twoPointNegativeStopLoss
      ring
    _ = (1 / u) *
        ((b / (a + b)) *
            (∫ t in Set.Ici (0 : ℝ), Real.sin (u * t) * positivePart (a - t)) -
          (a / (a + b)) *
            (∫ t in Set.Ici (0 : ℝ), Real.sin (u * t) * positivePart (b - t))) := by
      rw [integral_sub (hAIntegrable.const_mul _) (hBIntegrable.const_mul _),
        integral_const_mul, integral_const_mul]
    _ = twoPointSineMoment u a b := by
      rw [hAIntegral, hBIntegral]
      unfold twoPointSineMoment
      field_simp [hu.ne', hab.ne']
      ring

/-- The mixture-weighted two-point energy, written after cancellation of the
factor `a+b`.  The coordinates are `a=X₊` and `b=Y₋`. -/
def mixtureStopLossEnergy (r₀ : ℝ) (p : ℝ × ℝ) : ℝ :=
  positivePart p.1 ^ 2 * negativePart p.2 ^ 2 / (3 * r₀)

/-- The mixture-weighted radius `J_{a,b}` after cancellation. -/
def mixtureWeightedMoment (r₀ : ℝ) (p : ℝ × ℝ) : ℝ :=
  positivePart p.1 * negativePart p.2 *
    (positivePart p.1 ^ 2 + negativePart p.2 ^ 2) / (6 * r₀)

/-- The mixture-weighted sine coordinate after cancellation. -/
def mixtureSineMoment (r₀ u : ℝ) (p : ℝ × ℝ) : ℝ :=
  (positivePart p.1 * Real.sin (u * negativePart p.2) -
      negativePart p.2 * Real.sin (u * positivePart p.1)) /
    (r₀ * u ^ 3)

theorem mixture_component_moment_sine_circle
    {r₀ u : ℝ} (hr₀ : 0 < r₀) (hu : 0 < u) (p : ℝ × ℝ) :
    mixtureStopLossEnergy r₀ p ^ 2 + mixtureSineMoment r₀ u p ^ 2 ≤
      mixtureWeightedMoment r₀ p ^ 2 := by
  let a := positivePart p.1
  let b := negativePart p.2
  have ha0 : 0 ≤ a := positivePart_nonneg p.1
  have hb0 : 0 ≤ b := negativePart_nonneg p.2
  by_cases ha : 0 < a
  · by_cases hb : 0 < b
    · let w := (a + b) / r₀
      have hbase := twoPoint_moment_sine_circle hu ha hb
      have henergy : mixtureStopLossEnergy r₀ p =
          w * twoPointStopLossEnergy a b := by
        change a ^ 2 * b ^ 2 / (3 * r₀) =
          w * (a ^ 2 * b ^ 2 / (3 * (a + b)))
        dsimp [w]
        field_simp [hr₀.ne', (add_pos ha hb).ne']
      have hsine : mixtureSineMoment r₀ u p =
          w * twoPointSineMoment u a b := by
        change (a * Real.sin (u * b) - b * Real.sin (u * a)) / (r₀ * u ^ 3) =
          w * ((a * Real.sin (u * b) - b * Real.sin (u * a)) /
            ((a + b) * u ^ 3))
        dsimp [w]
        field_simp [hr₀.ne', hu.ne', (add_pos ha hb).ne']
      have hmoment : mixtureWeightedMoment r₀ p =
          w * twoPointWeightedMoment a b := by
        change a * b * (a ^ 2 + b ^ 2) / (6 * r₀) =
          w * (a * b * (a ^ 2 + b ^ 2) / (6 * (a + b)))
        dsimp [w]
        field_simp [hr₀.ne', (add_pos ha hb).ne']
      rw [henergy, hsine, hmoment]
      calc
        (w * twoPointStopLossEnergy a b) ^ 2 +
            (w * twoPointSineMoment u a b) ^ 2 =
            w ^ 2 *
              (twoPointStopLossEnergy a b ^ 2 + twoPointSineMoment u a b ^ 2) := by
          ring
        _ ≤ w ^ 2 * twoPointWeightedMoment a b ^ 2 :=
          mul_le_mul_of_nonneg_left hbase (sq_nonneg w)
        _ = (w * twoPointWeightedMoment a b) ^ 2 := by ring
    · have hbzero : b = 0 := le_antisymm (le_of_not_gt hb) hb0
      simp [mixtureStopLossEnergy, mixtureSineMoment, mixtureWeightedMoment, b,
        hbzero]
  · have hazero : a = 0 := le_antisymm (le_of_not_gt ha) ha0
    simp [mixtureStopLossEnergy, mixtureSineMoment, mixtureWeightedMoment, a,
      hazero]

theorem integrable_mixtureStopLossEnergy
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    Integrable (mixtureStopLossEnergy r₀) (mu.prod mu) := by
  have hprod := (integrable_positivePart_sq hX).mul_prod (integrable_negativePart_sq hX)
  have hscaled := hprod.const_mul (1 / (3 * r₀))
  apply hscaled.congr
  filter_upwards with p
  unfold mixtureStopLossEnergy
  field_simp [hr₀.ne']

theorem mixtureStopLossEnergy_integral
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {r₀ : ℝ} (hr₀ : 0 < r₀) :
    (∫ p : ℝ × ℝ, mixtureStopLossEnergy r₀ p ∂mu.prod mu) =
      positiveMoment mu 2 * negativeMoment mu 2 / (3 * r₀) := by
  have hprod :
      (∫ p : ℝ × ℝ, positivePart p.1 ^ 2 * negativePart p.2 ^ 2 ∂mu.prod mu) =
        (∫ x, positivePart x ^ 2 ∂mu) * ∫ x, negativePart x ^ 2 ∂mu := by
    simpa only using integral_prod_mul (μ := mu) (ν := mu)
      (fun x : ℝ => positivePart x ^ 2) (fun x : ℝ => negativePart x ^ 2)
  calc
    (∫ p : ℝ × ℝ, mixtureStopLossEnergy r₀ p ∂mu.prod mu) =
        (1 / (3 * r₀)) *
          ∫ p : ℝ × ℝ, positivePart p.1 ^ 2 * negativePart p.2 ^ 2 ∂mu.prod mu := by
      unfold mixtureStopLossEnergy
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with p
      field_simp [hr₀.ne']
    _ = positiveMoment mu 2 * negativeMoment mu 2 / (3 * r₀) := by
      rw [hprod]
      unfold positiveMoment negativeMoment
      ring

theorem integrable_mixtureWeightedMoment
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    Integrable (mixtureWeightedMoment r₀) (mu.prod mu) := by
  have hpositive1 := integrable_positivePart hX
  have hnegative1 := integrable_negativePart hX
  have hpositive3 := integrable_positivePart_cube hX
  have hnegative3 := integrable_negativePart_cube hX
  have htermOne : Integrable
      (fun p : ℝ × ℝ => positivePart p.1 ^ 3 * negativePart p.2) (mu.prod mu) :=
    hpositive3.mul_prod hnegative1
  have htermTwo : Integrable
      (fun p : ℝ × ℝ => positivePart p.1 * negativePart p.2 ^ 3) (mu.prod mu) :=
    hpositive1.mul_prod hnegative3
  have hscaled := (htermOne.add htermTwo).const_mul (1 / (6 * r₀))
  apply hscaled.congr
  filter_upwards with p
  unfold mixtureWeightedMoment
  simp only [Pi.add_apply]
  field_simp [hr₀.ne']

theorem mixtureWeightedMoment_integral
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    (∫ p : ℝ × ℝ,
      mixtureWeightedMoment (positiveMoment mu 1) p ∂mu.prod mu) =
        thirdAbsoluteMoment mu / 6 := by
  have hr₀ := positive_firstMoment_pos mu hX hmean hsecond
  have hfirst := centered_first_part_moments_eq mu hX hmean
  have hprodOne :
      (∫ p : ℝ × ℝ, positivePart p.1 ^ 3 * negativePart p.2 ∂mu.prod mu) =
        positiveMoment mu 3 * negativeMoment mu 1 := by
    simpa only [positiveMoment, negativeMoment, pow_one] using
      integral_prod_mul (μ := mu) (ν := mu)
        (fun x : ℝ => positivePart x ^ 3) negativePart
  have hprodTwo :
      (∫ p : ℝ × ℝ, positivePart p.1 * negativePart p.2 ^ 3 ∂mu.prod mu) =
        positiveMoment mu 1 * negativeMoment mu 3 := by
    simpa only [positiveMoment, negativeMoment, pow_one] using
      integral_prod_mul (μ := mu) (ν := mu)
        positivePart (fun x : ℝ => negativePart x ^ 3)
  calc
    (∫ p : ℝ × ℝ,
        mixtureWeightedMoment (positiveMoment mu 1) p ∂mu.prod mu) =
        (1 / (6 * positiveMoment mu 1)) *
          ((∫ p : ℝ × ℝ, positivePart p.1 ^ 3 * negativePart p.2 ∂mu.prod mu) +
            ∫ p : ℝ × ℝ, positivePart p.1 * negativePart p.2 ^ 3 ∂mu.prod mu) := by
      rw [← integral_add
        ((integrable_positivePart_cube hX).mul_prod (integrable_negativePart hX))
        ((integrable_positivePart hX).mul_prod (integrable_negativePart_cube hX)),
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with p
      unfold mixtureWeightedMoment
      field_simp [hr₀.ne']
    _ = thirdAbsoluteMoment mu / 6 := by
      rw [hprodOne, hprodTwo, ← hfirst]
      rw [← third_absolute_part_moments_add mu hX]
      field_simp [hr₀.ne']

theorem integrable_sin_positivePart
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (u : ℝ) :
    Integrable (fun x => Real.sin (u * positivePart x)) mu := by
  have hcontinuous : Continuous (fun x : ℝ => Real.sin (u * positivePart x)) := by
    unfold positivePart
    fun_prop
  apply (integrable_const (μ := mu) (1 : ℝ)).mono' hcontinuous.aestronglyMeasurable
  exact ae_of_all mu fun x => by
    simpa only [Real.norm_eq_abs, norm_one] using
      Real.abs_sin_le_one (u * positivePart x)

theorem integrable_sin_negativePart
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (u : ℝ) :
    Integrable (fun x => Real.sin (u * negativePart x)) mu := by
  have hcontinuous : Continuous (fun x : ℝ => Real.sin (u * negativePart x)) := by
    unfold negativePart
    fun_prop
  apply (integrable_const (μ := mu) (1 : ℝ)).mono' hcontinuous.aestronglyMeasurable
  exact ae_of_all mu fun x => by
    simpa only [Real.norm_eq_abs, norm_one] using
      Real.abs_sin_le_one (u * negativePart x)

theorem integrable_mixtureSineMoment
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    {r₀ u : ℝ} (hr₀ : 0 < r₀) (hu : 0 < u) :
    Integrable (mixtureSineMoment r₀ u) (mu.prod mu) := by
  have htermOne : Integrable
      (fun p : ℝ × ℝ =>
        positivePart p.1 * Real.sin (u * negativePart p.2)) (mu.prod mu) :=
    (integrable_positivePart hX).mul_prod (integrable_sin_negativePart mu u)
  have htermTwo : Integrable
      (fun p : ℝ × ℝ =>
        Real.sin (u * positivePart p.1) * negativePart p.2) (mu.prod mu) :=
    (integrable_sin_positivePart mu u).mul_prod (integrable_negativePart hX)
  have hscaled := (htermOne.sub htermTwo).const_mul (1 / (r₀ * u ^ 3))
  apply hscaled.congr
  filter_upwards with p
  unfold mixtureSineMoment
  simp only [Pi.sub_apply]
  field_simp [hr₀.ne', hu.ne']

theorem mixtureSineMoment_integral
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {u : ℝ} (hu : 0 < u) :
    (∫ p : ℝ × ℝ,
      mixtureSineMoment (positiveMoment mu 1) u p ∂mu.prod mu) =
        ((∫ x, Real.sin (u * negativePart x) ∂mu) -
          ∫ x, Real.sin (u * positivePart x) ∂mu) / u ^ 3 := by
  have hr₀ := positive_firstMoment_pos mu hX hmean hsecond
  have hfirst := centered_first_part_moments_eq mu hX hmean
  have hprodOne :
      (∫ p : ℝ × ℝ,
        positivePart p.1 * Real.sin (u * negativePart p.2) ∂mu.prod mu) =
          positiveMoment mu 1 * ∫ x, Real.sin (u * negativePart x) ∂mu := by
    simpa only [positiveMoment, pow_one] using
      integral_prod_mul (μ := mu) (ν := mu)
        positivePart (fun x : ℝ => Real.sin (u * negativePart x))
  have hprodTwo :
      (∫ p : ℝ × ℝ,
        Real.sin (u * positivePart p.1) * negativePart p.2 ∂mu.prod mu) =
          (∫ x, Real.sin (u * positivePart x) ∂mu) * negativeMoment mu 1 := by
    simpa only [negativeMoment, pow_one] using
      integral_prod_mul (μ := mu) (ν := mu)
        (fun x : ℝ => Real.sin (u * positivePart x)) negativePart
  have htermOne : Integrable
      (fun p : ℝ × ℝ =>
        positivePart p.1 * Real.sin (u * negativePart p.2)) (mu.prod mu) :=
    (integrable_positivePart hX).mul_prod (integrable_sin_negativePart mu u)
  have htermTwo : Integrable
      (fun p : ℝ × ℝ =>
        Real.sin (u * positivePart p.1) * negativePart p.2) (mu.prod mu) :=
    (integrable_sin_positivePart mu u).mul_prod (integrable_negativePart hX)
  calc
    (∫ p : ℝ × ℝ,
        mixtureSineMoment (positiveMoment mu 1) u p ∂mu.prod mu) =
        (1 / (positiveMoment mu 1 * u ^ 3)) *
          ((∫ p : ℝ × ℝ,
              positivePart p.1 * Real.sin (u * negativePart p.2) ∂mu.prod mu) -
            ∫ p : ℝ × ℝ,
              Real.sin (u * positivePart p.1) * negativePart p.2 ∂mu.prod mu) := by
      rw [← integral_sub htermOne htermTwo, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with p
      unfold mixtureSineMoment
      field_simp [hr₀.ne', hu.ne']
    _ = ((∫ x, Real.sin (u * negativePart x) ∂mu) -
          ∫ x, Real.sin (u * positivePart x) ∂mu) / u ^ 3 := by
      rw [hprodOne, hprodTwo, ← hfirst]
      field_simp [hr₀.ne', hu.ne']

theorem sine_integral_eq_part_integrals
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (u : ℝ) :
    (∫ x, Real.sin (u * x) ∂mu) =
      (∫ x, Real.sin (u * positivePart x) ∂mu) -
        ∫ x, Real.sin (u * negativePart x) ∂mu := by
  have hpositive := integrable_sin_positivePart mu u
  have hnegative := integrable_sin_negativePart mu u
  rw [← integral_sub hpositive hnegative]
  apply integral_congr_ae
  exact ae_of_all mu fun x => by
    by_cases hx : 0 ≤ x
    · simp [positivePart, negativePart, max_eq_left hx,
        max_eq_right (neg_nonpos.mpr hx)]
    · have hx' : x ≤ 0 := le_of_not_ge hx
      simp [positivePart, negativePart, max_eq_right hx',
        max_eq_left (neg_nonneg.mpr hx'), Real.sin_neg]

theorem mixtureSineMoment_integral_eq_neg_sine
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {u : ℝ} (hu : 0 < u) :
    (∫ p : ℝ × ℝ,
      mixtureSineMoment (positiveMoment mu 1) u p ∂mu.prod mu) =
        -(∫ x, Real.sin (u * x) ∂mu) / u ^ 3 := by
  rw [mixtureSineMoment_integral mu hX hmean hsecond hu,
    sine_integral_eq_part_integrals mu u]
  ring

/-- `E₀ = ∫₀∞ (A(t)²+B(t)²) dt` in the source proof. -/
def stopLossEnergy (mu : Measure ℝ) : ℝ :=
  ∫ t in Set.Ici (0 : ℝ), positiveStopLoss mu t ^ 2 + negativeStopLoss mu t ^ 2

theorem stopLossEnergy_nonneg (mu : Measure ℝ) : 0 ≤ stopLossEnergy mu := by
  unfold stopLossEnergy
  exact integral_nonneg fun t => add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem mixtureWeightedMoment_nonneg {r₀ : ℝ} (hr₀ : 0 < r₀) (p : ℝ × ℝ) :
    0 ≤ mixtureWeightedMoment r₀ p := by
  unfold mixtureWeightedMoment
  apply div_nonneg
  · exact mul_nonneg
      (mul_nonneg (positivePart_nonneg p.1) (negativePart_nonneg p.2))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  · positivity

theorem stopLossEnergy_le_mixture_integral
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    stopLossEnergy mu ≤
      ∫ p : ℝ × ℝ,
        mixtureStopLossEnergy (positiveMoment mu 1) p ∂mu.prod mu := by
  have hr₀ := positive_firstMoment_pos mu hX hmean hsecond
  have hhardy := combined_stopLoss_sq_integral_le_firstMoment mu hX hmean hsecond
  change 3 * stopLossEnergy mu ≤ positiveMoment mu 1 at hhardy
  have hcovariance := first_part_moment_sq_le_second_product mu hX hmean hsecond
  have hmul :
      (3 * stopLossEnergy mu) * positiveMoment mu 1 ≤
        positiveMoment mu 1 ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_right hhardy hr₀.le
  have hnumerator :
      stopLossEnergy mu * (3 * positiveMoment mu 1) ≤
        positiveMoment mu 2 * negativeMoment mu 2 := by
    calc
      stopLossEnergy mu * (3 * positiveMoment mu 1) =
          (3 * stopLossEnergy mu) * positiveMoment mu 1 := by ring
      _ ≤ positiveMoment mu 1 ^ 2 := hmul
      _ ≤ positiveMoment mu 2 * negativeMoment mu 2 := hcovariance
  rw [mixtureStopLossEnergy_integral mu hr₀]
  exact (le_div_iff₀ (mul_pos (by norm_num) hr₀)).2 hnumerator

/-- Route B equation (2.6), before replacing the three aggregate coordinates
by `r`, `rho`, and the sine remainder. -/
theorem stopLoss_sine_functional_circle
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {u : ℝ} (hu : 0 < u) :
    stopLossEnergy mu ^ 2 +
        (∫ p : ℝ × ℝ,
          mixtureSineMoment (positiveMoment mu 1) u p ∂mu.prod mu) ^ 2 ≤
      (thirdAbsoluteMoment mu / 6) ^ 2 := by
  have hr₀ := positive_firstMoment_pos mu hX hmean hsecond
  have haggregate := integral_energy_sine_circle
    (mu.prod mu)
    (mixtureStopLossEnergy (positiveMoment mu 1))
    (mixtureSineMoment (positiveMoment mu 1) u)
    (mixtureWeightedMoment (positiveMoment mu 1))
    (stopLossEnergy mu)
    (integrable_mixtureStopLossEnergy mu hX hr₀)
    (integrable_mixtureSineMoment mu hX hr₀ hu)
    (integrable_mixtureWeightedMoment mu hX hr₀)
    (ae_of_all (mu.prod mu) (mixtureWeightedMoment_nonneg hr₀))
    (ae_of_all (mu.prod mu) (mixture_component_moment_sine_circle hr₀ hu))
    (stopLossEnergy_nonneg mu)
    (stopLossEnergy_le_mixture_integral mu hX hmean hsecond)
  rw [mixtureWeightedMoment_integral mu hX hmean hsecond] at haggregate
  exact haggregate

theorem stopLossEnergy_eq_ratio_coordinate
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    stopLossEnergy mu =
      (thirdAbsoluteMoment mu / 6) * (symmetrizationRatio mu - 1) := by
  have hrho := thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPositive : 0 < thirdAbsoluteMoment mu := lt_of_lt_of_le zero_lt_one hrho
  have hidentity := symmetrizedThirdAbsoluteMoment_stopLoss_identity mu hX hmean
  unfold stopLossEnergy symmetrizationRatio
  rw [hidentity]
  field_simp [hrhoPositive.ne']
  ring

/-- The expectation in Route B equation (2.5). -/
def sineRemainderExpectation (mu : Measure ℝ) (u : ℝ) : ℝ :=
  ∫ x, Real.sin (u * x) - u * x ∂mu

theorem integrable_sin_linear
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (u : ℝ) :
    Integrable (fun x : ℝ => Real.sin (u * x)) mu := by
  have hcontinuous : Continuous (fun x : ℝ => Real.sin (u * x)) := by fun_prop
  apply (integrable_const (μ := mu) (1 : ℝ)).mono' hcontinuous.aestronglyMeasurable
  exact ae_of_all mu fun x => by
    simpa only [Real.norm_eq_abs, norm_one] using Real.abs_sin_le_one (u * x)

theorem sineRemainderExpectation_eq_sine_integral
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0) (u : ℝ) :
    sineRemainderExpectation mu u = ∫ x, Real.sin (u * x) ∂mu := by
  have hId : Integrable (id : ℝ → ℝ) mu := hX.integrable (by norm_num)
  have hlinear : Integrable (fun x : ℝ => u * x) mu := by
    simpa only [id_eq] using hId.const_mul u
  unfold sineRemainderExpectation
  rw [integral_sub (integrable_sin_linear mu u) hlinear, integral_const_mul, hmean]
  ring

theorem sineRemainderExpectation_eq_neg_cube_mul_mixture
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {u : ℝ} (hu : 0 < u) :
    sineRemainderExpectation mu u =
      -u ^ 3 *
        ∫ p : ℝ × ℝ,
          mixtureSineMoment (positiveMoment mu 1) u p ∂mu.prod mu := by
  rw [sineRemainderExpectation_eq_sine_integral mu hX hmean]
  rw [mixtureSineMoment_integral_eq_neg_sine mu hX hmean hsecond hu]
  field_simp [hu.ne']

theorem sine_remainder_circle_pos
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {u : ℝ} (hu : 0 < u) :
    |sineRemainderExpectation mu u| ≤
      thirdAbsoluteMoment mu * u ^ 3 / 6 *
        Real.sqrt (1 - (symmetrizationRatio mu - 1) ^ 2) := by
  let H := ∫ p : ℝ × ℝ,
    mixtureSineMoment (positiveMoment mu 1) u p ∂mu.prod mu
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  have hrho := thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoNonneg : 0 ≤ rho := by dsimp [rho]; linarith
  have hrLower := symmetrizationRatio_lower mu hX hmean hsecond
  have hrUpper := symmetrizationRatio_le_two mu hX hmean hsecond
  have hradicand : 0 ≤ 1 - (r - 1) ^ 2 := by
    dsimp [r] at hrLower hrUpper ⊢
    nlinarith
  have hfunctional := stopLoss_sine_functional_circle mu hX hmean hsecond hu
  change stopLossEnergy mu ^ 2 + H ^ 2 ≤ (rho / 6) ^ 2 at hfunctional
  have henergy := stopLossEnergy_eq_ratio_coordinate mu hX hmean hsecond
  change stopLossEnergy mu = (rho / 6) * (r - 1) at henergy
  have hHsq : H ^ 2 ≤ (rho / 6) ^ 2 * (1 - (r - 1) ^ 2) := by
    rw [henergy] at hfunctional
    nlinarith
  have hHabs : |H| ≤
      (rho / 6) * Real.sqrt (1 - (r - 1) ^ 2) := by
    apply (sq_le_sq₀ (abs_nonneg H)
      (mul_nonneg (div_nonneg hrhoNonneg (by norm_num)) (Real.sqrt_nonneg _))).mp
    rw [sq_abs, mul_pow, Real.sq_sqrt hradicand]
    exact hHsq
  have hremainder := sineRemainderExpectation_eq_neg_cube_mul_mixture
    mu hX hmean hsecond hu
  change sineRemainderExpectation mu u = -u ^ 3 * H at hremainder
  rw [hremainder, abs_mul, abs_neg, abs_of_nonneg (pow_nonneg hu.le 3)]
  have hscaled := mul_le_mul_of_nonneg_left hHabs (pow_nonneg hu.le 3)
  dsimp [rho, r] at hscaled ⊢
  calc
    u ^ 3 * |H| ≤
        u ^ 3 *
          (thirdAbsoluteMoment mu / 6 *
            Real.sqrt (1 - (symmetrizationRatio mu - 1) ^ 2)) := hscaled
    _ = thirdAbsoluteMoment mu * u ^ 3 / 6 *
          Real.sqrt (1 - (symmetrizationRatio mu - 1) ^ 2) := by ring

/-- Route B equation (2.5): the sine remainder is controlled at every
frequency by the same symmetrization parameter `r`. -/
theorem sine_remainder_circle
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (u : ℝ) :
    |sineRemainderExpectation mu u| ≤
      thirdAbsoluteMoment mu * |u| ^ 3 / 6 *
        Real.sqrt (1 - (symmetrizationRatio mu - 1) ^ 2) := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · have hpos := sine_remainder_circle_pos mu hX hmean hsecond (neg_pos.mpr hu)
    have hodd : sineRemainderExpectation mu (-u) = -sineRemainderExpectation mu u := by
      unfold sineRemainderExpectation
      rw [← integral_neg]
      apply integral_congr_ae
      exact ae_of_all mu fun x => by
        change Real.sin (-u * x) - (-u) * x = -(Real.sin (u * x) - u * x)
        rw [show -u * x = -(u * x) by ring, Real.sin_neg]
        ring
    rw [hodd] at hpos
    simpa [abs_of_neg hu] using hpos
  · simp [sineRemainderExpectation]
  · simpa [abs_of_pos hu] using sine_remainder_circle_pos mu hX hmean hsecond hu

end

end BerryEsseen
