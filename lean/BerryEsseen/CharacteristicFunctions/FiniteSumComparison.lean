import BerryEsseen.Moments.FirstAbsoluteMoment
import BerryEsseen.CharacteristicFunctions.TwoPointComparison
import BerryEsseen.CharacteristicFunctions.ComponentBounds
import BerryEsseen.Analysis.TrigonometricBounds

/-!
# Characteristic Functions / Finite Sum Comparison
-/

namespace BerryEsseen

open MeasureTheory DyadicInterval

noncomputable section

theorem dUpper_contains_radialDefect
    {rho z : DyadicInterval}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hrhoLo : 0 < rho.lo) :
    (dUpper rho z).Contains
      (1 - ∫ x : ℝ, |x| ∂mu) := by
  have hconstraints := radialDefect_constraints mu hX hmean hsecond
  exact dUpper_sound hrho hz hrhoLo
    hconstraints.1 hconstraints.2.1 hconstraints.2.2

lemma charFun_real_mem_unit
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (u : ℝ) :
    -1 ≤ (charFun mu u).re ∧ (charFun mu u).re ≤ 1 := by
  have hnorm : ‖charFun mu u‖ ≤ 1 := norm_charFun_le_one u
  have habs : |(charFun mu u).re| ≤ 1 :=
    (Complex.abs_re_le_norm (charFun mu u)).trans hnorm
  exact (abs_le).1 habs

theorem realInterval_contains_charFun
    {rho z uBox sinU cosU : DyadicInterval}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hrhoLo : 0 < rho.lo)
    {uR : ℝ} (hu0 : 0 ≤ uR) (hu : uBox.Contains uR)
    (hsin : sinU.Contains (Real.sin uR))
    (hcos : cosU.Contains (Real.cos uR)) :
    (realInterval rho (dUpper rho z) uBox sinU cosU).Contains
      (charFun mu uR).re := by
  let rhoR := thirdAbsoluteMoment mu
  let dR := 1 - ∫ x : ℝ, |x| ∂mu
  have hd : (dUpper rho z).Contains dR := by
    simpa only [dR] using
      dUpper_contains_radialDefect mu hX hmean hsecond hrho hz hrhoLo
  have htaylor : |(charFun mu uR).re - Real.cos uR| ≤
      dR * (|uR * Real.sin uR| + uR ^ 2) := by
    simpa only [dR] using
      charFun_real_radial_bound mu hX hsecond uR
  have hquadratic : 1 - uR ^ 2 / 2 ≤ (charFun mu uR).re := by
    have h := charFun_real_remainder_nonneg mu hX hsecond uR
    linarith
  have hrhoOne : 1 ≤ rhoR := by
    simpa only [rhoR] using thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrho0 : 0 ≤ rhoR := le_trans (by norm_num) hrhoOne
  have hfactor0 : 0 ≤ rhoR * uR ^ 3 :=
    mul_nonneg hrho0 (pow_nonneg hu0 3)
  have hrem := charFun_real_remainder_le_certificate
    mu hX hsecond routeB_exactMinorantCertificate uR
  rw [abs_of_nonneg hu0] at hrem
  have hkappa :
      (rhoR * uR ^ 3) * routeBKappa ≤
        (rhoR * uR ^ 3) * routeBKappaUpper :=
    mul_le_mul_of_nonneg_left routeBKappa_lt_upper.le hfactor0
  have hcubic : (charFun mu uR).re ≤
      1 - uR ^ 2 / 2 + routeBKappaUpper * rhoR * uR ^ 3 := by
    change (charFun mu uR).re - (1 - uR ^ 2 / 2) ≤
      (rhoR * uR ^ 3) * routeBKappa at hrem
    nlinarith
  exact realInterval_sound hrho hd hu hsin hcos
    (charFun_real_mem_unit mu uR) htaylor hquadratic hcubic

theorem charFun_im_sine_circle_reparam
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {uR : ℝ} (hu0 : 0 ≤ uR) :
    |(charFun mu uR).im| ≤
      uR ^ 3 * Real.sqrt (
        thirdAbsoluteMoment mu ^ 2 -
          (thirdAbsoluteMoment mu *
            (symmetrizationRatio mu - 1)) ^ 2) / 6 := by
  let rhoR := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let zR := rhoR * (rR - 1)
  have hrhoOne : 1 ≤ rhoR := by
    simpa only [rhoR] using thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrho0 : 0 ≤ rhoR := le_trans (by norm_num) hrhoOne
  have hrLower : 1 ≤ rR := by
    simpa only [rR] using symmetrizationRatio_lower mu hX hmean hsecond
  have hrUpper : rR ≤ 2 := by
    simpa only [rR] using symmetrizationRatio_le_two mu hX hmean hsecond
  have hq : 0 ≤ 1 - (rR - 1) ^ 2 := by nlinarith
  have hsqrt :
      Real.sqrt (rhoR ^ 2 - zR ^ 2) =
        rhoR * Real.sqrt (1 - (rR - 1) ^ 2) := by
    rw [show rhoR ^ 2 - zR ^ 2 =
        rhoR ^ 2 * (1 - (rR - 1) ^ 2) by
      dsimp only [zR]
      ring,
      Real.sqrt_mul (sq_nonneg rhoR), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hrho0]
  have hsine := sine_remainder_circle mu hX hmean hsecond uR
  have him : (charFun mu uR).im = sineRemainderExpectation mu uR := by
    rw [charFun_im_eq_integral_sin,
      sineRemainderExpectation_eq_sine_integral mu hX hmean]
  rw [← him, abs_of_nonneg hu0] at hsine
  change |(charFun mu uR).im| ≤
    rhoR * uR ^ 3 / 6 * Real.sqrt (1 - (rR - 1) ^ 2) at hsine
  change |(charFun mu uR).im| ≤
    uR ^ 3 * Real.sqrt (rhoR ^ 2 - zR ^ 2) / 6
  calc
    |(charFun mu uR).im| ≤
        rhoR * uR ^ 3 / 6 * Real.sqrt (1 - (rR - 1) ^ 2) := hsine
    _ = uR ^ 3 * Real.sqrt (rhoR ^ 2 - zR ^ 2) / 6 := by
      rw [hsqrt]
      ring

theorem imagInterval_contains_charFun
    {rho z uBox sinU cosU : DyadicInterval}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hrhoLo : 0 < rho.lo)
    {uR : ℝ} (hu0 : 0 ≤ uR) (hu : uBox.Contains uR)
    (hsin : sinU.Contains (Real.sin uR))
    (hcos : cosU.Contains (Real.cos uR)) :
    (imagInterval rho z (dUpper rho z) uBox sinU cosU).Contains
      |(charFun mu uR).im| := by
  let rhoR := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let zR := rhoR * (rR - 1)
  let dR := 1 - ∫ x : ℝ, |x| ∂mu
  have hconstraints := radialDefect_constraints mu hX hmean hsecond
  have hd0 : 0 ≤ dR := by simpa only [dR] using hconstraints.1
  have hd : (dUpper rho z).Contains dR := by
    simpa only [dR] using
      dUpper_contains_radialDefect mu hX hmean hsecond hrho hz hrhoLo
  have hdLo : 0 ≤ (dUpper rho z).lo := by
    simp [dUpper, upperHull]
  have hrLower : 1 ≤ rR := by
    simpa only [rR] using symmetrizationRatio_lower mu hX hmean hsecond
  have hrUpper : rR ≤ 2 := by
    simpa only [rR] using symmetrizationRatio_le_two mu hX hmean hsecond
  have hq : 0 ≤ 1 - (rR - 1) ^ 2 := by nlinarith
  have hrad : 0 ≤ rhoR ^ 2 - zR ^ 2 := by
    calc
      0 ≤ rhoR ^ 2 * (1 - (rR - 1) ^ 2) :=
        mul_nonneg (sq_nonneg rhoR) hq
      _ = rhoR ^ 2 - zR ^ 2 := by
        dsimp only [zR]
        ring
  have htaylor : |(charFun mu uR).im| ≤
      Real.sqrt (2 * dR) * |Real.sin uR - uR * Real.cos uR| +
        dR * uR ^ 2 := by
    have h := charFun_imag_radial_bound mu hX hmean hsecond uR
    dsimp only [dR]
    convert h using 1 <;> ring
  have hcircle : |(charFun mu uR).im| ≤
      uR ^ 3 * Real.sqrt (rhoR ^ 2 - zR ^ 2) / 6 := by
    simpa only [rhoR, rR, zR] using
      charFun_im_sine_circle_reparam mu hX hmean hsecond hu0
  exact imagInterval_sound hrho hz hd hu hsin hcos hdLo hd0 hrad
    htaylor hcircle

def finiteRealRadius
    (d u sinU : DyadicInterval) : DyadicInterval :=
  DyadicInterval.mul d
    (DyadicInterval.add
      (absHull (DyadicInterval.mul u sinU))
      (DyadicInterval.sqr u))

theorem finiteRealRadius_sound
    {d u sinU : DyadicInterval} {dR uR : ℝ}
    (hd : d.Contains dR) (hu : u.Contains uR)
    (hsin : sinU.Contains (Real.sin uR)) :
    (finiteRealRadius d u sinU).Contains
      (dR * (|uR * Real.sin uR| + uR ^ 2)) := by
  have huSin : (DyadicInterval.mul u sinU).Contains
      (uR * Real.sin uR) := hu.mul hsin
  have habs := absHull_sound huSin
  have hu2 : (DyadicInterval.sqr u).Contains (uR ^ 2) :=
    hu.sqr hu.ordered
  simpa only [finiteRealRadius] using hd.mul (habs.add hu2)

theorem rectangularEnvelope_contains_charFun
    {rho z uBox sinU cosU : DyadicInterval}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hrhoLo : 0 < rho.lo)
    {uR : ℝ} (hu0 : 0 ≤ uR) (hu : uBox.Contains uR)
    (hsin : sinU.Contains (Real.sin uR))
    (hcos : cosU.Contains (Real.cos uR)) :
    let d := dUpper rho z
    let real := realInterval rho d uBox sinU cosU
    let imag := imagInterval rho z d uBox sinU cosU
    (rectangularEnvelope real imag).Contains ‖charFun mu uR‖ := by
  let d := dUpper rho z
  let real := realInterval rho d uBox sinU cosU
  let imag := imagInterval rho z d uBox sinU cosU
  have hreal : real.Contains (charFun mu uR).re := by
    simpa only [real, d] using
      realInterval_contains_charFun mu hX hmean hsecond
        hrho hz hrhoLo hu0 hu hsin hcos
  have himag : imag.Contains |(charFun mu uR).im| := by
    simpa only [imag, d] using
      imagInterval_contains_charFun mu hX hmean hsecond
        hrho hz hrhoLo hu0 hu hsin hcos
  have hrect := rectangularEnvelope_sound hreal himag
  simpa only [Complex.norm_def, Complex.normSq_apply, pow_two] using hrect

theorem errorToCosEnvelope_contains_charFun
    {rho z uBox sinU cosU : DyadicInterval}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hrhoLo : 0 < rho.lo)
    {uR : ℝ} (hu0 : 0 ≤ uR) (hu : uBox.Contains uR)
    (hsin : sinU.Contains (Real.sin uR))
    (hcos : cosU.Contains (Real.cos uR)) :
    let d := dUpper rho z
    let real := realInterval rho d uBox sinU cosU
    let imag := imagInterval rho z d uBox sinU cosU
    let realRadius := finiteRealRadius d uBox sinU
    (errorToCosEnvelope real realRadius imag cosU).Contains
      ‖charFun mu uR - (Real.cos uR : ℂ)‖ := by
  let d := dUpper rho z
  let real := realInterval rho d uBox sinU cosU
  let imag := imagInterval rho z d uBox sinU cosU
  let realRadius := finiteRealRadius d uBox sinU
  let dR := 1 - ∫ x : ℝ, |x| ∂mu
  have hd : d.Contains dR := by
    simpa only [d, dR] using
      dUpper_contains_radialDefect mu hX hmean hsecond hrho hz hrhoLo
  have hreal : real.Contains (charFun mu uR).re := by
    simpa only [real, d] using
      realInterval_contains_charFun mu hX hmean hsecond
        hrho hz hrhoLo hu0 hu hsin hcos
  have himag : imag.Contains |(charFun mu uR).im| := by
    simpa only [imag, d] using
      imagInterval_contains_charFun mu hX hmean hsecond
        hrho hz hrhoLo hu0 hu hsin hcos
  have hradius : realRadius.Contains
      (dR * (|uR * Real.sin uR| + uR ^ 2)) := by
    simpa only [realRadius] using
      finiteRealRadius_sound hd hu hsin
  have herrorRadius : |(charFun mu uR).re - Real.cos uR| ≤
      dR * (|uR * Real.sin uR| + uR ^ 2) := by
    simpa only [dR] using
      charFun_real_radial_bound mu hX hsecond uR
  have herror := errorToCosEnvelope_sound hreal hcos hradius himag
    herrorRadius
  simpa only [Complex.norm_def, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero,
    pow_two] using herror

/-- One representative end-to-end law-to-cell bridge: the proved dyadic
trigonometric primitive is instantiated on a nonnegative frequency cell, then
the actual characteristic function is enclosed both in modulus and relative
to the exact Rademacher reference `cos u`. -/
theorem finiteRadialEnvelopes_sound
    {rho z uBox : DyadicInterval}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hrhoLo : 0 < rho.lo) (huBoxLo : 0 ≤ uBox.lo)
    {uR : ℝ} (hu : uBox.Contains uR) :
    let trig := trigSinCos uBox
    let d := dUpper rho z
    let real := realInterval rho d uBox trig.1 trig.2
    let imag := imagInterval rho z d uBox trig.1 trig.2
    let realRadius := finiteRealRadius d uBox trig.1
    (rectangularEnvelope real imag).Contains ‖charFun mu uR‖ ∧
      (errorToCosEnvelope real realRadius imag trig.2).Contains
        ‖charFun mu uR - (Real.cos uR : ℂ)‖ := by
  let trig := trigSinCos uBox
  let d := dUpper rho z
  let real := realInterval rho d uBox trig.1 trig.2
  let imag := imagInterval rho z d uBox trig.1 trig.2
  let realRadius := finiteRealRadius d uBox trig.1
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  have huLower0 : 0 ≤ uBox.lower := by
    exact div_nonneg (by exact_mod_cast huBoxLo) hscale.le
  have hu0 : 0 ≤ uR := huLower0.trans hu.1
  have htrig := trigSinCos_sound hu huBoxLo
  constructor
  · simpa only [trig, d, real, imag] using
      rectangularEnvelope_contains_charFun mu hX hmean hsecond
        hrho hz hrhoLo hu0 hu htrig.1 htrig.2
  · simpa only [trig, d, real, imag, realRadius] using
      errorToCosEnvelope_contains_charFun mu hX hmean hsecond
        hrho hz hrhoLo hu0 hu htrig.1 htrig.2

/-- Law-level soundness of the exact Rademacher-reference branch after the
radial and trigonometric bridges.  `routeA` is left abstract here because its
sound interval is already supplied by the accepted the baseline bound cell checker. -/
theorem finiteRademacherBranch_upper
    {n : ℕ} (hn : 1 ≤ n)
    {rho z uBox routeA : DyadicInterval} {routeAR : ℝ}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hrhoLo : 0 < rho.lo) (huBoxLo : 0 ≤ uBox.lo)
    (hrouteA : routeA.Contains routeAR)
    {uR : ℝ} (hu : uBox.Contains uR)
    (hnormRouteA : ‖charFun mu uR‖ ≤ routeAR) :
    let trig := trigSinCos uBox
    let d := dUpper rho z
    let real := realInterval rho d uBox trig.1 trig.2
    let imag := imagInterval rho z d uBox trig.1 trig.2
    let rectangular := rectangularEnvelope real imag
    let f := minModulusEnvelope routeA rectangular
    let realRadius := finiteRealRadius d uBox trig.1
    let errorToCos :=
      errorToCosEnvelope real realRadius imag trig.2
    let cosAbs := absHull trig.2
    let normalN := normalN n uBox
    ‖(charFun mu uR) ^ n -
        (Real.exp (-((n : ℝ) * (uR ^ 2 / 2))) : ℂ)‖ ≤
      (rademacherDifferenceIntervals
        n f errorToCos trig.2 cosAbs normalN).upper := by
  let trig := trigSinCos uBox
  let d := dUpper rho z
  let real := realInterval rho d uBox trig.1 trig.2
  let imag := imagInterval rho z d uBox trig.1 trig.2
  let rectangular := rectangularEnvelope real imag
  let f := minModulusEnvelope routeA rectangular
  let realRadius := finiteRealRadius d uBox trig.1
  let errorToCos := errorToCosEnvelope real realRadius imag trig.2
  let cosAbs := absHull trig.2
  let normalN := normalN n uBox
  have henv := finiteRadialEnvelopes_sound mu hX hmean hsecond
    hrho hz hrhoLo huBoxLo hu
  have hrect : rectangular.Contains ‖charFun mu uR‖ := by
    simpa only [trig, d, real, imag, rectangular] using henv.1
  have herror : errorToCos.Contains
      ‖charFun mu uR - (Real.cos uR : ℂ)‖ := by
    simpa only [trig, d, real, imag, realRadius, errorToCos] using henv.2
  have hf : f.Contains ‖charFun mu uR‖ := by
    simpa only [f] using minModulusEnvelope_sound
      hrouteA hrect (norm_nonneg _) (norm_charFun_le_one uR)
        hnormRouteA le_rfl
  have htrig := trigSinCos_sound hu huBoxLo
  have hcosAbs : cosAbs.Contains |Real.cos uR| := by
    simpa only [trig, cosAbs] using absHull_sound htrig.2
  have hnormal : normalN.Contains
      (Real.exp (-((n : ℝ) * (uR ^ 2 / 2)))) := by
    simpa only [normalN] using normalN_sound (n := n) hu
  exact rademacherDifferenceIntervals_upper hn hf herror htrig.2
    hcosAbs hnormal

end

end BerryEsseen
