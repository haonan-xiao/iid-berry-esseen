import BerryEsseen.CharacteristicFunctions.FiniteSumComparison
import BerryEsseen.Smoothing.Prawitz.FiniteCell

/-!
# Smoothing / Finite Envelope
-/

namespace BerryEsseen

open MeasureTheory ProbabilityTheory intervalIntegral

noncomputable section

def scalarDbar (rho z : ℝ) : ℝ :=
  min (1 - 1 / rho) (1 - z)

def scalarU (rho z t : ℝ) : ℝ :=
  routeBUFrequency rho (routeBDboundR rho z) t

def scalarRealRadius (rho z t : ℝ) : ℝ :=
  let d := scalarDbar rho z
  let u := scalarU rho z t
  d * (|u * Real.sin u| + u ^ 2)

def scalarRealLow (rho z t : ℝ) : ℝ :=
  let u := scalarU rho z t
  let radius := scalarRealRadius rho z t
  max (-1) (max (Real.cos u - radius) (1 - u ^ 2 / 2))

def scalarRealHigh (rho z t : ℝ) : ℝ :=
  let u := scalarU rho z t
  let radius := scalarRealRadius rho z t
  min 1 (min (Real.cos u + radius)
    (1 - u ^ 2 / 2 + routeBKappaUpper * rho * u ^ 3))

def scalarImagTaylor (rho z t : ℝ) : ℝ :=
  let d := scalarDbar rho z
  let u := scalarU rho z t
  Real.sqrt (2 * d) * |Real.sin u - u * Real.cos u| + d * u ^ 2

def scalarImagCircle (rho z t : ℝ) : ℝ :=
  let u := scalarU rho z t
  u ^ 3 * Real.sqrt (rho ^ 2 - z ^ 2) / 6

def scalarImag (rho z t : ℝ) : ℝ :=
  min (scalarImagTaylor rho z t) (scalarImagCircle rho z t)

def scalarRectangular (rho z t : ℝ) : ℝ :=
  let realAbs := max |scalarRealLow rho z t|
    |scalarRealHigh rho z t|
  Real.sqrt (realAbs ^ 2 + scalarImag rho z t ^ 2)

def scalarRealError (rho z t : ℝ) : ℝ :=
  let u := scalarU rho z t
  let intersected := max
    |scalarRealLow rho z t - Real.cos u|
    |scalarRealHigh rho z t - Real.cos u|
  min (scalarRealRadius rho z t) intersected

def scalarErrorToCos (rho z t : ℝ) : ℝ :=
  Real.sqrt (scalarRealError rho z t ^ 2 +
    scalarImag rho z t ^ 2)

def scalarModulus (rho z t : ℝ) : ℝ :=
  min 1 (min
    (routeBModulusEnvelope routeBKappa routeBTheta rho
      (routeBDboundR rho z) t)
    (scalarRectangular rho z t))

def scalarNormalOne (rho z t : ℝ) : ℝ :=
  routeBGaussianEnvelope rho (routeBDboundR rho z) t

def scalarNormalN (n : ℕ) (rho z t : ℝ) : ℝ :=
  routeBPowerGaussianEnvelope n rho (routeBDboundR rho z) t

def scalarDiskDifference (n : ℕ) (rho z t : ℝ) : ℝ :=
  let u := scalarU rho z t
  (n : ℝ) * rho * u ^ 3 *
    routeBDiskBound routeBKappa rho (routeBDboundR rho z)
      (2 * Real.pi * t / routeBDboundR rho z) *
    max (scalarModulus rho z t)
      (scalarNormalOne rho z t) ^ (n - 1)

def scalarTrivialDifference (n : ℕ) (rho z t : ℝ) : ℝ :=
  scalarModulus rho z t ^ n + scalarNormalN n rho z t

def scalarRademacherDifference (n : ℕ) (rho z t : ℝ) : ℝ :=
  let u := scalarU rho z t
  (n : ℝ) * scalarErrorToCos rho z t *
      max (scalarModulus rho z t) |Real.cos u| ^ (n - 1) +
    |Real.cos u ^ n - scalarNormalN n rho z t|

def scalarPowerDifference (n : ℕ) (rho z t : ℝ) : ℝ :=
  min (scalarDiskDifference n rho z t)
    (min (scalarTrivialDifference n rho z t)
      (scalarRademacherDifference n rho z t))

def scalarPowerModulus (n : ℕ) (rho z t : ℝ) : ℝ :=
  scalarModulus rho z t ^ n

lemma scalarModulus_nonneg (rho z t : ℝ) :
    0 ≤ scalarModulus rho z t := by
  unfold scalarModulus scalarRectangular
  exact le_min zero_le_one (le_min
    (routeBModulusEnvelope_nonneg routeBKappa routeBTheta rho
      (routeBDboundR rho z) t)
    (Real.sqrt_nonneg _))

lemma scalarModulus_le_routeB (rho z t : ℝ) :
    scalarModulus rho z t ≤
      routeBModulusEnvelope routeBKappa routeBTheta rho
        (routeBDboundR rho z) t := by
  unfold scalarModulus
  exact (min_le_right _ _).trans (min_le_left _ _)

lemma scalarPowerModulus_le_routeB
    (n : ℕ) (rho z t : ℝ) :
    scalarPowerModulus n rho z t ≤
      routeBPowerModulusEnvelope routeBKappa routeBTheta n rho
        (routeBDboundR rho z) t := by
  unfold scalarPowerModulus routeBPowerModulusEnvelope
  exact pow_le_pow_left₀ (scalarModulus_nonneg rho z t)
    (scalarModulus_le_routeB rho z t) n

lemma measurable_scalarU (rho z : ℝ) :
    Measurable (scalarU rho z) := by
  unfold scalarU
  exact measurable_routeBUFrequency rho (routeBDboundR rho z)

lemma measurable_scalarRealRadius (rho z : ℝ) :
    Measurable (scalarRealRadius rho z) := by
  let hu := measurable_scalarU rho z
  unfold scalarRealRadius
  exact measurable_const.mul ((hu.mul hu.sin).abs.add (hu.pow_const 2))

lemma measurable_scalarRealLow (rho z : ℝ) :
    Measurable (scalarRealLow rho z) := by
  let hu := measurable_scalarU rho z
  let hRadius := measurable_scalarRealRadius rho z
  unfold scalarRealLow
  exact measurable_const.max ((hu.cos.sub hRadius).max
    (measurable_const.sub ((hu.pow_const 2).div_const 2)))

lemma measurable_scalarRealHigh (rho z : ℝ) :
    Measurable (scalarRealHigh rho z) := by
  let hu := measurable_scalarU rho z
  let hRadius := measurable_scalarRealRadius rho z
  unfold scalarRealHigh
  exact measurable_const.min ((hu.cos.add hRadius).min
    ((measurable_const.sub ((hu.pow_const 2).div_const 2)).add
      (((measurable_const.mul measurable_const).mul (hu.pow_const 3)))))

lemma measurable_scalarImagTaylor (rho z : ℝ) :
    Measurable (scalarImagTaylor rho z) := by
  let hu := measurable_scalarU rho z
  unfold scalarImagTaylor
  exact (measurable_const.mul
    ((hu.sin.sub (hu.mul hu.cos)).abs)).add
      (measurable_const.mul (hu.pow_const 2))

lemma measurable_scalarImagCircle (rho z : ℝ) :
    Measurable (scalarImagCircle rho z) := by
  let hu := measurable_scalarU rho z
  unfold scalarImagCircle
  exact ((hu.pow_const 3).mul measurable_const).div_const 6

lemma measurable_scalarImag (rho z : ℝ) :
    Measurable (scalarImag rho z) := by
  unfold scalarImag
  exact (measurable_scalarImagTaylor rho z).min
    (measurable_scalarImagCircle rho z)

lemma measurable_scalarRectangular (rho z : ℝ) :
    Measurable (scalarRectangular rho z) := by
  let hLow := measurable_scalarRealLow rho z
  let hHigh := measurable_scalarRealHigh rho z
  let hImag := measurable_scalarImag rho z
  unfold scalarRectangular
  exact (((hLow.abs.max hHigh.abs).pow_const 2).add
    (hImag.pow_const 2)).sqrt

lemma measurable_scalarRealError (rho z : ℝ) :
    Measurable (scalarRealError rho z) := by
  let hu := measurable_scalarU rho z
  let hRadius := measurable_scalarRealRadius rho z
  let hLow := measurable_scalarRealLow rho z
  let hHigh := measurable_scalarRealHigh rho z
  unfold scalarRealError
  exact hRadius.min ((hLow.sub hu.cos).abs.max (hHigh.sub hu.cos).abs)

lemma measurable_scalarErrorToCos (rho z : ℝ) :
    Measurable (scalarErrorToCos rho z) := by
  unfold scalarErrorToCos
  exact (((measurable_scalarRealError rho z).pow_const 2).add
    ((measurable_scalarImag rho z).pow_const 2)).sqrt

lemma measurable_scalarModulus (rho z : ℝ) :
    Measurable (scalarModulus rho z) := by
  unfold scalarModulus
  exact measurable_const.min
    ((measurable_routeBModulusEnvelope routeBKappa routeBTheta rho
      (routeBDboundR rho z)).min
      (measurable_scalarRectangular rho z))

lemma measurable_scalarNormalOne (rho z : ℝ) :
    Measurable (scalarNormalOne rho z) := by
  unfold scalarNormalOne
  exact measurable_routeBGaussianEnvelope rho (routeBDboundR rho z)

lemma measurable_scalarNormalN (n : ℕ) (rho z : ℝ) :
    Measurable (scalarNormalN n rho z) := by
  unfold scalarNormalN
  exact measurable_routeBPowerGaussianEnvelope n rho (routeBDboundR rho z)

lemma measurable_scalarPowerModulus
    (n : ℕ) (rho z : ℝ) :
    Measurable (scalarPowerModulus n rho z) := by
  unfold scalarPowerModulus
  exact (measurable_scalarModulus rho z).pow_const n

lemma measurable_scalarDiskDifference
    (n : ℕ) (rho z : ℝ) :
    Measurable (scalarDiskDifference n rho z) := by
  let hu := measurable_scalarU rho z
  let hD := (measurable_routeBDiskBound routeBKappa rho
    (routeBDboundR rho z)).comp (by fun_prop :
      Measurable (fun t : ℝ => 2 * Real.pi * t / routeBDboundR rho z))
  unfold scalarDiskDifference
  exact (((((measurable_const.mul measurable_const).mul
    (hu.pow_const 3)).mul hD).mul
      (((measurable_scalarModulus rho z).max
        (measurable_scalarNormalOne rho z)).pow_const (n - 1))))

lemma measurable_scalarTrivialDifference
    (n : ℕ) (rho z : ℝ) :
    Measurable (scalarTrivialDifference n rho z) := by
  unfold scalarTrivialDifference
  exact ((measurable_scalarModulus rho z).pow_const n).add
    (measurable_scalarNormalN n rho z)

lemma measurable_scalarRademacherDifference
    (n : ℕ) (rho z : ℝ) :
    Measurable (scalarRademacherDifference n rho z) := by
  let hu := measurable_scalarU rho z
  unfold scalarRademacherDifference
  exact (((measurable_const.mul
    (measurable_scalarErrorToCos rho z)).mul
      (((measurable_scalarModulus rho z).max hu.cos.abs).pow_const
        (n - 1))).add
    (((hu.cos.pow_const n).sub
      (measurable_scalarNormalN n rho z)).abs))

lemma measurable_scalarPowerDifference
    (n : ℕ) (rho z : ℝ) :
    Measurable (scalarPowerDifference n rho z) := by
  unfold scalarPowerDifference
  exact (measurable_scalarDiskDifference n rho z).min
    ((measurable_scalarTrivialDifference n rho z).min
      (measurable_scalarRademacherDifference n rho z))

lemma scalarDiskDifference_le_routeBBranch
    (n : ℕ) {rho z t : ℝ} (hrho : 0 < rho)
    (hr : 0 < routeBDboundR rho z) (ht : 0 ≤ t) :
    scalarDiskDifference n rho z t ≤
      (n : ℝ) * rho *
        routeBUFrequency rho (routeBDboundR rho z) t ^ 3 *
        routeBDiskBound routeBKappa rho (routeBDboundR rho z)
          (2 * Real.pi * t / routeBDboundR rho z) *
        max
          (routeBModulusEnvelope routeBKappa routeBTheta rho
            (routeBDboundR rho z) t)
          (routeBGaussianEnvelope rho (routeBDboundR rho z) t) ^
            (n - 1) := by
  have hu : 0 ≤ routeBUFrequency rho (routeBDboundR rho z) t :=
    routeBUFrequency_nonneg hrho hr ht
  have hF0 := scalarModulus_nonneg rho z t
  have hFle := scalarModulus_le_routeB rho z t
  have hmax0 : 0 ≤ max (scalarModulus rho z t)
      (scalarNormalOne rho z t) :=
    hF0.trans (le_max_left _ _)
  have hmax : max (scalarModulus rho z t)
      (scalarNormalOne rho z t) ≤
      max
        (routeBModulusEnvelope routeBKappa routeBTheta rho
          (routeBDboundR rho z) t)
        (routeBGaussianEnvelope rho (routeBDboundR rho z) t) :=
    max_le_max hFle le_rfl
  have hpow := pow_le_pow_left₀ hmax0 hmax (n - 1)
  have hprefix :
      0 ≤ (n : ℝ) * rho *
        routeBUFrequency rho (routeBDboundR rho z) t ^ 3 *
        routeBDiskBound routeBKappa rho (routeBDboundR rho z)
          (2 * Real.pi * t / routeBDboundR rho z) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg n) hrho.le) (pow_nonneg hu 3))
      (routeBDiskBound_nonneg routeBKappa rho (routeBDboundR rho z)
        (2 * Real.pi * t / routeBDboundR rho z))
  unfold scalarDiskDifference scalarU scalarNormalOne
  exact mul_le_mul_of_nonneg_left hpow hprefix

lemma scalarTrivialDifference_le_routeBBranch
    (n : ℕ) (rho z t : ℝ) :
    scalarTrivialDifference n rho z t ≤
      routeBPowerModulusEnvelope routeBKappa routeBTheta n rho
          (routeBDboundR rho z) t +
        routeBPowerGaussianEnvelope n rho (routeBDboundR rho z) t := by
  unfold scalarTrivialDifference scalarNormalN
  exact add_le_add (scalarPowerModulus_le_routeB n rho z t) le_rfl

lemma scalarPowerDifference_le_routeB
    (n : ℕ) {rho z t : ℝ} (hrho : 0 < rho)
    (hr : 0 < routeBDboundR rho z) (ht : 0 ≤ t) :
    scalarPowerDifference n rho z t ≤
      routeBPowerDifferenceEnvelope routeBKappa routeBTheta n rho
        (routeBDboundR rho z) t := by
  have hDisk := scalarDiskDifference_le_routeBBranch n hrho hr ht
  have hTrivial := scalarTrivialDifference_le_routeBBranch n rho z t
  unfold scalarPowerDifference routeBPowerDifferenceEnvelope
  dsimp only
  exact min_le_min hDisk ((min_le_left _ _).trans hTrivial)

def scalarFunctionalBound (n : ℕ) (rho z : ℝ) : ℝ :=
  2 * (∫ t in (0 : ℝ)..prawitzSplit,
    ‖prawitzKernel t‖ * scalarPowerDifference n rho z t) +
  2 * (∫ t in prawitzSplit..(1 : ℝ),
    ‖prawitzKernel t‖ * scalarPowerModulus n rho z t) +
  2 * (∫ t in (0 : ℝ)..prawitzSplit,
    ‖prawitzKernelCorrection t‖ * scalarNormalN n rho z t) +
  (1 / Real.pi) * ∫ t in Set.Ici prawitzSplit,
    scalarNormalN n rho z t / t

lemma routeBDboundR_mul_excess
    {rho r : ℝ} (hrho : rho ≠ 0) :
    routeBDboundR rho (rho * (r - 1)) = r := by
  rw [routeBDboundR_eq_one_add hrho]
  field_simp
  ring

lemma abs_le_max_abs_endpoints
    {L x H : ℝ} (hL : L ≤ x) (hH : x ≤ H) :
    |x| ≤ max |L| |H| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    exact hH.trans ((le_abs_self H).trans (le_max_right _ _))
  · rw [abs_of_nonpos (le_of_not_ge hx)]
    exact (neg_le_neg hL).trans ((neg_le_abs L).trans (le_max_left _ _))

theorem scalarDbar_actual_bounds
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    let rho := thirdAbsoluteMoment mu
    let z := rho * (symmetrizationRatio mu - 1)
    let d := 1 - ∫ x : ℝ, |x| ∂mu
    0 ≤ d ∧ d ≤ scalarDbar rho z := by
  let rho := thirdAbsoluteMoment mu
  let z := rho * (symmetrizationRatio mu - 1)
  let d := 1 - ∫ x : ℝ, |x| ∂mu
  have h := radialDefect_constraints mu hX hmean hsecond
  refine ⟨h.1, ?_⟩
  simpa only [scalarDbar, rho, z, d] using le_min h.2.1 h.2.2

theorem scalar_real_contains_actual
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let z := rho * (symmetrizationRatio mu - 1)
    let u := scalarU rho z t
    scalarRealLow rho z t ≤ (charFun mu u).re ∧
      (charFun mu u).re ≤ scalarRealHigh rho z t := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  let u := scalarU rho z t
  let d := 1 - ∫ x : ℝ, |x| ∂mu
  let dbar := scalarDbar rho z
  let radius := scalarRealRadius rho z t
  have hrhoOne : 1 ≤ rho := by
    simpa only [rho] using thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < rho := lt_of_lt_of_le zero_lt_one hrhoOne
  have hrLower : 1 ≤ r := by
    simpa only [r] using symmetrizationRatio_lower mu hX hmean hsecond
  have hrPos : 0 < r := lt_of_lt_of_le zero_lt_one hrLower
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrhoPos.ne'
  have hu0 : 0 ≤ u := by
    dsimp only [u, scalarU]
    rw [hrouteR]
    exact routeBUFrequency_nonneg hrhoPos hrPos ht
  have hdb := scalarDbar_actual_bounds mu hX hmean hsecond
  have hd0 : 0 ≤ d := by simpa only [rho, r, z, d] using hdb.1
  have hdle : d ≤ dbar := by
    simpa only [rho, r, z, d, dbar] using hdb.2
  have hbase0 : 0 ≤ |u * Real.sin u| + u ^ 2 :=
    add_nonneg (abs_nonneg _) (sq_nonneg _)
  have htaylor : |(charFun mu u).re - Real.cos u| ≤
      d * (|u * Real.sin u| + u ^ 2) := by
    simpa only [d] using charFun_real_radial_bound mu hX hsecond u
  have hradius : |(charFun mu u).re - Real.cos u| ≤ radius := by
    calc
      |(charFun mu u).re - Real.cos u| ≤
          d * (|u * Real.sin u| + u ^ 2) := htaylor
      _ ≤ dbar * (|u * Real.sin u| + u ^ 2) :=
        mul_le_mul_of_nonneg_right hdle hbase0
      _ = radius := by
        simp only [radius, scalarRealRadius, dbar, u]
  have hradiusBounds := (abs_le).1 hradius
  have hrealLow : Real.cos u - radius ≤ (charFun mu u).re := by linarith
  have hrealHigh : (charFun mu u).re ≤ Real.cos u + radius := by linarith
  have hquadratic : 1 - u ^ 2 / 2 ≤ (charFun mu u).re := by
    have h := charFun_real_remainder_nonneg mu hX hsecond u
    linarith
  have hrem := charFun_real_remainder_le_certificate
    mu hX hsecond routeB_exactMinorantCertificate u
  rw [abs_of_nonneg hu0] at hrem
  change (charFun mu u).re - (1 - u ^ 2 / 2) ≤
    (rho * u ^ 3) * routeBKappa at hrem
  have hfactor0 : 0 ≤ rho * u ^ 3 :=
    mul_nonneg hrhoPos.le (pow_nonneg hu0 3)
  have hkappa : (rho * u ^ 3) * routeBKappa ≤
      (rho * u ^ 3) * routeBKappaUpper :=
    mul_le_mul_of_nonneg_left routeBKappa_lt_upper.le hfactor0
  have hcubic : (charFun mu u).re ≤
      1 - u ^ 2 / 2 + routeBKappaUpper * rho * u ^ 3 := by
    nlinarith
  have hunit := charFun_real_mem_unit mu u
  constructor
  · change max (-1) (max (Real.cos u - radius) (1 - u ^ 2 / 2)) ≤
      (charFun mu u).re
    exact max_le hunit.1 (max_le hrealLow hquadratic)
  · change (charFun mu u).re ≤
      min 1 (min (Real.cos u + radius)
        (1 - u ^ 2 / 2 + routeBKappaUpper * rho * u ^ 3))
    exact le_min hunit.2 (le_min hrealHigh hcubic)

theorem scalar_imag_bounds_actual
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let z := rho * (symmetrizationRatio mu - 1)
    let u := scalarU rho z t
    |(charFun mu u).im| ≤ scalarImag rho z t := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  let u := scalarU rho z t
  let d := 1 - ∫ x : ℝ, |x| ∂mu
  let dbar := scalarDbar rho z
  have hrhoOne : 1 ≤ rho := by
    simpa only [rho] using thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < rho := lt_of_lt_of_le zero_lt_one hrhoOne
  have hrLower : 1 ≤ r := by
    simpa only [r] using symmetrizationRatio_lower mu hX hmean hsecond
  have hrPos : 0 < r := lt_of_lt_of_le zero_lt_one hrLower
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrhoPos.ne'
  have hu0 : 0 ≤ u := by
    dsimp only [u, scalarU]
    rw [hrouteR]
    exact routeBUFrequency_nonneg hrhoPos hrPos ht
  have hdb := scalarDbar_actual_bounds mu hX hmean hsecond
  have hdle : d ≤ dbar := by
    simpa only [rho, r, z, d, dbar] using hdb.2
  have hsqrt : Real.sqrt (2 * d) ≤ Real.sqrt (2 * dbar) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hfirst :
      Real.sqrt (2 * d) * |Real.sin u - u * Real.cos u| ≤
        Real.sqrt (2 * dbar) * |Real.sin u - u * Real.cos u| :=
    mul_le_mul_of_nonneg_right hsqrt (abs_nonneg _)
  have hsecondTerm : d * u ^ 2 ≤ dbar * u ^ 2 :=
    mul_le_mul_of_nonneg_right hdle (sq_nonneg u)
  have hradial := charFun_imag_radial_bound mu hX hmean hsecond u
  have htaylor : |(charFun mu u).im| ≤ scalarImagTaylor rho z t := by
    calc
      |(charFun mu u).im| ≤
          Real.sqrt (2 * d) * |Real.sin u - u * Real.cos u| +
            u ^ 2 * d := by simpa only [d] using hradial
      _ ≤ Real.sqrt (2 * dbar) * |Real.sin u - u * Real.cos u| +
          dbar * u ^ 2 := by nlinarith
      _ = scalarImagTaylor rho z t := by
        simp only [scalarImagTaylor, dbar, u]
  have hcircle : |(charFun mu u).im| ≤
      scalarImagCircle rho z t := by
    have h := charFun_im_sine_circle_reparam
      mu hX hmean hsecond hu0
    change |(charFun mu u).im| ≤
      u ^ 3 * Real.sqrt (rho ^ 2 - z ^ 2) / 6 at h
    simpa only [scalarImagCircle, u] using h
  simpa only [scalarImag] using le_min htaylor hcircle

theorem scalar_rectangular_actual
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let z := rho * (symmetrizationRatio mu - 1)
    let u := scalarU rho z t
    ‖charFun mu u‖ ≤ scalarRectangular rho z t := by
  let rho := thirdAbsoluteMoment mu
  let z := rho * (symmetrizationRatio mu - 1)
  let u := scalarU rho z t
  let L := scalarRealLow rho z t
  let H := scalarRealHigh rho z t
  let I := scalarImag rho z t
  let realAbs := max |L| |H|
  have hreal := scalar_real_contains_actual mu hX hmean hsecond ht
  have himag := scalar_imag_bounds_actual mu hX hmean hsecond ht
  have hreAbs : |(charFun mu u).re| ≤ realAbs := by
    exact abs_le_max_abs_endpoints hreal.1 hreal.2
  have hreSq : (charFun mu u).re ^ 2 ≤ realAbs ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (charFun mu u).re) hreAbs 2
    simpa only [sq_abs] using this
  have himSq : (charFun mu u).im ^ 2 ≤ I ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (charFun mu u).im) himag 2
    simpa only [sq_abs] using this
  have hsum : (charFun mu u).re ^ 2 + (charFun mu u).im ^ 2 ≤
      realAbs ^ 2 + I ^ 2 := add_le_add hreSq himSq
  calc
    ‖charFun mu u‖ =
        Real.sqrt ((charFun mu u).re ^ 2 + (charFun mu u).im ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]
      congr 1
      ring
    _ ≤ Real.sqrt (realAbs ^ 2 + I ^ 2) := Real.sqrt_le_sqrt hsum
    _ = scalarRectangular rho z t := by
      rfl

theorem scalar_errorToCos_actual
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let z := rho * (symmetrizationRatio mu - 1)
    let u := scalarU rho z t
    ‖charFun mu u - (Real.cos u : ℂ)‖ ≤
      scalarErrorToCos rho z t := by
  let rho := thirdAbsoluteMoment mu
  let z := rho * (symmetrizationRatio mu - 1)
  let u := scalarU rho z t
  let d := 1 - ∫ x : ℝ, |x| ∂mu
  let dbar := scalarDbar rho z
  let radius := scalarRealRadius rho z t
  let L := scalarRealLow rho z t
  let H := scalarRealHigh rho z t
  let I := scalarImag rho z t
  let intersected := max |L - Real.cos u| |H - Real.cos u|
  let realError := min radius intersected
  have hreal := scalar_real_contains_actual mu hX hmean hsecond ht
  have himag := scalar_imag_bounds_actual mu hX hmean hsecond ht
  have hdb := scalarDbar_actual_bounds mu hX hmean hsecond
  have hdle : d ≤ dbar := by
    simpa only [rho, z, d, dbar] using hdb.2
  have hbase0 : 0 ≤ |u * Real.sin u| + u ^ 2 :=
    add_nonneg (abs_nonneg _) (sq_nonneg _)
  have hradial := charFun_real_radial_bound mu hX hsecond u
  have hradius : |(charFun mu u).re - Real.cos u| ≤ radius := by
    calc
      |(charFun mu u).re - Real.cos u| ≤
          d * (|u * Real.sin u| + u ^ 2) := by
        simpa only [d] using hradial
      _ ≤ dbar * (|u * Real.sin u| + u ^ 2) :=
        mul_le_mul_of_nonneg_right hdle hbase0
      _ = radius := by
        simp only [radius, scalarRealRadius, dbar, u]
  have hintersected : |(charFun mu u).re - Real.cos u| ≤ intersected := by
    exact abs_le_max_abs_endpoints
      (sub_le_sub_right hreal.1 (Real.cos u))
      (sub_le_sub_right hreal.2 (Real.cos u))
  have hrealError : |(charFun mu u).re - Real.cos u| ≤ realError :=
    le_min hradius hintersected
  have hreSq : ((charFun mu u).re - Real.cos u) ^ 2 ≤ realError ^ 2 := by
    have := pow_le_pow_left₀
      (abs_nonneg ((charFun mu u).re - Real.cos u)) hrealError 2
    simpa only [sq_abs] using this
  have himSq : (charFun mu u).im ^ 2 ≤ I ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (charFun mu u).im) himag 2
    simpa only [sq_abs] using this
  have hsum : ((charFun mu u).re - Real.cos u) ^ 2 +
      (charFun mu u).im ^ 2 ≤ realError ^ 2 + I ^ 2 :=
    add_le_add hreSq himSq
  calc
    ‖charFun mu u - (Real.cos u : ℂ)‖ =
        Real.sqrt (((charFun mu u).re - Real.cos u) ^ 2 +
          (charFun mu u).im ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]
      norm_num only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, sub_zero]
      congr 1
      ring
    _ ≤ Real.sqrt (realError ^ 2 + I ^ 2) := Real.sqrt_le_sqrt hsum
    _ = scalarErrorToCos rho z t := by
      rfl

theorem scalar_modulus_actual
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let z := rho * (symmetrizationRatio mu - 1)
    let u := scalarU rho z t
    ‖charFun mu u‖ ≤ scalarModulus rho z t := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  let u := scalarU rho z t
  have hrhoOne : 1 ≤ rho := by
    simpa only [rho] using thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < rho := lt_of_lt_of_le zero_lt_one hrhoOne
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrhoPos.ne'
  have huEq : u = routeBUFrequency rho r t := by
    dsimp only [u, scalarU]
    rw [hrouteR]
  have hroute := routeB_charFun_norm_le_modulusEnvelope
    mu hX hmean hsecond routeB_exactMinorantCertificate ht
  have hroute' : ‖charFun mu u‖ ≤
      routeBModulusEnvelope routeBKappa routeBTheta rho
        (routeBDboundR rho z) t := by
    rw [hrouteR, huEq]
    simpa only [rho, r] using hroute
  have hrect := scalar_rectangular_actual mu hX hmean hsecond ht
  change ‖charFun mu u‖ ≤ min 1
    (min (routeBModulusEnvelope routeBKappa routeBTheta rho
      (routeBDboundR rho z) t) (scalarRectangular rho z t))
  exact le_min (norm_charFun_le_one u) (le_min hroute' hrect)

lemma scalarNormalOne_eq (rho z t : ℝ) :
    scalarNormalOne rho z t =
      Real.exp (-(scalarU rho z t) ^ 2 / 2) := rfl

lemma scalarNormalN_nonneg (n : ℕ) (rho z t : ℝ) :
    0 ≤ scalarNormalN n rho z t := by
  exact routeBPowerGaussianEnvelope_nonneg n rho (routeBDboundR rho z) t

lemma scalarNormalN_complex_eq (n : ℕ) (rho z t : ℝ) :
    (scalarNormalN n rho z t : ℂ) =
      Complex.exp (-(scalarU rho z t : ℂ) ^ 2 / 2) ^ n := by
  have hbase :
      (routeBGaussianEnvelope rho (routeBDboundR rho z) t : ℂ) =
        Complex.exp (-(scalarU rho z t : ℂ) ^ 2 / 2) := by
    rw [complex_gaussian_eq_real]
    rfl
  calc
    (scalarNormalN n rho z t : ℂ) =
        (routeBGaussianEnvelope rho (routeBDboundR rho z) t : ℂ) ^ n := by
      exact Complex.ofReal_pow _ n
    _ = Complex.exp (-(scalarU rho z t : ℂ) ^ 2 / 2) ^ n := by
      rw [hbase]

theorem scalar_rademacher_difference_actual
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let z := rho * (symmetrizationRatio mu - 1)
    let u := scalarU rho z t
    ‖charFun mu u ^ n - (scalarNormalN n rho z t : ℂ)‖ ≤
      scalarRademacherDifference n rho z t := by
  let rho := thirdAbsoluteMoment mu
  let z := rho * (symmetrizationRatio mu - 1)
  let u := scalarU rho z t
  let F := scalarModulus rho z t
  let E := scalarErrorToCos rho z t
  let N := scalarNormalN n rho z t
  have hF : ‖charFun mu u‖ ≤ F := by
    simpa only [rho, z, u, F] using
      scalar_modulus_actual mu hX hmean hsecond ht
  have hE : ‖charFun mu u - (Real.cos u : ℂ)‖ ≤ E := by
    simpa only [rho, z, u, E] using
      scalar_errorToCos_actual mu hX hmean hsecond ht
  have hF0 : 0 ≤ F := (norm_nonneg _).trans hF
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hE
  have hbase : max ‖charFun mu u‖ |Real.cos u| ≤
      max F |Real.cos u| := max_le_max hF le_rfl
  have hbasePow := pow_le_pow_left₀
    (le_trans (norm_nonneg _) (le_max_left _ _)) hbase (n - 1)
  have herrorScaled :
      (n : ℝ) * ‖charFun mu u - (Real.cos u : ℂ)‖ ≤
        (n : ℝ) * E :=
    mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg n)
  have hcomparison :
      (n : ℝ) * ‖charFun mu u - (Real.cos u : ℂ)‖ *
          max ‖charFun mu u‖ |Real.cos u| ^ (n - 1) ≤
        (n : ℝ) * E * max F |Real.cos u| ^ (n - 1) := by
    calc
      (n : ℝ) * ‖charFun mu u - (Real.cos u : ℂ)‖ *
          max ‖charFun mu u‖ |Real.cos u| ^ (n - 1) ≤
        (n : ℝ) * E *
          max ‖charFun mu u‖ |Real.cos u| ^ (n - 1) :=
        mul_le_mul_of_nonneg_right herrorScaled (pow_nonneg (by
          exact le_trans (norm_nonneg _) (le_max_left _ _)) _)
      _ ≤ (n : ℝ) * E * max F |Real.cos u| ^ (n - 1) :=
        mul_le_mul_of_nonneg_left hbasePow
          (mul_nonneg (Nat.cast_nonneg n) hE0)
  have hraw := rademacher_power_difference_le
    (a := charFun mu u) (c := Real.cos u) (g := N) hn
  calc
    ‖charFun mu u ^ n - (N : ℂ)‖ ≤
        (n : ℝ) * ‖charFun mu u - (Real.cos u : ℂ)‖ *
            max ‖charFun mu u‖ |Real.cos u| ^ (n - 1) +
          |Real.cos u ^ n - N| := hraw
    _ ≤ (n : ℝ) * E * max F |Real.cos u| ^ (n - 1) +
          |Real.cos u ^ n - N| := add_le_add hcomparison le_rfl
    _ = scalarRademacherDifference n rho z t := by
      rfl

theorem scalar_trivial_difference_actual
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let z := rho * (symmetrizationRatio mu - 1)
    let u := scalarU rho z t
    ‖charFun mu u ^ n - (scalarNormalN n rho z t : ℂ)‖ ≤
      scalarTrivialDifference n rho z t := by
  let rho := thirdAbsoluteMoment mu
  let z := rho * (symmetrizationRatio mu - 1)
  let u := scalarU rho z t
  let F := scalarModulus rho z t
  let N := scalarNormalN n rho z t
  have hF : ‖charFun mu u‖ ≤ F := by
    simpa only [rho, z, u, F] using
      scalar_modulus_actual mu hX hmean hsecond ht
  have hN0 : 0 ≤ N := by
    simpa only [N] using scalarNormalN_nonneg n rho z t
  calc
    ‖charFun mu u ^ n - (N : ℂ)‖ ≤
        ‖charFun mu u ^ n‖ + ‖(N : ℂ)‖ := norm_sub_le _ _
    _ = ‖charFun mu u‖ ^ n + N := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN0]
    _ ≤ F ^ n + N := add_le_add (pow_le_pow_left₀ (norm_nonneg _) hF n) le_rfl
    _ = scalarTrivialDifference n rho z t := by
      rfl

theorem scalar_disk_difference_actual
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let z := rho * (symmetrizationRatio mu - 1)
    let u := scalarU rho z t
    ‖charFun mu u ^ n - (scalarNormalN n rho z t : ℂ)‖ ≤
      scalarDiskDifference n rho z t := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  let u := scalarU rho z t
  let F := scalarModulus rho z t
  let B := scalarNormalOne rho z t
  let D := routeBDiskBound routeBKappa rho (routeBDboundR rho z)
    (2 * Real.pi * t / routeBDboundR rho z)
  change ‖charFun mu u ^ n - (scalarNormalN n rho z t : ℂ)‖ ≤
    scalarDiskDifference n rho z t
  have hrhoOne : 1 ≤ rho := by
    simpa only [rho] using thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < rho := lt_of_lt_of_le zero_lt_one hrhoOne
  have hrLower : 1 ≤ r := by
    simpa only [r] using symmetrizationRatio_lower mu hX hmean hsecond
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrhoPos.ne'
  have huEq : u = routeBUFrequency rho r t := by
    dsimp only [u, scalarU]
    rw [hrouteR]
  have hF : ‖charFun mu u‖ ≤ F := by
    simpa only [rho, r, z, u, F] using
      scalar_modulus_actual mu hX hmean hsecond ht
  have hBnorm :
      ‖Complex.exp (-(u : ℂ) ^ 2 / 2)‖ = B := by
    rw [complex_gaussian_eq_real, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    rfl
  have hone0 := routeB_one_step_at_smoothing_frequency
    mu hX hmean hsecond routeB_exactMinorantCertificate ht
  have hone :
      ‖charFun mu u - Complex.exp (-(u : ℂ) ^ 2 / 2)‖ ≤
        rho * u ^ 3 * D := by
    dsimp only [D]
    rw [hrouteR, huEq]
    simpa only [rho, r] using hone0
  have hpower := norm_pow_sub_pow_le_nat hn
    (hF.trans (le_max_left F B))
    (hBnorm.le.trans (le_max_right F B))
  have hbase0 : 0 ≤ max F B :=
    (norm_nonneg (charFun mu u)).trans
      (hF.trans (le_max_left F B))
  have hscaled :
      (n : ℝ) *
          ‖charFun mu u - Complex.exp (-(u : ℂ) ^ 2 / 2)‖ *
            max F B ^ (n - 1) ≤
        (n : ℝ) * (rho * u ^ 3 * D) * max F B ^ (n - 1) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg n))
      (pow_nonneg hbase0 _)
  rw [scalarNormalN_complex_eq]
  calc
    ‖charFun mu u ^ n - Complex.exp (-(u : ℂ) ^ 2 / 2) ^ n‖ ≤
        (n : ℝ) *
          ‖charFun mu u - Complex.exp (-(u : ℂ) ^ 2 / 2)‖ *
            max F B ^ (n - 1) := hpower
    _ ≤ (n : ℝ) * (rho * u ^ 3 * D) * max F B ^ (n - 1) := hscaled
    _ = scalarDiskDifference n rho z t := by
      simp only [scalarDiskDifference, u, F, B, D]
      ring

theorem scalar_power_difference_actual
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let z := rho * (symmetrizationRatio mu - 1)
    let u := scalarU rho z t
    ‖charFun mu u ^ n - (scalarNormalN n rho z t : ℂ)‖ ≤
      scalarPowerDifference n rho z t := by
  let rho := thirdAbsoluteMoment mu
  let z := rho * (symmetrizationRatio mu - 1)
  let u := scalarU rho z t
  have hdisk := scalar_disk_difference_actual
    mu hX hmean hsecond hn ht
  have htrivial := scalar_trivial_difference_actual
    mu hX hmean hsecond n ht
  have hrademacher := scalar_rademacher_difference_actual
    mu hX hmean hsecond hn ht
  simpa only [scalarPowerDifference, rho, z, u] using
    le_min hdisk (le_min htrivial hrademacher)

lemma scalarDiskDifference_nonneg
    (n : ℕ) {rho z t : ℝ} (hrho : 0 < rho)
    (hr : 0 < routeBDboundR rho z) (ht : 0 ≤ t) :
    0 ≤ scalarDiskDifference n rho z t := by
  have hu : 0 ≤ scalarU rho z t := by
    unfold scalarU
    exact routeBUFrequency_nonneg hrho hr ht
  have hbase : 0 ≤ max (scalarModulus rho z t)
      (scalarNormalOne rho z t) :=
    (scalarModulus_nonneg rho z t).trans (le_max_left _ _)
  unfold scalarDiskDifference
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg n) hrho.le) (pow_nonneg hu 3))
      (routeBDiskBound_nonneg routeBKappa rho (routeBDboundR rho z)
        (2 * Real.pi * t / routeBDboundR rho z)))
    (pow_nonneg hbase (n - 1))

lemma scalarTrivialDifference_nonneg
    (n : ℕ) (rho z t : ℝ) :
    0 ≤ scalarTrivialDifference n rho z t := by
  unfold scalarTrivialDifference scalarNormalN
  exact add_nonneg
    (pow_nonneg (scalarModulus_nonneg rho z t) n)
    (routeBPowerGaussianEnvelope_nonneg n rho (routeBDboundR rho z) t)

lemma scalarRademacherDifference_nonneg
    (n : ℕ) (rho z t : ℝ) :
    0 ≤ scalarRademacherDifference n rho z t := by
  have hbase : 0 ≤ max (scalarModulus rho z t)
      |Real.cos (scalarU rho z t)| :=
    (scalarModulus_nonneg rho z t).trans (le_max_left _ _)
  unfold scalarRademacherDifference scalarErrorToCos
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _))
      (pow_nonneg hbase (n - 1)))
    (abs_nonneg _)

lemma scalarPowerDifference_nonneg
    (n : ℕ) {rho z t : ℝ} (hrho : 0 < rho)
    (hr : 0 < routeBDboundR rho z) (ht : 0 ≤ t) :
    0 ≤ scalarPowerDifference n rho z t := by
  unfold scalarPowerDifference
  exact le_min
    (scalarDiskDifference_nonneg n hrho hr ht)
    (le_min
      (scalarTrivialDifference_nonneg n rho z t)
      (scalarRademacherDifference_nonneg n rho z t))

theorem standardizedSum_charFun_norm_le
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    let r := symmetrizationRatio (P.map (X 0))
    let z := rho * (r - 1)
    let T := routeBSmoothingT n rho r
    ‖charFun (standardizedSumLaw P X n) (T * t)‖ ≤
      scalarPowerModulus n rho z t := by
  let mu := P.map (X 0)
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  let T := routeBSmoothingT n rho r
  let u := scalarU rho z t
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  have hnPos : 0 < n := by omega
  have hrho : 0 < rho := by
    dsimp only [rho, mu]
    linarith [thirdAbsoluteMoment_ge_one (P.map (X 0)) hX hsecond]
  have hr : 0 < r := by
    dsimp only [r, mu]
    linarith [symmetrizationRatio_lower (P.map (X 0)) hX hmean hsecond]
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrho.ne'
  have huEq : u = routeBUFrequency rho r t := by
    dsimp only [u, scalarU]
    rw [hrouteR]
  have harg : (Real.sqrt (n : ℝ))⁻¹ * (T * t) = u := by
    have hscale := routeBSmoothingT_mul_div_sqrt
      (n := n) (rho := rho) (r := r) (t := t) hnPos hrho hr
    rw [huEq]
    simpa only [T, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscale
  change ‖charFun (standardizedSumLaw P X n) (T * t)‖ ≤
    scalarPowerModulus n rho z t
  rw [charFun_standardizedSumLaw P X hindep hident n (T * t), harg,
    norm_pow]
  unfold scalarPowerModulus
  exact pow_le_pow_left₀ (norm_nonneg _)
    (scalar_modulus_actual mu hX hmean hsecond ht) n

theorem standardizedSum_charFun_difference_le
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    let r := symmetrizationRatio (P.map (X 0))
    let z := rho * (r - 1)
    let T := routeBSmoothingT n rho r
    ‖charFun (standardizedSumLaw P X n) (T * t) -
        Complex.exp (-(T * t : ℂ) ^ 2 / 2)‖ ≤
      scalarPowerDifference n rho z t := by
  let mu := P.map (X 0)
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  let T := routeBSmoothingT n rho r
  let u := scalarU rho z t
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  have hnPos : 0 < n := by omega
  have hrho : 0 < rho := by
    dsimp only [rho, mu]
    linarith [thirdAbsoluteMoment_ge_one (P.map (X 0)) hX hsecond]
  have hr : 0 < r := by
    dsimp only [r, mu]
    linarith [symmetrizationRatio_lower (P.map (X 0)) hX hmean hsecond]
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrho.ne'
  have huEq : u = routeBUFrequency rho r t := by
    dsimp only [u, scalarU]
    rw [hrouteR]
  have harg : (Real.sqrt (n : ℝ))⁻¹ * (T * t) = u := by
    have hscale := routeBSmoothingT_mul_div_sqrt
      (n := n) (rho := rho) (r := r) (t := t) hnPos hrho hr
    rw [huEq]
    simpa only [T, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscale
  change ‖charFun (standardizedSumLaw P X n) (T * t) -
      Complex.exp (-(T * t : ℂ) ^ 2 / 2)‖ ≤
    scalarPowerDifference n rho z t
  rw [charFun_standardizedSumLaw P X hindep hident n (T * t), harg,
    ← complex_gaussian_pow_eq_smoothing_gaussian hnPos hrho hr,
    ← huEq, ← scalarNormalN_complex_eq]
  exact scalar_power_difference_actual mu hX hmean hsecond hn ht

/-- The strengthened low-frequency envelope inherits endpoint integrability
from Route B because it is pointwise no larger than the accepted Route B
power-difference envelope. -/
theorem prawitz_difference_envelope_intervalIntegrable
    (n : ℕ) {rho z : ℝ} (hrho : 0 < rho)
    (hr : 0 < routeBDboundR rho z) :
    IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        scalarPowerDifference n rho z t)
      volume 0 prawitzSplit := by
  have hbase : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        routeBPowerDifferenceEnvelope routeBKappa routeBTheta n rho
          (routeBDboundR rho z) t)
      volume 0 prawitzSplit :=
    routeB_prawitz_difference_envelope_intervalIntegrable
      routeB_exactMinorantCertificate n hrho hr
  refine hbase.mono_fun' ?_ ?_
  · exact ((measurable_prawitzKernel.norm).mul
      (measurable_scalarPowerDifference n rho z)).aestronglyMeasurable
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with t ht
    rw [Set.uIoc_of_le (by norm_num [prawitzSplit] :
      (0 : ℝ) ≤ prawitzSplit)] at ht
    have hnew0 : 0 ≤ scalarPowerDifference n rho z t :=
      scalarPowerDifference_nonneg n hrho hr ht.1.le
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (norm_nonneg (prawitzKernel t)) hnew0)]
    exact mul_le_mul_of_nonneg_left
      (scalarPowerDifference_le_routeB n hrho hr ht.1.le)
      (norm_nonneg (prawitzKernel t))

/-- The strengthened high-frequency modulus envelope is interval-integrable
because its power is pointwise no larger than Route B's power modulus. -/
theorem prawitz_modulus_envelope_intervalIntegrable
    (n : ℕ) (rho z : ℝ) :
    IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        scalarPowerModulus n rho z t)
      volume prawitzSplit 1 := by
  have hbase : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        routeBPowerModulusEnvelope routeBKappa routeBTheta n rho
          (routeBDboundR rho z) t)
      volume prawitzSplit 1 :=
    routeB_prawitz_modulus_envelope_intervalIntegrable
      routeB_exactMinorantCertificate n rho (routeBDboundR rho z)
  refine hbase.mono_fun' ?_ ?_
  · exact ((measurable_prawitzKernel.norm).mul
      (measurable_scalarPowerModulus n rho z)).aestronglyMeasurable
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with t ht
    have hnew0 : 0 ≤ scalarPowerModulus n rho z t := by
      unfold scalarPowerModulus
      exact pow_nonneg (scalarModulus_nonneg rho z t) n
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (norm_nonneg (prawitzKernel t)) hnew0)]
    exact mul_le_mul_of_nonneg_left
      (scalarPowerModulus_le_routeB n rho z t)
      (norm_nonneg (prawitzKernel t))

theorem prawitz_difference_integral_le
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n)
    (hEnvelopeIntegrable : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        scalarPowerDifference n
          (thirdAbsoluteMoment (P.map (X 0)))
          (thirdAbsoluteMoment (P.map (X 0)) *
            (symmetrizationRatio (P.map (X 0)) - 1)) t)
      volume 0 prawitzSplit) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    let r := symmetrizationRatio (P.map (X 0))
    let z := rho * (r - 1)
    let T := routeBSmoothingT n rho r
    (∫ t in (0 : ℝ)..prawitzSplit,
      ‖prawitzKernel t‖ *
        ‖charFun (standardizedSumLaw P X n) (T * t) -
          Complex.exp (-(T * t : ℂ) ^ 2 / 2)‖) ≤
      ∫ t in (0 : ℝ)..prawitzSplit,
        ‖prawitzKernel t‖ * scalarPowerDifference n rho z t := by
  let rho := thirdAbsoluteMoment (P.map (X 0))
  let r := symmetrizationRatio (P.map (X 0))
  let z := rho * (r - 1)
  let T := routeBSmoothingT n rho r
  letI : IsProbabilityMeasure (standardizedSumLaw P X n) :=
    isProbabilityMeasure_standardizedSumLaw P X
      (fun k => (hident k).aemeasurable_fst) n
  change (∫ t in (0 : ℝ)..prawitzSplit,
      ‖prawitzKernel t‖ *
        ‖charFun (standardizedSumLaw P X n) (T * t) -
          Complex.exp (-(T * t : ℂ) ^ 2 / 2)‖) ≤
    ∫ t in (0 : ℝ)..prawitzSplit,
      ‖prawitzKernel t‖ * scalarPowerDifference n rho z t
  have hleftIntegrable : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        ‖charFun (standardizedSumLaw P X n) (T * t) -
          Complex.exp (-(T * t : ℂ) ^ 2 / 2)‖)
      volume 0 prawitzSplit := by
    refine hEnvelopeIntegrable.mono_fun' ?_ ?_
    · exact ((measurable_prawitzKernel.norm).mul
        (((measurable_charFun.comp (by fun_prop)).sub (by fun_prop)).norm)).aestronglyMeasurable
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards with t ht
      rw [Set.uIoc_of_le (by norm_num [prawitzSplit] :
        (0 : ℝ) ≤ prawitzSplit)] at ht
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left
        (standardizedSum_charFun_difference_le
          P X hindep hident hX hmean hsecond hn ht.1.le)
        (norm_nonneg _)
  exact intervalIntegral.integral_mono_on
    (by norm_num [prawitzSplit]) hleftIntegrable hEnvelopeIntegrable fun t ht =>
      mul_le_mul_of_nonneg_left
        (standardizedSum_charFun_difference_le
          P X hindep hident hX hmean hsecond hn ht.1)
        (norm_nonneg _)

theorem prawitz_modulus_integral_le
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n)
    (hEnvelopeIntegrable : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        scalarPowerModulus n
          (thirdAbsoluteMoment (P.map (X 0)))
          (thirdAbsoluteMoment (P.map (X 0)) *
            (symmetrizationRatio (P.map (X 0)) - 1)) t)
      volume prawitzSplit 1) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    let r := symmetrizationRatio (P.map (X 0))
    let z := rho * (r - 1)
    let T := routeBSmoothingT n rho r
    (∫ t in prawitzSplit..(1 : ℝ),
      ‖prawitzKernel t‖ *
        ‖charFun (standardizedSumLaw P X n) (T * t)‖) ≤
      ∫ t in prawitzSplit..(1 : ℝ),
        ‖prawitzKernel t‖ * scalarPowerModulus n rho z t := by
  let rho := thirdAbsoluteMoment (P.map (X 0))
  let r := symmetrizationRatio (P.map (X 0))
  let z := rho * (r - 1)
  let T := routeBSmoothingT n rho r
  letI : IsProbabilityMeasure (standardizedSumLaw P X n) :=
    isProbabilityMeasure_standardizedSumLaw P X
      (fun k => (hident k).aemeasurable_fst) n
  change (∫ t in prawitzSplit..(1 : ℝ),
      ‖prawitzKernel t‖ *
        ‖charFun (standardizedSumLaw P X n) (T * t)‖) ≤
    ∫ t in prawitzSplit..(1 : ℝ),
      ‖prawitzKernel t‖ * scalarPowerModulus n rho z t
  have hleftIntegrable : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        ‖charFun (standardizedSumLaw P X n) (T * t)‖)
      volume prawitzSplit 1 := by
    refine hEnvelopeIntegrable.mono_fun' ?_ ?_
    · exact ((measurable_prawitzKernel.norm).mul
        ((measurable_charFun.comp (by fun_prop)).norm)).aestronglyMeasurable
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards with t ht
      rw [Set.uIoc_of_le (by norm_num [prawitzSplit] :
        prawitzSplit ≤ (1 : ℝ))] at ht
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left
        (standardizedSum_charFun_norm_le
          P X hindep hident hX hmean hsecond hn
            ((by norm_num [prawitzSplit] : 0 ≤ prawitzSplit).trans ht.1.le))
        (norm_nonneg _)
  exact intervalIntegral.integral_mono_on
    (by norm_num [prawitzSplit]) hleftIntegrable hEnvelopeIntegrable fun t ht =>
      mul_le_mul_of_nonneg_left
        (standardizedSum_charFun_norm_le
          P X hindep hident hX hmean hsecond hn
            ((by norm_num [prawitzSplit] : 0 ≤ prawitzSplit).trans ht.1))
        (norm_nonneg _)

theorem prawitzFunctional_standardizedSum_le_scalar_of_intervalIntegrable
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n)
    (hDifferenceIntegrable : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        scalarPowerDifference n
          (thirdAbsoluteMoment (P.map (X 0)))
          (thirdAbsoluteMoment (P.map (X 0)) *
            (symmetrizationRatio (P.map (X 0)) - 1)) t)
      volume 0 prawitzSplit)
    (hModulusIntegrable : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        scalarPowerModulus n
          (thirdAbsoluteMoment (P.map (X 0)))
          (thirdAbsoluteMoment (P.map (X 0)) *
            (symmetrizationRatio (P.map (X 0)) - 1)) t)
      volume prawitzSplit 1) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    let r := symmetrizationRatio (P.map (X 0))
    let z := rho * (r - 1)
    let T := routeBSmoothingT n rho r
    prawitzFunctional (standardizedSumLaw P X n) T prawitzSplit ≤
      scalarFunctionalBound n rho z := by
  let rho := thirdAbsoluteMoment (P.map (X 0))
  let r := symmetrizationRatio (P.map (X 0))
  let z := rho * (r - 1)
  let T := routeBSmoothingT n rho r
  letI : IsProbabilityMeasure (P.map (X 0)) :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  have hnPos : 0 < n := by omega
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith [thirdAbsoluteMoment_ge_one (P.map (X 0)) hX hsecond]
  have hr : 0 < r := by
    dsimp only [r]
    linarith [symmetrizationRatio_lower (P.map (X 0)) hX hmean hsecond]
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrho.ne'
  have hDifference := prawitz_difference_integral_le
    P X hindep hident hX hmean hsecond hn hDifferenceIntegrable
  have hModulus := prawitz_modulus_integral_le
    P X hindep hident hX hmean hsecond hn hModulusIntegrable
  have hnormal (t : ℝ) : scalarNormalN n rho z t =
      routeBPowerGaussianEnvelope n rho r t := by
    simp only [scalarNormalN, hrouteR]
  change prawitzFunctional (standardizedSumLaw P X n) T prawitzSplit ≤
    scalarFunctionalBound n rho z
  unfold prawitzFunctional scalarFunctionalBound
  simp_rw [hnormal,
    routeBPowerGaussianEnvelope_eq_smoothing_gaussian hnPos hrho hr]
  dsimp only [rho, r, z, T] at hDifference hModulus
  linarith

/-- The complete analytic the first-absolute-moment bounds bridge.  No new assumption is added to the
classical i.i.d. interface: both endpoint-integrability obligations are
discharged internally by comparison with the accepted Route B envelopes. -/
theorem prawitzFunctional_standardizedSum_le_scalar
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    let r := symmetrizationRatio (P.map (X 0))
    let z := rho * (r - 1)
    let T := routeBSmoothingT n rho r
    prawitzFunctional (standardizedSumLaw P X n) T prawitzSplit ≤
      scalarFunctionalBound n rho z := by
  let rho := thirdAbsoluteMoment (P.map (X 0))
  let r := symmetrizationRatio (P.map (X 0))
  let z := rho * (r - 1)
  letI : IsProbabilityMeasure (P.map (X 0)) :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith [thirdAbsoluteMoment_ge_one (P.map (X 0)) hX hsecond]
  have hr : 0 < r := by
    dsimp only [r]
    linarith [symmetrizationRatio_lower (P.map (X 0)) hX hmean hsecond]
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrho.ne'
  have hrouteRPos : 0 < routeBDboundR rho z := by
    rw [hrouteR]
    exact hr
  have hDifference : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        scalarPowerDifference n rho z t)
      volume 0 prawitzSplit :=
    prawitz_difference_envelope_intervalIntegrable n hrho hrouteRPos
  have hModulus : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        scalarPowerModulus n rho z t)
      volume prawitzSplit 1 :=
    prawitz_modulus_envelope_intervalIntegrable n rho z
  simpa only [rho, r, z] using
    prawitzFunctional_standardizedSum_le_scalar_of_intervalIntegrable
      P X hindep hident hX hmean hsecond hn hDifference hModulus

/-- The unconditional law-level the first-absolute-moment bounds reduction.  The conclusion has the
same assumptions and quantifiers as the accepted classical i.i.d. Route B
reduction; only the scalar envelope on the right-hand side is strengthened. -/
theorem kolmogorovDistance_standardizedSum_le_scalar
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    let r := symmetrizationRatio (P.map (X 0))
    let z := rho * (r - 1)
    kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw ≤
      scalarFunctionalBound n rho z := by
  let rho := thirdAbsoluteMoment (P.map (X 0))
  let r := symmetrizationRatio (P.map (X 0))
  let z := rho * (r - 1)
  let T := routeBSmoothingT n rho r
  letI : IsProbabilityMeasure (P.map (X 0)) :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  letI : IsProbabilityMeasure (standardizedSumLaw P X n) :=
    isProbabilityMeasure_standardizedSumLaw P X
      (fun k => (hident k).aemeasurable_fst) n
  have hnPos : 0 < n := by omega
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith [thirdAbsoluteMoment_ge_one (P.map (X 0)) hX hsecond]
  have hr : 0 < r := by
    dsimp only [r]
    linarith [symmetrizationRatio_lower (P.map (X 0)) hX hmean hsecond]
  have hT : 0 < T := by
    dsimp only [T]
    exact routeBSmoothingT_pos hnPos hrho hr
  have hX0 : MemLp (X 0) 3 P := by
    have hmap := (memLp_map_measure_iff aestronglyMeasurable_id
      (hident 0).aemeasurable_fst).1 hX
    simpa only [Function.comp_apply, id_eq] using hmap
  have hsumInt : Integrable (id : ℝ → ℝ)
      (standardizedSumLaw P X n) :=
    integrable_id_standardizedSumLaw P X hident hX0 n
  have hsmooth := prawitzSmoothingBound
    (standardizedSumLaw P X n) hsumInt T prawitzSplit hT
      (by norm_num [prawitzSplit]) (by norm_num [prawitzSplit])
  have hfunctional := prawitzFunctional_standardizedSum_le_scalar
    P X hindep hident hX hmean hsecond hn
  dsimp only [rho, r, z, T] at hsmooth hfunctional ⊢
  exact hsmooth.trans hfunctional

end

end BerryEsseen
