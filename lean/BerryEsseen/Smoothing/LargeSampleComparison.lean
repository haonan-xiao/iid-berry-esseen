import BerryEsseen.Smoothing.FiniteEnvelope
import BerryEsseen.CharacteristicFunctions.ExponentialModulus
import BerryEsseen.CharacteristicFunctions.GaussianCorrection
import BerryEsseen.Interval.Finite.Evaluator
import BerryEsseen.Smoothing.Prawitz.LargeNIntegral

/-!
# Smoothing / Large Sample Comparison
-/

namespace BerryEsseen

open MeasureTheory ProbabilityTheory

noncomputable section

lemma scalarDbar_nonneg_of_feasible
    {rho r : ℝ} (hrho : 1 ≤ rho)
    (hfeasible : rho * (r - 1) ≤ 1) :
    0 ≤ scalarDbar rho (rho * (r - 1)) := by
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hinv : 1 / rho ≤ 1 := by
    apply (div_le_iff₀ hrhoPos).2
    simpa using hrho
  unfold scalarDbar
  exact le_min (by linarith) (by linarith)

lemma scalarDbar_le_thirteen_over_250
    {rho r : ℝ} (hrho : 1 ≤ rho) (hr : 19 / 10 ≤ r) :
    scalarDbar rho (rho * (r - 1)) ≤ 13 / 250 := by
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hrOne : 1 ≤ r := by norm_num at hr ⊢; linarith
  have hdSqrt : scalarDbar rho (rho * (r - 1)) ≤
      1 - Real.sqrt (r - 1) := by
    apply d_le_one_sub_sqrt hrhoPos hrOne
    · exact min_le_left _ _
    · exact min_le_right _ _
  exact d_le_thirteen_over_250 hr hdSqrt

theorem scalarModulus_le_large_rate
    {rho r t : ℝ} (hrho : 1 ≤ rho) (hr : 19 / 10 ≤ r)
    (hfeasible : rho * (r - 1) ≤ 1)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) :
    scalarModulus rho (rho * (r - 1)) t ≤
      Real.exp (-((39 / 100 : ℝ) *
        routeBUFrequency rho r t ^ 2)) := by
  let d := scalarDbar rho (rho * (r - 1))
  let u := routeBUFrequency rho r t
  let radius := d * (|u * Real.sin u| + u ^ 2)
  let A := Real.cos u + d * (u * Real.sin u + u ^ 2)
  let B := Real.sqrt (2 * d) * |Real.sin u - u * Real.cos u| + d * u ^ 2
  let low := scalarRealLow rho (rho * (r - 1)) t
  let high := scalarRealHigh rho (rho * (r - 1)) t
  let imag := scalarImag rho (rho * (r - 1)) t
  let realAbs := max |low| |high|
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hrPos : 0 < r := by norm_num at hr ⊢; linarith
  have hrouteR : routeBDboundR rho (rho * (r - 1)) = r := by
    simpa using routeBDboundR_mul_excess hrhoPos.ne'
  have huEq : scalarU rho (rho * (r - 1)) t = u := by
    unfold scalarU
    rw [hrouteR]
  have hd0 : 0 ≤ d := by
    simpa only [d] using scalarDbar_nonneg_of_feasible hrho hfeasible
  have hd : d ≤ 13 / 250 := by
    simpa only [d] using scalarDbar_le_thirteen_over_250 hrho hr
  have hu0 : 0 ≤ u := by
    dsimp only [u]
    exact routeBUFrequency_nonneg hrhoPos hrPos ht0
  have hu56 : u ≤ 5 / 6 := by
    dsimp only [u]
    simpa only [routeBUFrequency, mul_comm] using
      low_frequency_le_five_sixths
        (rho := rho) (r := r) ht0 ht hrho hr
  have hu1 : u ≤ 1 := by norm_num at hu56 ⊢; linarith
  have hsin0 : 0 ≤ Real.sin u := sin_nonneg hu0 hu1
  have husin0 : 0 ≤ u * Real.sin u := mul_nonneg hu0 hsin0
  have habs : |u * Real.sin u| = u * Real.sin u := abs_of_nonneg husin0
  have hradius : radius = d * (u * Real.sin u + u ^ 2) := by
    simp only [radius, habs]
  have hradius0 : 0 ≤ radius := by
    rw [hradius]
    positivity
  have hAeq : A = Real.cos u + radius := by
    rw [hradius]
  have hA0 : 0 ≤ A := by
    simpa only [A] using real_envelope_nonneg hd0 hu0 hu56
  have hbase0 : 0 ≤ 1 - u ^ 2 / 2 := by
    have huSq := (sq_le_25_36 hu0 hu56).2
    nlinarith
  have hcosLower : 1 - u ^ 2 / 2 ≤ Real.cos u := by
    exact Real.one_sub_sq_div_two_le_cos
  have hlowDef : low =
      max (-1) (max (Real.cos u - radius) (1 - u ^ 2 / 2)) := by
    simp only [low, scalarRealLow, scalarRealRadius,
      huEq, radius, d]
  have hlow0 : 0 ≤ low := by
    rw [hlowDef]
    exact hbase0.trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hlowA : low ≤ A := by
    rw [hlowDef]
    apply max_le
    · linarith
    · apply max_le
      · rw [hAeq]
        linarith
      · rw [hAeq]
        exact hcosLower.trans (le_add_of_nonneg_right hradius0)
  have hthird0 : 0 ≤
      1 - u ^ 2 / 2 + routeBKappaUpper * rho * u ^ 3 := by
    have hkappa0 : 0 ≤ routeBKappaUpper := by
      norm_num [routeBKappaUpper]
    have hcubic0 : 0 ≤ routeBKappaUpper * rho * u ^ 3 := by positivity
    linarith
  have hhighDef : high = min 1
      (min (Real.cos u + radius)
        (1 - u ^ 2 / 2 + routeBKappaUpper * rho * u ^ 3)) := by
    simp only [high, scalarRealHigh, scalarRealRadius,
      huEq, radius, d]
  have hhigh0 : 0 ≤ high := by
    rw [hhighDef]
    have hcosRadius0 : 0 ≤ Real.cos u + radius := by
      simpa only [← hAeq] using hA0
    exact le_min zero_le_one (le_min hcosRadius0 hthird0)
  have hhighA : high ≤ A := by
    calc
      high ≤ Real.cos u + radius := by
        rw [hhighDef]
        exact (min_le_right _ _).trans (min_le_left _ _)
      _ = A := hAeq.symm
  have hrealAbs0 : 0 ≤ realAbs := by
    dsimp only [realAbs]
    exact (abs_nonneg low).trans (le_max_left _ _)
  have hrealAbsA : realAbs ≤ A := by
    dsimp only [realAbs]
    rw [abs_of_nonneg hlow0, abs_of_nonneg hhigh0]
    exact max_le hlowA hhighA
  have hcircle0 : 0 ≤ scalarImagCircle rho (rho * (r - 1)) t := by
    unfold scalarImagCircle
    rw [huEq]
    positivity
  have hTaylorEq : scalarImagTaylor rho (rho * (r - 1)) t = B := by
    simp only [scalarImagTaylor, huEq, d, B]
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity
  have himagDef : imag = min B
      (scalarImagCircle rho (rho * (r - 1)) t) := by
    simp only [imag, scalarImag, hTaylorEq]
  have himag0 : 0 ≤ imag := by
    rw [himagDef]
    exact le_min hB0 hcircle0
  have himagB : imag ≤ B := by
    rw [himagDef]
    exact min_le_left _ _
  have hsq : realAbs ^ 2 + imag ^ 2 ≤ A ^ 2 + B ^ 2 := by
    have hrealSq : realAbs ^ 2 ≤ A ^ 2 :=
      (sq_le_sq₀ hrealAbs0 hA0).2 hrealAbsA
    have himagSq : imag ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ himag0 hB0).2 himagB
    exact add_le_add hrealSq himagSq
  have hrect : scalarRectangular rho (rho * (r - 1)) t ≤
      Real.exp (-((39 / 100 : ℝ) * u ^ 2)) := by
    have hsqrt := Real.sqrt_le_sqrt hsq
    have hrate := rectangular_modulus_le_exp hd0 hd hu0 hu56
    have hrectDef : scalarRectangular rho (rho * (r - 1)) t =
        Real.sqrt (realAbs ^ 2 + imag ^ 2) := by rfl
    rw [hrectDef]
    exact hsqrt.trans (by simpa only [A, B] using hrate)
  have hmodulus : scalarModulus rho (rho * (r - 1)) t ≤
      scalarRectangular rho (rho * (r - 1)) t := by
    unfold scalarModulus
    exact (min_le_right _ _).trans (min_le_right _ _)
  simpa only [u] using hmodulus.trans hrect

def largeDirectRateQReal (L r t : ℝ) : ℝ :=
  (39 / 100 : ℝ) * (2 * Real.pi * t) ^ 2 / (r ^ 2 * L ^ 2)

def largeDirectStrongQReal (L r t : ℝ) : ℝ :=
  if t ≤ 1 / 4 then
    max (routeBLargeQ L r t) (largeDirectRateQReal L r t)
  else
    routeBLargeQ L r t

lemma rate_frequency_eq_direct
    {n : ℕ} (hn : 0 < n) {rho r t : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) :
    (n : ℝ) * ((39 / 100 : ℝ) * routeBUFrequency rho r t ^ 2) =
      largeDirectRateQReal (routeBSmoothingScale n rho) r t := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  unfold largeDirectRateQReal routeBUFrequency routeBSmoothingScale
  field_simp [hrho.ne', hr.ne', hsqrt.ne']
  rw [Real.sq_sqrt hnReal.le]
  ring

lemma scalarMaxPower_le_large_old_exp
    {n : ℕ} (hn : 100 ≤ n) {rho r t : ℝ}
    (hrho : 1 ≤ rho) (hr : 1 ≤ r) (ht0 : 0 ≤ t) :
    max (scalarModulus rho (rho * (r - 1)) t)
          (scalarNormalOne rho (rho * (r - 1)) t) ^ (n - 1) ≤
      Real.exp (-routeBLargeNAlpha *
        routeBLargeQ (routeBSmoothingScale n rho) r t) := by
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hrPos : 0 < r := zero_lt_one.trans_le hr
  have hrouteR : routeBDboundR rho (rho * (r - 1)) = r := by
    simpa using routeBDboundR_mul_excess hrhoPos.ne'
  have hF : scalarModulus rho (rho * (r - 1)) t ≤
      routeBModulusEnvelope routeBKappa routeBTheta rho r t := by
    simpa only [hrouteR] using
      scalarModulus_le_routeB rho (rho * (r - 1)) t
  have hB : scalarNormalOne rho (rho * (r - 1)) t =
      routeBGaussianEnvelope rho r t := by
    simp only [scalarNormalOne, hrouteR]
  have hbase :
      max (scalarModulus rho (rho * (r - 1)) t)
          (scalarNormalOne rho (rho * (r - 1)) t) ≤
        max (routeBModulusEnvelope routeBKappa routeBTheta rho r t)
          (routeBGaussianEnvelope rho r t) := by
    rw [hB]
    exact max_le_max hF le_rfl
  have hbase0 : 0 ≤
      max (scalarModulus rho (rho * (r - 1)) t)
        (scalarNormalOne rho (rho * (r - 1)) t) :=
    (scalarModulus_nonneg rho (rho * (r - 1)) t).trans
      (le_max_left _ _)
  have hpow := pow_le_pow_left₀ hbase0 hbase (n - 1)
  exact hpow.trans <|
    routeBMaxEnvelope_pow_le_largeQ_exp hn hrhoPos hrPos ht0

lemma scalarMaxPower_le_large_rate_exp
    {n : ℕ} (hn : 100 ≤ n) {rho r t : ℝ}
    (hrho : 1 ≤ rho) (hr : 19 / 10 ≤ r)
    (hfeasible : rho * (r - 1) ≤ 1)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) :
    max (scalarModulus rho (rho * (r - 1)) t)
          (scalarNormalOne rho (rho * (r - 1)) t) ^ (n - 1) ≤
      Real.exp (-routeBLargeNAlpha *
        largeDirectRateQReal (routeBSmoothingScale n rho) r t) := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hrPos : 0 < r := by norm_num at hr ⊢; linarith
  have hrouteR : routeBDboundR rho (rho * (r - 1)) = r := by
    simpa using routeBDboundR_mul_excess hrhoPos.ne'
  have hF := scalarModulus_le_large_rate hrho hr hfeasible ht0 ht
  have hpow := max_pow_le_rate_exp hn
    (scalarModulus_nonneg rho (rho * (r - 1)) t) hF
  rw [rate_frequency_eq_direct hnPos hrhoPos hrPos] at hpow
  simpa only [scalarNormalOne, routeBGaussianEnvelope,
    scalarU, hrouteR, neg_div] using hpow

theorem scalarMaxPower_le_large_strong_exp
    {n : ℕ} (hn : 100 ≤ n) {rho r t : ℝ}
    (hrho : 1 ≤ rho) (hr : 19 / 10 ≤ r)
    (hfeasible : rho * (r - 1) ≤ 1) (ht0 : 0 ≤ t) :
    max (scalarModulus rho (rho * (r - 1)) t)
          (scalarNormalOne rho (rho * (r - 1)) t) ^ (n - 1) ≤
      Real.exp (-routeBLargeNAlpha *
        largeDirectStrongQReal (routeBSmoothingScale n rho) r t) := by
  have hrOne : 1 ≤ r := by norm_num at hr ⊢; linarith
  have hold := scalarMaxPower_le_large_old_exp hn hrho hrOne ht0
  by_cases htQuarter : t ≤ 1 / 4
  · have hrate := scalarMaxPower_le_large_rate_exp
      hn hrho hr hfeasible ht0 htQuarter
    unfold largeDirectStrongQReal
    rw [if_pos htQuarter]
    rcases le_total
        (routeBLargeQ (routeBSmoothingScale n rho) r t)
        (largeDirectRateQReal (routeBSmoothingScale n rho) r t) with
      hle | hge
    · rw [max_eq_right hle]
      exact hrate
    · rw [max_eq_left hge]
      exact hold
  · unfold largeDirectStrongQReal
    rw [if_neg htQuarter]
    exact hold

def largeDirectTelescopingReal
    (L r t k0 : ℝ) : ℝ :=
  k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
    (refinedRouteBDiskStar r (2 * Real.pi * t / r) /
      (r ^ 3 * L ^ 3)) *
    Real.exp (-routeBLargeNAlpha * largeDirectStrongQReal L r t)

theorem scalar_normalizedDifference_le_large_telescoping
    {n : ℕ} (hn : 100 ≤ n) {rho r t k0 : ℝ}
    (hrho : 1 ≤ rho) (hr : 19 / 10 ≤ r)
    (hfeasible : rho * (r - 1) ≤ 1)
    (ht0 : 0 ≤ t) (hk0 : t * ‖prawitzKernel t‖ ≤ k0) :
    (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ *
        scalarPowerDifference n rho (rho * (r - 1)) t ≤
      largeDirectTelescopingReal
        (routeBSmoothingScale n rho) r t k0 := by
  let L := routeBSmoothingScale n rho
  let F := scalarModulus rho (rho * (r - 1)) t
  let B := scalarNormalOne rho (rho * (r - 1)) t
  let H := max F B ^ (n - 1)
  let D := routeBDiskBound routeBKappa rho r (2 * Real.pi * t / r)
  let Dstar := refinedRouteBDiskStar r (2 * Real.pi * t / r)
  let E := Real.exp (-routeBLargeNAlpha * largeDirectStrongQReal L r t)
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hrPos : 0 < r := by norm_num at hr ⊢; linarith
  have hrStrict : 1 < r := by norm_num at hr ⊢; linarith
  have hLPos : 0 < L := by
    dsimp only [L, routeBSmoothingScale]
    positivity
  have hrouteR : routeBDboundR rho (rho * (r - 1)) = r := by
    simpa using routeBDboundR_mul_excess hrhoPos.ne'
  have hpower : H ≤ E := by
    simpa only [F, B, H, E, L] using
      scalarMaxPower_le_large_strong_exp
        hn hrho hr hfeasible ht0
  have hc0 : 0 ≤ 2 * Real.pi * t / r := by positivity
  have hD : D ≤ Dstar := by
    simpa only [D, Dstar] using
      refinedRouteBDiskBound_le_diskStar hrho hrStrict hfeasible hc0
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact routeBDiskBound_nonneg _ _ _ _
  have hDstar0 : 0 ≤ Dstar := by
    dsimp only [Dstar, refinedRouteBDiskStar]
    positivity
  have hk00 : 0 ≤ k0 :=
    (mul_nonneg ht0 (norm_nonneg _)).trans hk0
  have hfrequency0 : 0 ≤ 2 * (t ^ 2 * (2 * Real.pi) ^ 3) := by
    positivity
  have hdenPos : 0 < r ^ 3 * L ^ 3 :=
    mul_pos (pow_pos hrPos 3) (pow_pos hLPos 3)
  have hDquot0 : 0 ≤ D / (r ^ 3 * L ^ 3) :=
    div_nonneg hD0 hdenPos.le
  have hDstarQuot0 : 0 ≤ Dstar / (r ^ 3 * L ^ 3) :=
    div_nonneg hDstar0 hdenPos.le
  have hH0 : 0 ≤ H := by
    dsimp only [H]
    exact pow_nonneg
      ((scalarModulus_nonneg rho (rho * (r - 1)) t).trans
        (le_max_left _ _)) _
  have hscalar : scalarPowerDifference n rho (rho * (r - 1)) t ≤
      scalarDiskDifference n rho (rho * (r - 1)) t := by
    unfold scalarPowerDifference
    exact min_le_left _ _
  have hscale0 : 0 ≤
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ := by
    positivity
  have hscaleIdentity :
      Real.sqrt (n : ℝ) * (n : ℝ) / rho ^ 3 = 1 / L ^ 3 := by
    let s := Real.sqrt (n : ℝ)
    have hsSq : s ^ 2 = (n : ℝ) := by
      dsimp only [s]
      exact Real.sq_sqrt hnReal.le
    have hsNe : s ≠ 0 := by
      dsimp only [s]
      exact hsqrt.ne'
    change s * (n : ℝ) / rho ^ 3 = 1 / (rho / s) ^ 3
    rw [← hsSq]
    field_simp [hrhoPos.ne', hsNe]
  have hrewrite :
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ *
          scalarDiskDifference n rho (rho * (r - 1)) t =
        (t * ‖prawitzKernel t‖) *
          (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (D / (r ^ 3 * L ^ 3)) * H := by
    calc
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ *
          scalarDiskDifference n rho (rho * (r - 1)) t =
        (t * ‖prawitzKernel t‖) *
          (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (D / r ^ 3) *
          (Real.sqrt (n : ℝ) * (n : ℝ) / rho ^ 3) * H := by
            dsimp only [D, H, F, B]
            unfold scalarDiskDifference scalarU routeBUFrequency
            rw [hrouteR]
            field_simp [hrhoPos.ne', hrPos.ne']
      _ = (t * ‖prawitzKernel t‖) *
          (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (D / r ^ 3) * (1 / L ^ 3) * H := by
            rw [hscaleIdentity]
      _ = (t * ‖prawitzKernel t‖) *
          (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (D / (r ^ 3 * L ^ 3)) * H := by
            field_simp [hrPos.ne', hLPos.ne']
  calc
    (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ *
        scalarPowerDifference n rho (rho * (r - 1)) t ≤
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ *
        scalarDiskDifference n rho (rho * (r - 1)) t :=
          mul_le_mul_of_nonneg_left hscalar hscale0
    _ = (t * ‖prawitzKernel t‖) *
          (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (D / (r ^ 3 * L ^ 3)) * H := hrewrite
    _ ≤ k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (D / (r ^ 3 * L ^ 3)) * H := by
      have h1 := mul_le_mul_of_nonneg_right hk0 hfrequency0
      have h2 := mul_le_mul_of_nonneg_right h1 hDquot0
      exact mul_le_mul_of_nonneg_right h2 hH0
    _ ≤ k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (Dstar / (r ^ 3 * L ^ 3)) * H := by
      have hquot := div_le_div_of_nonneg_right hD hdenPos.le
      have hpref0 : 0 ≤ k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) :=
        mul_nonneg hk00 hfrequency0
      have h1 := mul_le_mul_of_nonneg_left hquot hpref0
      exact mul_le_mul_of_nonneg_right h1 hH0
    _ ≤ k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (Dstar / (r ^ 3 * L ^ 3)) * E := by
      exact mul_le_mul_of_nonneg_left hpower
        (mul_nonneg (mul_nonneg hk00 hfrequency0) hDstarQuot0)
    _ = largeDirectTelescopingReal L r t k0 := by rfl

theorem lawNormalizedDifferenceIntegrand_le_large_telescoping
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 100 ≤ n) {t k0 : ℝ}
    (hr : 19 / 10 ≤ symmetrizationRatio mu)
    (ht0 : 0 ≤ t) (hk0 : t * ‖prawitzKernel t‖ ≤ k0) :
    lawNormalizedDifferenceIntegrand n mu t ≤
      largeDirectTelescopingReal
        (routeBSmoothingScale n (thirdAbsoluteMoment mu))
        (symmetrizationRatio mu) t k0 := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  have hnOne : 1 ≤ n := by omega
  have hrho : 1 ≤ rho := by
    dsimp only [rho]
    exact thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hrUpper : r ≤ 1 + 1 / rho := by
    simpa only [rho, r] using symmetrizationRatio_upper mu hX hmean hsecond
  have hdiff : r - 1 ≤ 1 / rho := by linarith
  have hmul : rho * (r - 1) ≤ rho * (1 / rho) :=
    mul_le_mul_of_nonneg_left hdiff (zero_le_one.trans hrho)
  have hfeasible : rho * (r - 1) ≤ 1 := by
    have hcancel : rho * (1 / rho) = 1 := by field_simp
    linarith
  have henvelope := lawNormalizedDifferenceIntegrand_le_envelope
    mu hX hmean hsecond hnOne ht0
  have htel := scalar_normalizedDifference_le_large_telescoping
    hn hrho (by simpa only [r] using hr) hfeasible ht0 hk0
  exact henvelope.trans (by simpa only [rho, r] using htel)

/-- The unchanged Route B compact large-`n` envelope remains a valid second
branch for the sharper the first-absolute-moment bounds difference term.  It supplies the positive-`t`
trivial branch used by the exact cell minimum. -/
theorem lawNormalizedDifferenceIntegrand_le_large_old
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 100 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) :
    lawNormalizedDifferenceIntegrand n mu t ≤
      routeBLargeLowerDifferenceIntegrand
        (routeBSmoothingScale n (thirdAbsoluteMoment mu))
        (symmetrizationRatio mu) t := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  have hnOne : 1 ≤ n := by omega
  have hrho : 1 ≤ rho := by
    dsimp only [rho]
    exact thirdAbsoluteMoment_ge_one mu hX hsecond
  have hr : 1 ≤ r := by
    dsimp only [r]
    exact symmetrizationRatio_lower mu hX hmean hsecond
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hrPos : 0 < r := zero_lt_one.trans_le hr
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrhoPos.ne'
  have henvelope := lawNormalizedDifferenceIntegrand_le_envelope
    mu hX hmean hsecond hnOne ht0
  have hscalar := scalarPowerDifference_le_routeB n
    (rho := rho) (z := z) (t := t) hrhoPos
      (by rw [hrouteR]; exact hrPos) ht0
  have hscale : 0 ≤
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ := by
    positivity
  have hrouteScaled := mul_le_mul_of_nonneg_left hscalar hscale
  have hlarge := routeBNormalizedLowerDifference_le_largeIntegrand
    hn hrho hr ht0
  change lawNormalizedDifferenceIntegrand n mu t ≤
    routeBLargeLowerDifferenceIntegrand
      (routeBSmoothingScale n rho) r t
  exact henvelope.trans <| hrouteScaled.trans <| by
    simpa only [hrouteR] using hlarge

/-- The the first-absolute-moment bounds high-frequency law term is controlled by the already certified
compact large-`n` high-frequency envelope.  This step uses the the first-absolute-moment bounds scalar
modulus only through its proved domination by the Route B modulus. -/
theorem lawNormalizedHighIntegrand_le_large
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 100 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) :
    lawNormalizedHighIntegrand n mu t ≤
      routeBLargeHighIntegrand
        (routeBSmoothingScale n (thirdAbsoluteMoment mu))
        (symmetrizationRatio mu) t := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  have hrho : 1 ≤ rho := by
    dsimp only [rho]
    exact thirdAbsoluteMoment_ge_one mu hX hsecond
  have hr : 1 ≤ r := by
    dsimp only [r]
    exact symmetrizationRatio_lower mu hX hmean hsecond
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrhoPos.ne'
  have henvelope := lawNormalizedHighIntegrand_le_envelope
    mu hX hmean hsecond n ht0
  have hscalar := scalarPowerModulus_le_routeB n rho z t
  have hscale : 0 ≤
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ := by
    positivity
  have hrouteScaled := mul_le_mul_of_nonneg_left hscalar hscale
  have hlarge := routeBNormalizedHigh_le_largeIntegrand
    hn hrho hr ht0
  exact henvelope.trans <| hrouteScaled.trans <| by
    simpa only [hrouteR] using hlarge

/-- The Gaussian correction is unchanged by the first-absolute-moment bounds and therefore reduces
exactly to the compact large-`n` correction envelope from the baseline bound. -/
theorem lawNormalizedCorrectionIntegrand_le_large
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 100 ≤ n) {t : ℝ} :
    lawNormalizedCorrectionIntegrand n mu t ≤
      routeBLargeCorrectionIntegrand
        (routeBSmoothingScale n (thirdAbsoluteMoment mu))
        (symmetrizationRatio mu) t := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  have hrho : 1 ≤ rho := by
    dsimp only [rho]
    exact thirdAbsoluteMoment_ge_one mu hX hsecond
  have hr : 1 ≤ r := by
    dsimp only [r]
    exact symmetrizationRatio_lower mu hX hmean hsecond
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrhoPos.ne'
  have heq := congrFun
    (lawNormalizedCorrectionIntegrand_eq_routeB mu hX hsecond n) t
  have heq' : lawNormalizedCorrectionIntegrand n mu t =
      routeBNormalizedCorrectionIntegrand n rho z t := by
    simpa only [rho, r, z] using heq
  have hlarge := routeBNormalizedCorrection_le_largeIntegrand
    (t := t) hn hrho hr
  change lawNormalizedCorrectionIntegrand n mu t ≤
    routeBLargeCorrectionIntegrand (routeBSmoothingScale n rho) r t
  rw [heq']
  simpa only [routeBNormalizedCorrectionIntegrand, hrouteR] using hlarge

end

end BerryEsseen
