import BerryEsseen.Smoothing.PrawitzLargeNCell
import BerryEsseen.Smoothing.PrawitzKernelEnvelopes
/-!
# Endpoint-regular envelopes for the small-`L` large-`n` region

For `0 < L ≤ 1/16`, the direct large-`n` integrands are ill-conditioned as
functions of `L`, although their integrals have removable endpoint
singularities.  This module begins the analytic change of variables used by
the supplied numerical lemma: `t = L*y` at the lower endpoint and
`t = 1 - L*y` at the upper endpoint.

The two quantities below are the exact real semantics of the exponent lower
bounds used by `tail_small`.  Their soundness is proved against
`routeBLargeQ`; later dyadic cells may therefore use them without assuming a
floating-point endpoint limit.
-/

namespace BerryEsseen

noncomputable section

/-- Alternating lower polynomial for `(1 - cos x) / x^2`, continued at
`x = 0`.  Multiplying it by `x^2` gives
`prawitzCosineLossTaylor12 x`. -/
def routeBSmallCosineRatioLower (x : ℝ) : ℝ :=
  (1 : ℝ) / 2 - x ^ 2 / 24 + x ^ 4 / 720 - x ^ 6 / 40320 +
    x ^ 8 / 3628800 - x ^ 10 / 479001600

lemma routeBSmallCosineRatioLower_mul_sq (x : ℝ) :
    x ^ 2 * routeBSmallCosineRatioLower x =
      prawitzCosineLossTaylor12 x := by
  unfold routeBSmallCosineRatioLower prawitzCosineLossTaylor12
  ring

/-- Lower exponent after `t = L*y` on the low-frequency side.  The maximum
with zero mirrors the checker's `max0` and remains a lower bound because the
true Route B exponent is nonnegative. -/
def routeBLargeSmallLowQ (L r y : ℝ) : ℝ :=
  max
    (((2 * Real.pi * y) ^ 2 *
        ((1 : ℝ) / 2 - routeBKappaUpper * (2 * Real.pi * L * y))) /
      r ^ 2)
    0

/-- Lower exponent after `t = 1 - L*y` on the high-frequency side. -/
def routeBLargeSmallHighQ (L r y : ℝ) : ℝ :=
  max
    (((2 * Real.pi * y) ^ 2 *
        routeBSmallCosineRatioLower (2 * Real.pi * L * y)) /
      r ^ 2)
    0

def routeBLargeSmallLowHQ (L y : ℝ) : ℝ :=
  (2 * Real.pi * (L * y)) ^ 2 *
    ((1 : ℝ) / 2 - routeBKappaUpper * (2 * Real.pi * (L * y)))

def routeBLargeSmallHighHQ (L y : ℝ) : ℝ :=
  prawitzCosineLossTaylor12 (2 * Real.pi * L * y)

/-- Compact low-frequency endpoint integrand corresponding to the
telescoping branch after `t = L*y`. -/
def routeBLargeSmallF1 (L r y : ℝ) : ℝ :=
  (8 * Real.pi ^ 2 / r ^ 3) * y ^ 2 *
    (2 * Real.pi * prawitzK0Envelope (L * y)) *
    routeBDiskStar r (2 * Real.pi * L * y / r) *
    Real.exp (-routeBLargeNAlpha * routeBLargeSmallLowQ L r y)

/-- Compact Gaussian correction after `t = L*y`. -/
def routeBLargeSmallF3 (L r y : ℝ) : ℝ :=
  prawitzKD2Envelope (L * y) *
    Real.exp (-((2 * Real.pi * y) ^ 2 / (2 * r ^ 2)))

/-- Compact high-frequency endpoint integrand after `t = 1 - L*y`. -/
def routeBLargeSmallF2 (L r y : ℝ) : ℝ :=
  prawitzKH2Envelope (1 - L * y) *
    Real.exp (-routeBLargeSmallHighQ L r y)

def routeBLargeSmallLowIntegrand (L r y : ℝ) : ℝ :=
  routeBLargeSmallF1 L r y + routeBLargeSmallF3 L r y

def routeBLargeSmallIntegrand (L r y : ℝ) : ℝ :=
  routeBLargeSmallLowIntegrand L r y + routeBLargeSmallF2 L r y

lemma routeBLargeSmallLowQ_nonneg (L r y : ℝ) :
    0 ≤ routeBLargeSmallLowQ L r y := by
  exact le_max_right _ _

lemma routeBLargeSmallHighQ_nonneg (L r y : ℝ) :
    0 ≤ routeBLargeSmallHighQ L r y := by
  exact le_max_right _ _

lemma routeBLargeCellQLower_smallLow_eq
    {L r y : ℝ} (hL : 0 < L) (hr : 0 < r) :
    routeBLargeCellQLower L r (routeBLargeSmallLowHQ L y) =
      routeBLargeSmallLowQ L r y := by
  unfold routeBLargeCellQLower routeBLargeSmallLowHQ routeBLargeSmallLowQ
  congr 1
  field_simp [hL.ne', hr.ne']

lemma routeBLargeCellQLower_smallHigh_eq
    {L r y : ℝ} (hL : 0 < L) (hr : 0 < r) :
    routeBLargeCellQLower L r (routeBLargeSmallHighHQ L y) =
      routeBLargeSmallHighQ L r y := by
  unfold routeBLargeCellQLower routeBLargeSmallHighHQ routeBLargeSmallHighQ
  rw [← routeBSmallCosineRatioLower_mul_sq]
  congr 1
  field_simp [hL.ne', hr.ne']

/-- The low-frequency endpoint-regular exponent is below the exact direct
large-`n` exponent. -/
theorem routeBLargeSmallLowQ_le
    {L r y : ℝ} (hL : 0 < L) (hLupper : L ≤ 1 / 16)
    (hr : 0 < r) (hy0 : 0 ≤ y) (hy4 : y ≤ 4) :
    routeBLargeSmallLowQ L r y ≤ routeBLargeQ L r (L * y) := by
  have ht0 : 0 ≤ L * y := mul_nonneg hL.le hy0
  have ht1 : L * y ≤ 1 := by
    nlinarith [mul_le_mul hLupper hy4 hy0 (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have hhq := prawitzHQLowBranch_le
    (t := L * y) ht0 ht1
  have hden : 0 < r ^ 2 * L ^ 2 := mul_pos (sq_pos_of_pos hr) (sq_pos_of_pos hL)
  have hraw :
      ((2 * Real.pi * y) ^ 2 *
          ((1 : ℝ) / 2 - routeBKappaUpper * (2 * Real.pi * L * y))) /
          r ^ 2 ≤
        routeBLargeQ L r (L * y) := by
    unfold routeBLargeQ
    rw [show
      ((2 * Real.pi * y) ^ 2 *
          ((1 : ℝ) / 2 - routeBKappaUpper * (2 * Real.pi * L * y))) /
          r ^ 2 =
        ((2 * Real.pi * (L * y)) ^ 2 *
          ((1 : ℝ) / 2 - routeBKappaUpper * (2 * Real.pi * (L * y)))) /
          (r ^ 2 * L ^ 2) by
        field_simp [hL.ne', hr.ne']]
    exact div_le_div_of_nonneg_right hhq hden.le
  unfold routeBLargeSmallLowQ
  exact max_le hraw (routeBLargeQ_nonneg hL hr ht0)

/-- The high-frequency endpoint-regular exponent is below the exact direct
large-`n` exponent. -/
theorem routeBLargeSmallHighQ_le
    {L r y : ℝ} (hL : 0 < L) (hLupper : L ≤ 1 / 16)
    (hr : 0 < r) (hy0 : 0 ≤ y) (hy4 : y ≤ 4) :
    routeBLargeSmallHighQ L r y ≤
      routeBLargeQ L r (1 - L * y) := by
  have hLy0 : 0 ≤ L * y := mul_nonneg hL.le hy0
  have hLyQuarter : L * y ≤ 1 / 4 := by
    nlinarith [mul_le_mul hLupper hy4 hy0 (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have ht0 : 0 ≤ 1 - L * y := by linarith
  have ht1 : 1 - L * y ≤ 1 := by linarith
  have hv4 : 4 ≤ 2 * Real.pi * (1 - L * y) := by
    nlinarith [Real.pi_gt_three]
  have hhq := prawitzHQHighBranch_le
    (t := 1 - L * y) ht1 hv4
  have hrewrite :
      prawitzCosineLossTaylor12
          (2 * Real.pi * (1 - (1 - L * y))) =
        (2 * Real.pi * L * y) ^ 2 *
          routeBSmallCosineRatioLower (2 * Real.pi * L * y) := by
    have hx : 2 * Real.pi * (1 - (1 - L * y)) =
        2 * Real.pi * L * y := by ring
    rw [hx, routeBSmallCosineRatioLower_mul_sq]
  rw [hrewrite] at hhq
  have hden : 0 < r ^ 2 * L ^ 2 := mul_pos (sq_pos_of_pos hr) (sq_pos_of_pos hL)
  have hraw :
      ((2 * Real.pi * y) ^ 2 *
          routeBSmallCosineRatioLower (2 * Real.pi * L * y)) /
          r ^ 2 ≤
        routeBLargeQ L r (1 - L * y) := by
    unfold routeBLargeQ
    rw [show
      ((2 * Real.pi * y) ^ 2 *
          routeBSmallCosineRatioLower (2 * Real.pi * L * y)) /
          r ^ 2 =
        ((2 * Real.pi * L * y) ^ 2 *
          routeBSmallCosineRatioLower (2 * Real.pi * L * y)) /
          (r ^ 2 * L ^ 2) by
        field_simp [hL.ne', hr.ne']]
    exact div_le_div_of_nonneg_right hhq hden.le
  unfold routeBLargeSmallHighQ
  exact max_le hraw (routeBLargeQ_nonneg hL hr ht0)

/-- The Gaussian term loses all dependence on `L` after `t = L*y`. -/
lemma routeBLargeNormalEnvelope_mul_scale
    {L r y : ℝ} (hL : 0 < L) (hr : 0 < r) :
    routeBLargeNormalEnvelope L r (L * y) =
      Real.exp (-((2 * Real.pi * y) ^ 2 / (2 * r ^ 2))) := by
  unfold routeBLargeNormalEnvelope
  congr 2
  field_simp [hL.ne', hr.ne']

/-- The factor `L` from `dt = L dy` cancels the apparent lower-endpoint
singularity in the telescoping branch. -/
theorem routeBLargeLowerDifference_mul_scale_le_smallF1
    {L r y : ℝ} (hL : 0 < L) (hLupper : L ≤ 1 / 16)
    (hr : 0 < r) (hy0 : 0 ≤ y) (hy4 : y ≤ 4) :
    L * routeBLargeLowerDifferenceIntegrand L r (L * y) ≤
      routeBLargeSmallF1 L r y := by
  have hLy0 : 0 ≤ L * y := mul_nonneg hL.le hy0
  have hLyQuarter : L * y ≤ 1 / 4 := by
    nlinarith [mul_le_mul hLupper hy4 hy0 (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have hLyOne : L * y < 1 := lt_of_le_of_lt hLyQuarter (by norm_num)
  have hhq : routeBLargeSmallLowHQ L y ≤
      (2 * Real.pi * (L * y)) ^ 2 *
        routeBMinorant routeBKappa routeBTheta (2 * Real.pi * (L * y)) := by
    simpa [routeBLargeSmallLowHQ] using
      prawitzHQLowBranch_le (t := L * y) hLy0 hLyOne.le
  have hk0 : L * y * ‖prawitzKernel (L * y)‖ ≤
      prawitzK0Envelope (L * y) :=
    t_mul_norm_prawitzKernel_le_K0Envelope hLy0 hLyOne
  have hbase := routeBLargeLowerDifference_le_cellTelescoping
    hL hr hLy0 hhq hk0
      (show routeBDiskStar r (2 * Real.pi * (L * y) / r) ≤
        routeBDiskStar r (2 * Real.pi * (L * y) / r) from le_rfl)
  have hscaled := mul_le_mul_of_nonneg_left hbase hL.le
  calc
    L * routeBLargeLowerDifferenceIntegrand L r (L * y) ≤
        L * routeBLargeCellTelescoping L r (L * y)
          (prawitzK0Envelope (L * y)) (routeBLargeSmallLowHQ L y)
          (routeBDiskStar r (2 * Real.pi * (L * y) / r)) := hscaled
    _ = routeBLargeSmallF1 L r y := by
      unfold routeBLargeCellTelescoping routeBLargeSmallF1
      rw [routeBLargeCellQLower_smallLow_eq hL hr]
      field_simp [hL.ne', hr.ne'] <;> ring

/-- The Gaussian correction is endpoint-regular after the same substitution. -/
theorem routeBLargeCorrection_mul_scale_le_smallF3
    {L r y : ℝ} (hL : 0 < L) (hLupper : L ≤ 1 / 16)
    (hr : 0 < r) (hy0 : 0 ≤ y) (hy4 : y ≤ 4) :
    L * routeBLargeCorrectionIntegrand L r (L * y) ≤
      routeBLargeSmallF3 L r y := by
  have hLy0 : 0 ≤ L * y := mul_nonneg hL.le hy0
  have hLyQuarter : L * y ≤ 1 / 4 := by
    nlinarith [mul_le_mul hLupper hy4 hy0 (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have hLyOne : L * y < 1 := lt_of_le_of_lt hLyQuarter (by norm_num)
  have hkernel : 2 * ‖prawitzKernelCorrection (L * y)‖ ≤
      prawitzKD2Envelope (L * y) :=
    two_mul_norm_prawitzKernelCorrection_le_KD2Envelope hLy0 hLyOne
  have hbase := routeBLargeCorrection_le_cellF3 (r := r) hL hkernel
  have hscaled := mul_le_mul_of_nonneg_left hbase hL.le
  calc
    L * routeBLargeCorrectionIntegrand L r (L * y) ≤
        L * routeBLargeCellF3 L r (prawitzKD2Envelope (L * y))
          (2 * Real.pi * (L * y)) := hscaled
    _ = routeBLargeSmallF3 L r y := by
      unfold routeBLargeCellF3 routeBLargeSmallF3
      rw [← routeBLargeNormalEnvelope_eq_cellN,
        routeBLargeNormalEnvelope_mul_scale hL hr]
      field_simp [hL.ne']

/-- The factor `L` also cancels at the high-frequency endpoint after
`t = 1 - L*y`. -/
theorem routeBLargeHigh_mul_scale_le_smallF2
    {L r y : ℝ} (hL : 0 < L) (hLupper : L ≤ 1 / 16)
    (hr : 0 < r) (hy0 : 0 ≤ y) (hy4 : y ≤ 4) :
    L * routeBLargeHighIntegrand L r (1 - L * y) ≤
      routeBLargeSmallF2 L r y := by
  have hLy0 : 0 ≤ L * y := mul_nonneg hL.le hy0
  have hLyQuarter : L * y ≤ 1 / 4 := by
    nlinarith [mul_le_mul hLupper hy4 hy0 (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have htPos : 0 < 1 - L * y := by linarith
  have htOne : 1 - L * y ≤ 1 := by linarith
  have hv4 : 4 ≤ 2 * Real.pi * (1 - L * y) := by
    nlinarith [Real.pi_gt_three]
  have hhqRaw := prawitzHQHighBranch_le
    (t := 1 - L * y) htOne hv4
  have hhq : routeBLargeSmallHighHQ L y ≤
      (2 * Real.pi * (1 - L * y)) ^ 2 *
        routeBMinorant routeBKappa routeBTheta
          (2 * Real.pi * (1 - L * y)) := by
    convert hhqRaw using 1 <;> simp [routeBLargeSmallHighHQ] <;> ring
  have hkernel : 2 * ‖prawitzKernel (1 - L * y)‖ ≤
      prawitzKH2Envelope (1 - L * y) :=
    two_mul_norm_prawitzKernel_le_KH2Envelope htPos htOne
  have hbase := routeBLargeHigh_le_cellF2 hL hr htPos.le hhq hkernel
  have hscaled := mul_le_mul_of_nonneg_left hbase hL.le
  calc
    L * routeBLargeHighIntegrand L r (1 - L * y) ≤
        L * routeBLargeCellF2 L r (prawitzKH2Envelope (1 - L * y))
          (routeBLargeSmallHighHQ L y) := hscaled
    _ = routeBLargeSmallF2 L r y := by
      unfold routeBLargeCellF2 routeBLargeCellM routeBLargeSmallF2
      rw [routeBLargeCellQLower_smallHigh_eq hL hr]
      field_simp [hL.ne']

/-- The compact lower-endpoint integrand controls the original normalized
finite-`n` low-frequency integrand after `t = L*y`. -/
theorem routeBNormalizedLow_mul_scale_le_largeSmallLow
    {n : ℕ} (hn : 100 ≤ n) {rho z y : ℝ}
    (hrho1 : 1 ≤ rho) (hz0 : 0 ≤ z)
    (hLupper : routeBSmoothingScale n rho ≤ 1 / 16)
    (hy0 : 0 ≤ y) (hy4 : y ≤ 4) :
    routeBSmoothingScale n rho *
        routeBNormalizedLowIntegrand n rho z
          (routeBSmoothingScale n rho * y) ≤
      routeBLargeSmallLowIntegrand (routeBSmoothingScale n rho)
        (routeBDboundR rho z) y := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  let L := routeBSmoothingScale n rho
  let r := routeBDboundR rho z
  have hL : 0 < L := routeBSmoothingScale_pos hnPos hrhoPos
  have hr1 : 1 ≤ r := by
    dsimp only [r]
    rw [routeBDboundR_eq_one_add hrhoPos.ne']
    have hzdiv : 0 ≤ z / rho := div_nonneg hz0 hrhoPos.le
    linarith
  have hr : 0 < r := zero_lt_one.trans_le hr1
  have ht0 : 0 ≤ L * y := mul_nonneg hL.le hy0
  have hdiff := routeBNormalizedLowerDifference_le_largeIntegrand
    (rho := rho) (r := r) (t := L * y) hn hrho1 hr1 ht0
  have hcorr := routeBNormalizedCorrection_le_largeIntegrand
    (rho := rho) (r := r) (t := L * y) hn hrho1 hr1
  have hdiff' : routeBNormalizedLowerDifferenceIntegrand n rho z (L * y) ≤
      routeBLargeLowerDifferenceIntegrand L r (L * y) := by
    simpa [routeBNormalizedLowerDifferenceIntegrand, L, r] using hdiff
  have hcorr' : routeBNormalizedCorrectionIntegrand n rho z (L * y) ≤
      routeBLargeCorrectionIntegrand L r (L * y) := by
    simpa [routeBNormalizedCorrectionIntegrand, L, r] using hcorr
  have hdiffScaled := mul_le_mul_of_nonneg_left hdiff' hL.le
  have hcorrScaled := mul_le_mul_of_nonneg_left hcorr' hL.le
  have hsmallDiff := routeBLargeLowerDifference_mul_scale_le_smallF1
    hL (by simpa only [L] using hLupper) hr hy0 hy4
  have hsmallCorr := routeBLargeCorrection_mul_scale_le_smallF3
    hL (by simpa only [L] using hLupper) hr hy0 hy4
  have hadd := add_le_add hdiffScaled hcorrScaled
  have hsmallAdd := add_le_add hsmallDiff hsmallCorr
  unfold routeBNormalizedLowIntegrand routeBLargeSmallLowIntegrand
  dsimp only [L, r] at hadd hsmallAdd ⊢
  calc
    routeBSmoothingScale n rho *
        (routeBNormalizedLowerDifferenceIntegrand n rho z
          (routeBSmoothingScale n rho * y) +
        routeBNormalizedCorrectionIntegrand n rho z
          (routeBSmoothingScale n rho * y)) =
      routeBSmoothingScale n rho *
          routeBNormalizedLowerDifferenceIntegrand n rho z
            (routeBSmoothingScale n rho * y) +
        routeBSmoothingScale n rho *
          routeBNormalizedCorrectionIntegrand n rho z
            (routeBSmoothingScale n rho * y) := by ring
    _ ≤ routeBSmoothingScale n rho *
          routeBLargeLowerDifferenceIntegrand (routeBSmoothingScale n rho)
            (routeBDboundR rho z) (routeBSmoothingScale n rho * y) +
        routeBSmoothingScale n rho *
          routeBLargeCorrectionIntegrand (routeBSmoothingScale n rho)
            (routeBDboundR rho z) (routeBSmoothingScale n rho * y) := hadd
    _ ≤ routeBLargeSmallF1 (routeBSmoothingScale n rho)
          (routeBDboundR rho z) y +
        routeBLargeSmallF3 (routeBSmoothingScale n rho)
          (routeBDboundR rho z) y := by
      exact hsmallAdd

/-- The compact upper-endpoint integrand controls the original normalized
finite-`n` high-frequency integrand after `t = 1 - L*y`. -/
theorem routeBNormalizedHigh_mul_scale_le_largeSmallF2
    {n : ℕ} (hn : 100 ≤ n) {rho z y : ℝ}
    (hrho1 : 1 ≤ rho) (hz0 : 0 ≤ z)
    (hLupper : routeBSmoothingScale n rho ≤ 1 / 16)
    (hy0 : 0 ≤ y) (hy4 : y ≤ 4) :
    routeBSmoothingScale n rho *
        routeBNormalizedHighIntegrand n rho z
          (1 - routeBSmoothingScale n rho * y) ≤
      routeBLargeSmallF2 (routeBSmoothingScale n rho)
        (routeBDboundR rho z) y := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  let L := routeBSmoothingScale n rho
  let r := routeBDboundR rho z
  have hL : 0 < L := routeBSmoothingScale_pos hnPos hrhoPos
  have hr1 : 1 ≤ r := by
    dsimp only [r]
    rw [routeBDboundR_eq_one_add hrhoPos.ne']
    have hzdiv : 0 ≤ z / rho := div_nonneg hz0 hrhoPos.le
    linarith
  have hr : 0 < r := zero_lt_one.trans_le hr1
  have hLyQuarter : L * y ≤ 1 / 4 := by
    have hLu : L ≤ 1 / 16 := by simpa only [L] using hLupper
    nlinarith [mul_le_mul hLu hy4 hy0 (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have ht0 : 0 ≤ 1 - L * y := by linarith
  have hlarge := routeBNormalizedHigh_le_largeIntegrand
    (rho := rho) (r := r) (t := 1 - L * y) hn hrho1 hr1 ht0
  have hlarge' : routeBNormalizedHighIntegrand n rho z (1 - L * y) ≤
      routeBLargeHighIntegrand L r (1 - L * y) := by
    simpa [routeBNormalizedHighIntegrand, L, r] using hlarge
  have hlargeScaled := mul_le_mul_of_nonneg_left hlarge' hL.le
  have hsmall := routeBLargeHigh_mul_scale_le_smallF2
    hL (by simpa only [L] using hLupper) hr hy0 hy4
  dsimp only [L, r] at hlargeScaled hsmall ⊢
  exact hlargeScaled.trans hsmall

end

end BerryEsseen
