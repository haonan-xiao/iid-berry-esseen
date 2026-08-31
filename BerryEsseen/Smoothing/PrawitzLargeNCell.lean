import BerryEsseen.Smoothing.PrawitzLargeNIntegral
/-!
# Real semantics of the direct large-`n` cell evaluator

This module isolates the real formulas computed, with outward rounding, by the
supplied checker's `tail_direct` routine.  The parameter `hq` is a cellwise
lower bound for `(2 * pi * t)^2 q(2 * pi * t)`; the checker truncates its
quotient at zero before evaluating the exponential.
-/

namespace BerryEsseen

noncomputable section

def routeBLargeCellQLower (L r hq : ℝ) : ℝ :=
  max (hq / (r ^ 2 * L ^ 2)) 0

def routeBLargeCellM (L r hq : ℝ) : ℝ :=
  Real.exp (-routeBLargeCellQLower L r hq)

def routeBLargeCellN (L r v : ℝ) : ℝ :=
  Real.exp (-(v ^ 2 / (2 * (r ^ 2 * L ^ 2))))

def routeBLargeCellTelescoping
    (L r t k0 hq D : ℝ) : ℝ :=
  k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
    (D / (r ^ 3 * L ^ 3)) *
    Real.exp (-routeBLargeNAlpha * routeBLargeCellQLower L r hq)

def routeBLargeCellTrivial
    (L r t k0 hq v : ℝ) : ℝ :=
  2 * k0 *
    ((routeBLargeCellM L r hq + routeBLargeCellN L r v) / (t * L))

def routeBLargeCellF1
    (L r t k0 hq v D : ℝ) : ℝ :=
  min (routeBLargeCellTelescoping L r t k0 hq D)
    (routeBLargeCellTrivial L r t k0 hq v)

def routeBLargeCellF3 (L r kd2 v : ℝ) : ℝ :=
  kd2 * routeBLargeCellN L r v / L

def routeBLargeCellF2 (L r kh2 hq : ℝ) : ℝ :=
  kh2 * routeBLargeCellM L r hq / L

lemma routeBLargeCellQLower_nonneg (L r hq : ℝ) :
    0 ≤ routeBLargeCellQLower L r hq := by
  exact le_max_right _ _

lemma routeBLargeCellM_nonneg (L r hq : ℝ) :
    0 ≤ routeBLargeCellM L r hq := by
  exact (Real.exp_pos _).le

lemma routeBLargeCellN_nonneg (L r v : ℝ) :
    0 ≤ routeBLargeCellN L r v := by
  exact (Real.exp_pos _).le

/-- A checker cell's truncated lower exponent is no larger than the analytic
large-`n` exponent throughout that cell. -/
theorem routeBLargeCellQLower_le
    {L r t hq : ℝ} (hL : 0 < L) (hr : 0 < r) (ht : 0 ≤ t)
    (hhq : hq ≤ (2 * Real.pi * t) ^ 2 *
      routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t)) :
    routeBLargeCellQLower L r hq ≤ routeBLargeQ L r t := by
  have hden : 0 < r ^ 2 * L ^ 2 := mul_pos (sq_pos_of_pos hr) (sq_pos_of_pos hL)
  have hquot :
      hq / (r ^ 2 * L ^ 2) ≤
        ((2 * Real.pi * t) ^ 2 *
          routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t)) /
          (r ^ 2 * L ^ 2) :=
    div_le_div_of_nonneg_right hhq hden.le
  unfold routeBLargeCellQLower routeBLargeQ
  exact max_le hquot (routeBLargeQ_nonneg hL hr ht)

theorem routeBLargeExp_le_cellM
    {L r t hq : ℝ} (hL : 0 < L) (hr : 0 < r) (ht : 0 ≤ t)
    (hhq : hq ≤ (2 * Real.pi * t) ^ 2 *
      routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t)) :
    Real.exp (-routeBLargeQ L r t) ≤ routeBLargeCellM L r hq := by
  unfold routeBLargeCellM
  exact Real.exp_le_exp.mpr (neg_le_neg (routeBLargeCellQLower_le hL hr ht hhq))

theorem routeBLargeAlphaExp_le_cell
    {L r t hq : ℝ} (hL : 0 < L) (hr : 0 < r) (ht : 0 ≤ t)
    (hhq : hq ≤ (2 * Real.pi * t) ^ 2 *
      routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t)) :
    Real.exp (-routeBLargeNAlpha * routeBLargeQ L r t) ≤
      Real.exp (-routeBLargeNAlpha * routeBLargeCellQLower L r hq) := by
  apply Real.exp_le_exp.mpr
  have hq := routeBLargeCellQLower_le hL hr ht hhq
  nlinarith [routeBLargeNAlpha_nonneg]

theorem routeBLargeNormalEnvelope_eq_cellN
    (L r t : ℝ) :
    routeBLargeNormalEnvelope L r t =
      routeBLargeCellN L r (2 * Real.pi * t) := by
  unfold routeBLargeNormalEnvelope routeBLargeCellN
  congr 2
  ring

/-- The telescoping branch of the checker controls the first low-frequency
large-`n` integrand. -/
theorem routeBLargeLowerDifference_le_cellTelescoping
    {L r t k0 hq D : ℝ}
    (hL : 0 < L) (hr : 0 < r) (ht : 0 ≤ t)
    (hhq : hq ≤ (2 * Real.pi * t) ^ 2 *
      routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t))
    (hk0 : t * ‖prawitzKernel t‖ ≤ k0)
    (hD : routeBDiskStar r (2 * Real.pi * t / r) ≤ D) :
    routeBLargeLowerDifferenceIntegrand L r t ≤
      routeBLargeCellTelescoping L r t k0 hq D := by
  let first := ((2 * Real.pi * t) ^ 3 / (r ^ 3 * L ^ 2)) *
    routeBDiskStar r (2 * Real.pi * t / r) *
    Real.exp (-routeBLargeNAlpha * routeBLargeQ L r t)
  let second := Real.exp (-routeBLargeQ L r t) +
    routeBLargeNormalEnvelope L r t
  have hfactor : 0 ≤ 2 / L * ‖prawitzKernel t‖ :=
    mul_nonneg (div_nonneg (by norm_num) hL.le) (norm_nonneg _)
  have hbranch :
      2 / L * ‖prawitzKernel t‖ * min first second ≤
        2 / L * ‖prawitzKernel t‖ * first :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) hfactor
  have hrewrite :
      2 / L * ‖prawitzKernel t‖ * first =
        (t * ‖prawitzKernel t‖) *
          (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (routeBDiskStar r (2 * Real.pi * t / r) / (r ^ 3 * L ^ 3)) *
          Real.exp (-routeBLargeNAlpha * routeBLargeQ L r t) := by
    dsimp only [first]
    field_simp [hL.ne', hr.ne']
  have hB0 : 0 ≤ 2 * (t ^ 2 * (2 * Real.pi) ^ 3) := by positivity
  have hk00 : 0 ≤ k0 := (mul_nonneg ht (norm_nonneg _)).trans hk0
  have hden : 0 < r ^ 3 * L ^ 3 :=
    mul_pos (pow_pos hr 3) (pow_pos hL 3)
  have hDstar0 : 0 ≤ routeBDiskStar r (2 * Real.pi * t / r) :=
    routeBDiskStar_nonneg _ _
  have hD0 : 0 ≤ D := hDstar0.trans hD
  have hDisk :
      routeBDiskStar r (2 * Real.pi * t / r) / (r ^ 3 * L ^ 3) ≤
        D / (r ^ 3 * L ^ 3) :=
    div_le_div_of_nonneg_right hD hden.le
  have hDiskStar0 :
      0 ≤ routeBDiskStar r (2 * Real.pi * t / r) / (r ^ 3 * L ^ 3) :=
    div_nonneg hDstar0 hden.le
  have hDisk0 : 0 ≤ D / (r ^ 3 * L ^ 3) := div_nonneg hD0 hden.le
  have hExp := routeBLargeAlphaExp_le_cell hL hr ht hhq
  have hExp0 :
      0 ≤ Real.exp (-routeBLargeNAlpha * routeBLargeQ L r t) :=
    (Real.exp_pos _).le
  have hCellExp0 :
      0 ≤ Real.exp (-routeBLargeNAlpha * routeBLargeCellQLower L r hq) :=
    (Real.exp_pos _).le
  unfold routeBLargeLowerDifferenceIntegrand routeBLargeDifferenceEnvelope
  change 2 / L * ‖prawitzKernel t‖ * min first second ≤ _
  calc
    2 / L * ‖prawitzKernel t‖ * min first second ≤
        2 / L * ‖prawitzKernel t‖ * first := hbranch
    _ = (t * ‖prawitzKernel t‖) *
          (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (routeBDiskStar r (2 * Real.pi * t / r) / (r ^ 3 * L ^ 3)) *
          Real.exp (-routeBLargeNAlpha * routeBLargeQ L r t) := hrewrite
    _ ≤ k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (routeBDiskStar r (2 * Real.pi * t / r) / (r ^ 3 * L ^ 3)) *
          Real.exp (-routeBLargeNAlpha * routeBLargeQ L r t) := by
      have h1 := mul_le_mul_of_nonneg_right hk0 hB0
      have h2 := mul_le_mul_of_nonneg_right h1 hDiskStar0
      exact mul_le_mul_of_nonneg_right h2 hExp0
    _ ≤ k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (D / (r ^ 3 * L ^ 3)) *
          Real.exp (-routeBLargeNAlpha * routeBLargeQ L r t) := by
      have hpref : 0 ≤ k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) :=
        mul_nonneg hk00 hB0
      have h1 := mul_le_mul_of_nonneg_left hDisk hpref
      exact mul_le_mul_of_nonneg_right h1 hExp0
    _ ≤ k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (D / (r ^ 3 * L ^ 3)) *
          Real.exp (-routeBLargeNAlpha * routeBLargeCellQLower L r hq) := by
      exact mul_le_mul_of_nonneg_left hExp
        (mul_nonneg (mul_nonneg hk00 hB0) hDisk0)
    _ = routeBLargeCellTelescoping L r t k0 hq D := by
      rfl

/-- On a positive-frequency cell, the checker's direct `M + N` branch also
controls the first low-frequency integrand. -/
theorem routeBLargeLowerDifference_le_cellTrivial
    {L r t k0 hq : ℝ}
    (hL : 0 < L) (hr : 0 < r) (ht : 0 < t)
    (hhq : hq ≤ (2 * Real.pi * t) ^ 2 *
      routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t))
    (hk0 : t * ‖prawitzKernel t‖ ≤ k0) :
    routeBLargeLowerDifferenceIntegrand L r t ≤
      routeBLargeCellTrivial L r t k0 hq (2 * Real.pi * t) := by
  let first := ((2 * Real.pi * t) ^ 3 / (r ^ 3 * L ^ 2)) *
    routeBDiskStar r (2 * Real.pi * t / r) *
    Real.exp (-routeBLargeNAlpha * routeBLargeQ L r t)
  let second := Real.exp (-routeBLargeQ L r t) +
    routeBLargeNormalEnvelope L r t
  have hfactor : 0 ≤ 2 / L * ‖prawitzKernel t‖ :=
    mul_nonneg (div_nonneg (by norm_num) hL.le) (norm_nonneg _)
  have hbranch :
      2 / L * ‖prawitzKernel t‖ * min first second ≤
        2 / L * ‖prawitzKernel t‖ * second :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hfactor
  have hM := routeBLargeExp_le_cellM hL hr ht.le hhq
  have hN := routeBLargeNormalEnvelope_eq_cellN L r t
  have hsum : second ≤
      routeBLargeCellM L r hq + routeBLargeCellN L r (2 * Real.pi * t) := by
    dsimp only [second]
    exact add_le_add hM hN.le
  have hden : 0 < t * L := mul_pos ht hL
  have hrealSum0 : 0 ≤ second := by
    dsimp only [second]
    exact add_nonneg (Real.exp_pos _).le (routeBLargeNormalEnvelope_nonneg _ _ _)
  have hcellSum0 :
      0 ≤ routeBLargeCellM L r hq + routeBLargeCellN L r (2 * Real.pi * t) :=
    add_nonneg (routeBLargeCellM_nonneg _ _ _) (routeBLargeCellN_nonneg _ _ _)
  have hquot : second / (t * L) ≤
      (routeBLargeCellM L r hq + routeBLargeCellN L r (2 * Real.pi * t)) /
        (t * L) := div_le_div_of_nonneg_right hsum hden.le
  have hk00 : 0 ≤ k0 := (mul_nonneg ht.le (norm_nonneg _)).trans hk0
  have hrewrite :
      2 / L * ‖prawitzKernel t‖ * second =
        2 * (t * ‖prawitzKernel t‖) * (second / (t * L)) := by
    field_simp [hL.ne', ht.ne']
  unfold routeBLargeLowerDifferenceIntegrand routeBLargeDifferenceEnvelope
  change 2 / L * ‖prawitzKernel t‖ * min first second ≤ _
  calc
    2 / L * ‖prawitzKernel t‖ * min first second ≤
        2 / L * ‖prawitzKernel t‖ * second := hbranch
    _ = 2 * (t * ‖prawitzKernel t‖) * (second / (t * L)) := hrewrite
    _ ≤ 2 * k0 * (second / (t * L)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk0 (by norm_num))
        (div_nonneg hrealSum0 hden.le)
    _ ≤ 2 * k0 *
          ((routeBLargeCellM L r hq +
            routeBLargeCellN L r (2 * Real.pi * t)) / (t * L)) := by
      exact mul_le_mul_of_nonneg_left hquot (mul_nonneg (by norm_num) hk00)
    _ = routeBLargeCellTrivial L r t k0 hq (2 * Real.pi * t) := by
      rfl

theorem routeBLargeCorrection_le_cellF3
    {L r t kd2 : ℝ} (hL : 0 < L)
    (hkd2 : 2 * ‖prawitzKernelCorrection t‖ ≤ kd2) :
    routeBLargeCorrectionIntegrand L r t ≤
      routeBLargeCellF3 L r kd2 (2 * Real.pi * t) := by
  have hN := routeBLargeNormalEnvelope_eq_cellN L r t
  have hscale : 0 ≤ routeBLargeCellN L r (2 * Real.pi * t) / L :=
    div_nonneg (routeBLargeCellN_nonneg _ _ _) hL.le
  unfold routeBLargeCorrectionIntegrand routeBLargeCellF3
  rw [hN]
  calc
    2 / L * ‖prawitzKernelCorrection t‖ *
        routeBLargeCellN L r (2 * Real.pi * t) =
      (2 * ‖prawitzKernelCorrection t‖) *
        (routeBLargeCellN L r (2 * Real.pi * t) / L) := by ring
    _ ≤ kd2 * (routeBLargeCellN L r (2 * Real.pi * t) / L) :=
      mul_le_mul_of_nonneg_right hkd2 hscale
    _ = kd2 * routeBLargeCellN L r (2 * Real.pi * t) / L := by ring

theorem routeBLargeHigh_le_cellF2
    {L r t kh2 hq : ℝ}
    (hL : 0 < L) (hr : 0 < r) (ht : 0 ≤ t)
    (hhq : hq ≤ (2 * Real.pi * t) ^ 2 *
      routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t))
    (hkh2 : 2 * ‖prawitzKernel t‖ ≤ kh2) :
    routeBLargeHighIntegrand L r t ≤
      routeBLargeCellF2 L r kh2 hq := by
  have hM := routeBLargeExp_le_cellM hL hr ht hhq
  have hM0 : 0 ≤ Real.exp (-routeBLargeQ L r t) / L :=
    div_nonneg (Real.exp_pos _).le hL.le
  have hkh0 : 0 ≤ kh2 :=
    (mul_nonneg (by norm_num) (norm_nonneg _)).trans hkh2
  unfold routeBLargeHighIntegrand routeBLargeCellF2
  calc
    2 / L * ‖prawitzKernel t‖ * Real.exp (-routeBLargeQ L r t) =
      (2 * ‖prawitzKernel t‖) *
        (Real.exp (-routeBLargeQ L r t) / L) := by ring
    _ ≤ kh2 * (Real.exp (-routeBLargeQ L r t) / L) :=
      mul_le_mul_of_nonneg_right hkh2 hM0
    _ ≤ kh2 * (routeBLargeCellM L r hq / L) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hM hL.le) hkh0
    _ = kh2 * routeBLargeCellM L r hq / L := by ring

/-- The low-frequency split keeps the argument of `H` in the verified
`[0,3]` range used by `Dstar_bound`. -/
theorem routeBLargeDstar_y_le_three
    {r t : ℝ} (hr : 1 ≤ r) (ht0 : 0 ≤ t) (ht1 : t ≤ prawitzSplit) :
    ((2 * Real.pi * t) / r) ^ 2 / 2 ≤ 3 := by
  have hrPos : 0 < r := zero_lt_one.trans_le hr
  have hv0 : 0 ≤ 2 * Real.pi * t := by positivity
  have hvBound : 2 * Real.pi * t ≤ (2394 : ℝ) / 1000 := by
    have hpi := Real.pi_lt_d2
    norm_num [prawitzSplit] at ht1
    nlinarith
  have hc0 : 0 ≤ (2 * Real.pi * t) / r := div_nonneg hv0 hrPos.le
  have hcBound : (2 * Real.pi * t) / r ≤ (2394 : ℝ) / 1000 :=
    (div_le_self hv0 hr).trans hvBound
  have hcSq : ((2 * Real.pi * t) / r) ^ 2 ≤ ((2394 : ℝ) / 1000) ^ 2 :=
    (sq_le_sq₀ hc0 (by norm_num : (0 : ℝ) ≤ 2394 / 1000)).mpr hcBound
  norm_num at hcSq ⊢
  linarith

end

end BerryEsseen
