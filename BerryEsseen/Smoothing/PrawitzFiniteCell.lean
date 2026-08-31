import BerryEsseen.Smoothing.ExplicitSmoothing
import BerryEsseen.Smoothing.PrawitzHQLower
import BerryEsseen.Smoothing.PrawitzDbound
/-!
# Real semantics of the Route B finite-cell evaluator

The exact checker evaluates the three finite parts of `routeBU` after multiplying by
`sqrt n / rho`.  This module isolates its real-valued cell formulas.  The cell data consist of
an upper bound for each relevant Prawitz-kernel norm, a lower bound for
`(2 * pi * t)^2 q(2 * pi * t)`, and an upper bound for the one-step disk radius.  Later dyadic
modules only have to prove that their outward-rounded operations enclose these formulas.
-/

open scoped NNReal Real

namespace BerryEsseen

noncomputable section

def routeBCellV (t : ℝ) : ℝ := 2 * Real.pi * t

def routeBCellA (rho z hq : ℝ) : ℝ :=
  Real.sqrt (max (1 - 2 * hq / routeBDboundW rho z ^ 2) 0)

def routeBCellB (rho z t : ℝ) : ℝ :=
  Real.exp (-(routeBCellV t) ^ 2 / (2 * routeBDboundW rho z ^ 2))

def routeBCellN (n : ℕ) (rho z t : ℝ) : ℝ :=
  Real.exp (-(n : ℝ) * (routeBCellV t) ^ 2 /
    (2 * routeBDboundW rho z ^ 2))

def routeBCellH (n : ℕ) (rho z t hq : ℝ) : ℝ :=
  max (routeBCellA rho z hq) (routeBCellB rho z t) ^ (n - 1)

/-- The telescoping branch of the normalized low-frequency first integrand. -/
def routeBCellTelescopingBound
    (n : ℕ) (rho z t k0 hq D : ℝ) : ℝ :=
  2 * (n : ℝ) * Real.sqrt (n : ℝ) * k0 *
    (t ^ 2 * (2 * Real.pi) ^ 3) *
    (D / routeBDboundW rho z ^ 3) *
    routeBCellH n rho z t hq

/-- The direct `M + N` branch of the normalized low-frequency first integrand. -/
def routeBCellTrivialBound
    (n : ℕ) (rho z t k0 hq : ℝ) : ℝ :=
  2 * Real.sqrt (n : ℝ) * routeBDboundP rho * k0 *
    ((routeBCellA rho z hq ^ n + routeBCellN n rho z t) / t)

def routeBCellLowerDifferenceBound
    (n : ℕ) (rho z t k0 hq D : ℝ) : ℝ :=
  min (routeBCellTelescopingBound n rho z t k0 hq D)
    (routeBCellTrivialBound n rho z t k0 hq)

/-- The normalized low-frequency kernel-correction integrand. -/
def routeBCellCorrectionBound
    (n : ℕ) (rho z t kd2 : ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * routeBDboundP rho * kd2 * routeBCellN n rho z t

/-- The normalized high-frequency Prawitz-kernel integrand. -/
def routeBCellHighBound
    (n : ℕ) (rho z t kh2 hq : ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * routeBDboundP rho * kh2 *
    routeBCellA rho z hq ^ n

def routeBNormalizedLowerDifferenceIntegrand
    (n : ℕ) (rho z t : ℝ) : ℝ :=
  2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖ *
    routeBPowerDifferenceEnvelope routeBKappa routeBTheta n rho
      (routeBDboundR rho z) t

def routeBNormalizedCorrectionIntegrand
    (n : ℕ) (rho z t : ℝ) : ℝ :=
  2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernelCorrection t‖ *
    routeBPowerGaussianEnvelope n rho (routeBDboundR rho z) t

def routeBNormalizedLowIntegrand
    (n : ℕ) (rho z t : ℝ) : ℝ :=
  routeBNormalizedLowerDifferenceIntegrand n rho z t +
    routeBNormalizedCorrectionIntegrand n rho z t

def routeBNormalizedHighIntegrand
    (n : ℕ) (rho z t : ℝ) : ℝ :=
  2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖ *
    routeBPowerModulusEnvelope routeBKappa routeBTheta n rho
      (routeBDboundR rho z) t

theorem routeBCell_frequency_identity {rho z t : ℝ} (hrho : 0 < rho) :
    routeBUFrequency rho (routeBDboundR rho z) t =
      routeBCellV t / routeBDboundW rho z := by
  unfold routeBUFrequency routeBDboundR routeBCellV
  field_simp [hrho.ne']

theorem routeBCell_modulus_le {rho z t hq : ℝ}
    (hrho : 0 < rho) (hw : 0 < routeBDboundW rho z)
    (hhq : hq ≤ routeBCellV t ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV t)) :
    routeBModulusEnvelope routeBKappa routeBTheta rho
        (routeBDboundR rho z) t ≤
      routeBCellA rho z hq := by
  have hfreq := routeBCell_frequency_identity (rho := rho) (z := z) (t := t) hrho
  have hdiv :
      2 * hq / routeBDboundW rho z ^ 2 ≤
        2 * (routeBCellV t ^ 2 *
          routeBMinorant routeBKappa routeBTheta (routeBCellV t)) /
          routeBDboundW rho z ^ 2 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhq (by norm_num))
      (sq_nonneg _)
  unfold routeBModulusEnvelope routeBCellA
  rw [hfreq]
  apply Real.sqrt_le_sqrt
  apply max_le_max_right
  dsimp only [routeBCellV]
  have hrewrite :
      2 * (2 * Real.pi * t / routeBDboundW rho z) ^ 2 *
          routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t) =
        2 * ((2 * Real.pi * t) ^ 2 *
          routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t)) /
          routeBDboundW rho z ^ 2 := by
    field_simp [hw.ne']
  rw [hrewrite]
  dsimp only [routeBCellV] at hdiv
  linarith

theorem routeBCell_gaussian_eq {rho z t : ℝ} (hrho : 0 < rho) :
    routeBGaussianEnvelope rho (routeBDboundR rho z) t =
      routeBCellB rho z t := by
  unfold routeBGaussianEnvelope routeBCellB
  rw [routeBCell_frequency_identity hrho]
  ring_nf

theorem routeBCell_powerGaussian_eq {n : ℕ} {rho z t : ℝ}
    (hrho : 0 < rho) :
    routeBPowerGaussianEnvelope n rho (routeBDboundR rho z) t =
      routeBCellN n rho z t := by
  rw [routeBPowerGaussianEnvelope, routeBCell_gaussian_eq hrho]
  unfold routeBCellN routeBCellB
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem routeBCell_powerModulus_le {n : ℕ} {rho z t hq : ℝ}
    (hrho : 0 < rho) (hw : 0 < routeBDboundW rho z)
    (hhq : hq ≤ routeBCellV t ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV t)) :
    routeBPowerModulusEnvelope routeBKappa routeBTheta n rho
        (routeBDboundR rho z) t ≤
      routeBCellA rho z hq ^ n := by
  unfold routeBPowerModulusEnvelope
  exact pow_le_pow_left₀
    (routeBModulusEnvelope_nonneg _ _ _ _ _)
    (routeBCell_modulus_le hrho hw hhq) n

theorem routeBCell_maxPower_le {n : ℕ} {rho z t hq : ℝ}
    (hrho : 0 < rho) (hw : 0 < routeBDboundW rho z)
    (hhq : hq ≤ routeBCellV t ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV t)) :
    max (routeBModulusEnvelope routeBKappa routeBTheta rho
          (routeBDboundR rho z) t)
        (routeBGaussianEnvelope rho (routeBDboundR rho z) t) ^ (n - 1) ≤
      routeBCellH n rho z t hq := by
  unfold routeBCellH
  apply pow_le_pow_left₀
  · exact (routeBModulusEnvelope_nonneg _ _ _ _ _).trans (le_max_left _ _)
  · apply max_le_max
    · exact routeBCell_modulus_le hrho hw hhq
    · exact (routeBCell_gaussian_eq hrho).le

theorem routeBNormalizedCorrectionIntegrand_le_cell
    {n : ℕ} {rho z t kd2 : ℝ}
    (hrho : 0 < rho)
    (hkd2 : 2 * ‖prawitzKernelCorrection t‖ ≤ kd2) :
    routeBNormalizedCorrectionIntegrand n rho z t ≤
      routeBCellCorrectionBound n rho z t kd2 := by
  have hN := routeBCell_powerGaussian_eq (n := n) (rho := rho) (z := z) (t := t) hrho
  have hscale :
      0 ≤ Real.sqrt (n : ℝ) * (1 / rho) * routeBCellN n rho z t := by
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
      (Real.exp_pos _).le
  unfold routeBNormalizedCorrectionIntegrand routeBCellCorrectionBound routeBDboundP
  rw [hN]
  calc
    2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernelCorrection t‖ *
        routeBCellN n rho z t =
      (Real.sqrt (n : ℝ) * (1 / rho) * routeBCellN n rho z t) *
        (2 * ‖prawitzKernelCorrection t‖) := by ring
    _ ≤ (Real.sqrt (n : ℝ) * (1 / rho) * routeBCellN n rho z t) * kd2 :=
      mul_le_mul_of_nonneg_left hkd2 hscale
    _ = Real.sqrt (n : ℝ) * (1 / rho) * kd2 *
        routeBCellN n rho z t := by ring

theorem routeBNormalizedHighIntegrand_le_cell
    {n : ℕ} {rho z t kh2 hq : ℝ}
    (hrho : 0 < rho) (hw : 0 < routeBDboundW rho z)
    (hhq : hq ≤ routeBCellV t ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV t))
    (hkh2 : 2 * ‖prawitzKernel t‖ ≤ kh2) :
    routeBNormalizedHighIntegrand n rho z t ≤
      routeBCellHighBound n rho z t kh2 hq := by
  have hM := routeBCell_powerModulus_le (n := n) hrho hw hhq
  have hscale : 0 ≤ Real.sqrt (n : ℝ) * (1 / rho) :=
    mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hkh0 : 0 ≤ kh2 :=
    (mul_nonneg (by norm_num) (norm_nonneg _)).trans hkh2
  have hM0 : 0 ≤ routeBPowerModulusEnvelope routeBKappa routeBTheta n rho
      (routeBDboundR rho z) t :=
    routeBPowerModulusEnvelope_nonneg _ _ _ _ _ _
  unfold routeBNormalizedHighIntegrand routeBCellHighBound routeBDboundP
  calc
    2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖ *
        routeBPowerModulusEnvelope routeBKappa routeBTheta n rho
          (routeBDboundR rho z) t =
      (Real.sqrt (n : ℝ) * (1 / rho)) *
        (2 * ‖prawitzKernel t‖) *
        routeBPowerModulusEnvelope routeBKappa routeBTheta n rho
          (routeBDboundR rho z) t := by ring
    _ ≤ (Real.sqrt (n : ℝ) * (1 / rho)) * kh2 *
        routeBPowerModulusEnvelope routeBKappa routeBTheta n rho
          (routeBDboundR rho z) t := by
      gcongr
    _ ≤ (Real.sqrt (n : ℝ) * (1 / rho)) * kh2 *
        routeBCellA rho z hq ^ n := by
      exact mul_le_mul_of_nonneg_left hM (mul_nonneg hscale hkh0)

theorem routeBNormalizedLowerDifferenceIntegrand_le_telescoping
    {n : ℕ} {rho z t k0 hq D : ℝ}
    (hrho : 0 < rho) (hw : 0 < routeBDboundW rho z) (ht : 0 ≤ t)
    (hhq : hq ≤ routeBCellV t ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV t))
    (hk0 : t * ‖prawitzKernel t‖ ≤ k0)
    (hD : routeBDiskBound routeBKappa rho (routeBDboundR rho z)
        (routeBDboundFrequency rho z (routeBCellV t)) ≤ D) :
    routeBNormalizedLowerDifferenceIntegrand n rho z t ≤
      routeBCellTelescopingBound n rho z t k0 hq D := by
  let r := routeBDboundR rho z
  let u := routeBUFrequency rho r t
  let A := routeBModulusEnvelope routeBKappa routeBTheta rho r t
  let B := routeBGaussianEnvelope rho r t
  let D0 := routeBDiskBound routeBKappa rho r (2 * Real.pi * t / r)
  let H := max A B ^ (n - 1)
  have hr : 0 < r := by
    dsimp only [r, routeBDboundR]
    positivity
  have hdiff :
      routeBPowerDifferenceEnvelope routeBKappa routeBTheta n rho r t ≤
        (n : ℝ) * rho * u ^ 3 * D0 * H := by
    simp only [routeBPowerDifferenceEnvelope]
    exact min_le_left _ _
  have hcoef : 0 ≤ 2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖ := by
    positivity
  have hstep := mul_le_mul_of_nonneg_left hdiff hcoef
  have hH : H ≤ routeBCellH n rho z t hq := by
    exact routeBCell_maxPower_le hrho hw hhq
  have hD0 : 0 ≤ D0 := routeBDiskBound_nonneg _ _ _ _
  have hD' : D0 ≤ D := by
    simpa [D0, r, routeBDboundFrequency, routeBCellV] using hD
  have hk00 : 0 ≤ k0 :=
    (mul_nonneg ht (norm_nonneg _)).trans hk0
  have hH0 : 0 ≤ H := by
    dsimp only [H]
    exact pow_nonneg
      ((routeBModulusEnvelope_nonneg _ _ _ _ _).trans (le_max_left _ _)) _
  have hDnonneg : 0 ≤ D := hD0.trans hD'
  calc
    routeBNormalizedLowerDifferenceIntegrand n rho z t ≤
        (2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖) *
          ((n : ℝ) * rho * u ^ 3 * D0 * H) := by
      simpa [routeBNormalizedLowerDifferenceIntegrand, r] using hstep
    _ = 2 * (n : ℝ) * Real.sqrt (n : ℝ) *
        (t * ‖prawitzKernel t‖) * (t ^ 2 * (2 * Real.pi) ^ 3) *
        (D0 / routeBDboundW rho z ^ 3) * H := by
      dsimp only [u, r]
      rw [routeBCell_frequency_identity hrho]
      dsimp only [routeBCellV]
      field_simp [hrho.ne', hw.ne']
    _ ≤ routeBCellTelescopingBound n rho z t k0 hq D := by
      unfold routeBCellTelescopingBound
      gcongr

theorem routeBNormalizedLowerDifferenceIntegrand_le_trivial
    {n : ℕ} {rho z t k0 hq : ℝ}
    (hrho : 0 < rho) (hw : 0 < routeBDboundW rho z) (ht : 0 < t)
    (hhq : hq ≤ routeBCellV t ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV t))
    (hk0 : t * ‖prawitzKernel t‖ ≤ k0) :
    routeBNormalizedLowerDifferenceIntegrand n rho z t ≤
      routeBCellTrivialBound n rho z t k0 hq := by
  let r := routeBDboundR rho z
  let M := routeBPowerModulusEnvelope routeBKappa routeBTheta n rho r t
  let N := routeBPowerGaussianEnvelope n rho r t
  have hdiff :
      routeBPowerDifferenceEnvelope routeBKappa routeBTheta n rho r t ≤ M + N := by
    simp only [routeBPowerDifferenceEnvelope]
    exact min_le_right _ _
  have hcoef : 0 ≤ 2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖ := by
    positivity
  have hstep := mul_le_mul_of_nonneg_left hdiff hcoef
  have hkdiv : ‖prawitzKernel t‖ ≤ k0 / t := by
    apply (le_div_iff₀ ht).2
    simpa [mul_comm] using hk0
  have hM : M ≤ routeBCellA rho z hq ^ n := by
    exact routeBCell_powerModulus_le hrho hw hhq
  have hN : N = routeBCellN n rho z t := by
    exact routeBCell_powerGaussian_eq hrho
  have hsum : M + N ≤ routeBCellA rho z hq ^ n + routeBCellN n rho z t := by
    exact add_le_add hM hN.le
  have hsum0 : 0 ≤ M + N := by
    exact add_nonneg
      (routeBPowerModulusEnvelope_nonneg _ _ _ _ _ _)
      (routeBPowerGaussianEnvelope_nonneg _ _ _ _)
  have hscale : 0 ≤ 2 * Real.sqrt (n : ℝ) / rho := by positivity
  have hkdiv0 : 0 ≤ k0 / t := by
    have hk00 : 0 ≤ k0 :=
      (mul_nonneg ht.le (norm_nonneg _)).trans hk0
    positivity
  calc
    routeBNormalizedLowerDifferenceIntegrand n rho z t ≤
        (2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖) * (M + N) := by
      simpa [routeBNormalizedLowerDifferenceIntegrand, r] using hstep
    _ ≤ (2 * Real.sqrt (n : ℝ) / rho) * (k0 / t) * (M + N) := by
      calc
        (2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖) * (M + N) =
            (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ * (M + N) := by
              ring
        _ ≤ (2 * Real.sqrt (n : ℝ) / rho) * (k0 / t) * (M + N) := by
          gcongr
    _ ≤ (2 * Real.sqrt (n : ℝ) / rho) * (k0 / t) *
        (routeBCellA rho z hq ^ n + routeBCellN n rho z t) := by
      exact mul_le_mul_of_nonneg_left hsum (mul_nonneg hscale hkdiv0)
    _ = routeBCellTrivialBound n rho z t k0 hq := by
      unfold routeBCellTrivialBound routeBDboundP
      field_simp [ht.ne']

theorem routeBNormalizedLowerDifferenceIntegrand_le_cell
    {n : ℕ} {rho z t k0 hq D : ℝ}
    (hrho : 0 < rho) (hw : 0 < routeBDboundW rho z) (ht : 0 < t)
    (hhq : hq ≤ routeBCellV t ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV t))
    (hk0 : t * ‖prawitzKernel t‖ ≤ k0)
    (hD : routeBDiskBound routeBKappa rho (routeBDboundR rho z)
        (routeBDboundFrequency rho z (routeBCellV t)) ≤ D) :
    routeBNormalizedLowerDifferenceIntegrand n rho z t ≤
      routeBCellLowerDifferenceBound n rho z t k0 hq D := by
  unfold routeBCellLowerDifferenceBound
  exact le_min
    (routeBNormalizedLowerDifferenceIntegrand_le_telescoping
      hrho hw ht.le hhq hk0 hD)
    (routeBNormalizedLowerDifferenceIntegrand_le_trivial
      hrho hw ht hhq hk0)



end

end BerryEsseen
