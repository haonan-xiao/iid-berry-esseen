import BerryEsseen.Smoothing.PrawitzSmoothingInequality
import BerryEsseen.CharacteristicFunction.BreakpointCertificate
/-!
# Route B's explicit smoothing envelopes

This module fixes equations (5.1)--(5.4) and proves the pointwise
characteristic-function bounds that feed the Prawitz functional.  Numerical
integration remains on the L2 side of the trust boundary.
-/

open MeasureTheory ProbabilityTheory intervalIntegral
open scoped ENNReal NNReal Real

namespace BerryEsseen

noncomputable section

def routeBSmoothingScale (n : ℕ) (rho : ℝ) : ℝ :=
  rho / Real.sqrt (n : ℝ)

def routeBSmoothingT (n : ℕ) (rho r : ℝ) : ℝ :=
  2 * Real.pi / (r * routeBSmoothingScale n rho)

def routeBUFrequency (rho r t : ℝ) : ℝ :=
  2 * Real.pi * t / (r * rho)

def routeBModulusEnvelope
    (kappa theta rho r t : ℝ) : ℝ :=
  let u := routeBUFrequency rho r t
  Real.sqrt (max
    (1 - 2 * u ^ 2 * routeBMinorant kappa theta (2 * Real.pi * t)) 0)

def routeBGaussianEnvelope (rho r t : ℝ) : ℝ :=
  Real.exp (-(routeBUFrequency rho r t) ^ 2 / 2)

def routeBPowerModulusEnvelope
    (kappa theta : ℝ) (n : ℕ) (rho r t : ℝ) : ℝ :=
  routeBModulusEnvelope kappa theta rho r t ^ n

def routeBPowerGaussianEnvelope (n : ℕ) (rho r t : ℝ) : ℝ :=
  routeBGaussianEnvelope rho r t ^ n

def routeBPowerDifferenceEnvelope
    (kappa theta : ℝ) (n : ℕ) (rho r t : ℝ) : ℝ :=
  let u := routeBUFrequency rho r t
  let A := routeBModulusEnvelope kappa theta rho r t
  let B := routeBGaussianEnvelope rho r t
  let M := routeBPowerModulusEnvelope kappa theta n rho r t
  let N := routeBPowerGaussianEnvelope n rho r t
  min
    ((n : ℝ) * rho * u ^ 3 *
      routeBDiskBound kappa rho r (2 * Real.pi * t / r) *
      max A B ^ (n - 1))
    (M + N)

/-- Route B equation (5.4), now as the concrete function consumed by
`CertifiedNumericalBound`. -/
def routeBU (kappa theta : ℝ) (n : ℕ) (rho r : ℝ) : ℝ :=
  2 * (∫ t in (0 : ℝ)..prawitzSplit,
    ‖prawitzKernel t‖ *
      routeBPowerDifferenceEnvelope kappa theta n rho r t) +
  2 * (∫ t in prawitzSplit..(1 : ℝ),
    ‖prawitzKernel t‖ *
      routeBPowerModulusEnvelope kappa theta n rho r t) +
  2 * (∫ t in (0 : ℝ)..prawitzSplit,
    ‖prawitzKernelCorrection t‖ *
      routeBPowerGaussianEnvelope n rho r t) +
  (1 / Real.pi) *
    ∫ t in Set.Ici prawitzSplit,
      routeBPowerGaussianEnvelope n rho r t / t

/-- A finite, parameter-explicit dominator for the removable singularity in
Route B's lower-frequency difference integral. -/
def routeBLowerEndpointBound
    (kappa : ℝ) (n : ℕ) (rho r : ℝ) : ℝ :=
  2 * (n : ℝ) * rho * (2 * Real.pi / (r * rho)) ^ 3 *
    (routeBDiskStaticConstant kappa r * prawitzSplit ^ 2 +
      1 / (2 * (2 * Real.pi / r) ^ 2))

theorem routeBLowerEndpointBound_nonneg
    (kappa : ℝ) (n : ℕ) {rho r : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) :
    0 ≤ routeBLowerEndpointBound kappa n rho r := by
  unfold routeBLowerEndpointBound
  have hstatic := routeBDiskStaticConstant_nonneg kappa r
  have hfrequency : 0 < 2 * Real.pi / (r * rho) := by positivity
  have hscale : 0 < 2 * Real.pi / r := by positivity
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg n)) hrho.le)
      (pow_nonneg hfrequency.le 3))
    (add_nonneg
      (mul_nonneg hstatic (sq_nonneg prawitzSplit))
      (by positivity))

theorem routeBSmoothingScale_pos {n : ℕ} {rho : ℝ}
    (hn : 0 < n) (hrho : 0 < rho) : 0 < routeBSmoothingScale n rho := by
  unfold routeBSmoothingScale
  exact div_pos hrho (Real.sqrt_pos.2 (by exact_mod_cast hn))

theorem routeBSmoothingT_pos {n : ℕ} {rho r : ℝ}
    (hn : 0 < n) (hrho : 0 < rho) (hr : 0 < r) :
    0 < routeBSmoothingT n rho r := by
  unfold routeBSmoothingT
  positivity [routeBSmoothingScale_pos hn hrho]

theorem routeBSmoothingT_mul_div_sqrt {n : ℕ} {rho r t : ℝ}
    (hn : 0 < n) (hrho : 0 < rho) (hr : 0 < r) :
    routeBSmoothingT n rho r * t / Real.sqrt (n : ℝ) =
      routeBUFrequency rho r t := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  unfold routeBSmoothingT routeBSmoothingScale routeBUFrequency
  field_simp [hrho.ne', hr.ne', hsqrt.ne']

theorem routeBGaussian_exponent_scale {n : ℕ} {rho r t : ℝ}
    (hn : 0 < n) (hrho : 0 < rho) (hr : 0 < r) :
    (n : ℝ) * (-(routeBUFrequency rho r t) ^ 2 / 2) =
      -(routeBSmoothingT n rho r ^ 2 * t ^ 2) / 2 := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  have hscale := routeBSmoothingT_mul_div_sqrt
    (n := n) (rho := rho) (r := r) (t := t) hn hrho hr
  have hmul :
      routeBSmoothingT n rho r * t =
        routeBUFrequency rho r t * Real.sqrt (n : ℝ) :=
    (div_eq_iff hsqrt.ne').mp hscale
  rw [show routeBSmoothingT n rho r ^ 2 * t ^ 2 =
      (routeBSmoothingT n rho r * t) ^ 2 by ring, hmul, mul_pow,
    Real.sq_sqrt hnReal.le]
  ring

theorem routeBUFrequency_nonneg {rho r t : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) (ht : 0 ≤ t) :
    0 ≤ routeBUFrequency rho r t := by
  unfold routeBUFrequency
  positivity

theorem routeBUFrequency_mul_parameters {rho r t : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) :
    r * rho * routeBUFrequency rho r t = 2 * Real.pi * t := by
  unfold routeBUFrequency
  field_simp [hrho.ne', hr.ne']

theorem routeBUFrequency_scaled {rho r t : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) :
    rho * routeBUFrequency rho r t = 2 * Real.pi * t / r := by
  unfold routeBUFrequency
  field_simp [hrho.ne', hr.ne']

/-- The positive-exponent form of the complex power telescoping bound. -/
theorem norm_pow_sub_pow_le_nat {a b : ℂ} {M : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    ‖a ^ n - b ^ n‖ ≤ (n : ℝ) * ‖a - b‖ * M ^ (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm, add_comm] using
    norm_pow_sub_pow_le ha hb k

theorem routeBModulusEnvelope_nonneg (kappa theta rho r t : ℝ) :
    0 ≤ routeBModulusEnvelope kappa theta rho r t := by
  unfold routeBModulusEnvelope
  exact Real.sqrt_nonneg _

theorem measurable_routeBUFrequency (rho r : ℝ) :
    Measurable (routeBUFrequency rho r) := by
  unfold routeBUFrequency
  fun_prop

theorem measurable_routeBModulusEnvelope (kappa theta rho r : ℝ) :
    Measurable (routeBModulusEnvelope kappa theta rho r) := by
  unfold routeBModulusEnvelope
  change Measurable (fun t : ℝ => Real.sqrt (max
    (1 - 2 * routeBUFrequency rho r t ^ 2 *
      routeBMinorant kappa theta (2 * Real.pi * t)) 0))
  have hu : Measurable (routeBUFrequency rho r) :=
    measurable_routeBUFrequency rho r
  have hq : Measurable (fun t : ℝ =>
      routeBMinorant kappa theta (2 * Real.pi * t)) :=
    (routeBMinorant_measurable kappa theta).comp (by fun_prop)
  have hone : Measurable (fun _ : ℝ => (1 : ℝ)) := measurable_const
  have htwo : Measurable (fun _ : ℝ => (2 : ℝ)) := measurable_const
  have hzero : Measurable (fun _ : ℝ => (0 : ℝ)) := measurable_const
  exact (hone.sub ((htwo.mul (hu.pow_const 2)).mul hq)).max hzero |>.sqrt

theorem measurable_routeBPowerModulusEnvelope
    (kappa theta : ℝ) (n : ℕ) (rho r : ℝ) :
    Measurable (routeBPowerModulusEnvelope kappa theta n rho r) := by
  unfold routeBPowerModulusEnvelope
  exact (measurable_routeBModulusEnvelope kappa theta rho r).pow_const n

/-- The convex-minorant modulus envelope never exceeds one at nonnegative
frequencies. -/
theorem routeBModulusEnvelope_le_one
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    (rho r : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    routeBModulusEnvelope kappa theta rho r t ≤ 1 := by
  have harg : 0 ≤ 2 * Real.pi * t := by positivity
  have hq : 0 ≤ routeBMinorant kappa theta (2 * Real.pi * t) :=
    routeBMinorant_nonneg hcert _ harg
  unfold routeBModulusEnvelope
  rw [Real.sqrt_le_one]
  refine max_le ?_ zero_le_one
  nlinarith [mul_nonneg (sq_nonneg (routeBUFrequency rho r t)) hq]

theorem routeBPowerModulusEnvelope_nonneg
    (kappa theta : ℝ) (n : ℕ) (rho r t : ℝ) :
    0 ≤ routeBPowerModulusEnvelope kappa theta n rho r t := by
  unfold routeBPowerModulusEnvelope
  exact pow_nonneg (routeBModulusEnvelope_nonneg kappa theta rho r t) n

theorem routeBPowerModulusEnvelope_le_one
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    (n : ℕ) (rho r : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    routeBPowerModulusEnvelope kappa theta n rho r t ≤ 1 := by
  unfold routeBPowerModulusEnvelope
  exact pow_le_one₀ (routeBModulusEnvelope_nonneg kappa theta rho r t)
    (routeBModulusEnvelope_le_one hcert rho r ht)

theorem measurable_routeBGaussianEnvelope (rho r : ℝ) :
    Measurable (routeBGaussianEnvelope rho r) := by
  unfold routeBGaussianEnvelope
  exact (((measurable_routeBUFrequency rho r).pow_const 2).neg.div_const 2).exp

theorem measurable_routeBPowerGaussianEnvelope
    (n : ℕ) (rho r : ℝ) :
    Measurable (routeBPowerGaussianEnvelope n rho r) := by
  unfold routeBPowerGaussianEnvelope
  exact (measurable_routeBGaussianEnvelope rho r).pow_const n

theorem routeBGaussianEnvelope_le_one (rho r t : ℝ) :
    routeBGaussianEnvelope rho r t ≤ 1 := by
  unfold routeBGaussianEnvelope
  rw [Real.exp_le_one_iff]
  nlinarith [sq_nonneg (routeBUFrequency rho r t)]

theorem routeBPowerGaussianEnvelope_nonneg
    (n : ℕ) (rho r t : ℝ) :
    0 ≤ routeBPowerGaussianEnvelope n rho r t := by
  unfold routeBPowerGaussianEnvelope
  apply pow_nonneg
  unfold routeBGaussianEnvelope
  exact (Real.exp_pos _).le

theorem measurable_routeBPowerDifferenceEnvelope
    (kappa theta : ℝ) (n : ℕ) (rho r : ℝ) :
    Measurable (routeBPowerDifferenceEnvelope kappa theta n rho r) := by
  have hu : Measurable (routeBUFrequency rho r) :=
    measurable_routeBUFrequency rho r
  have hA : Measurable (routeBModulusEnvelope kappa theta rho r) :=
    measurable_routeBModulusEnvelope kappa theta rho r
  have hB : Measurable (routeBGaussianEnvelope rho r) :=
    measurable_routeBGaussianEnvelope rho r
  have hM : Measurable (routeBPowerModulusEnvelope kappa theta n rho r) :=
    measurable_routeBPowerModulusEnvelope kappa theta n rho r
  have hN : Measurable (routeBPowerGaussianEnvelope n rho r) :=
    measurable_routeBPowerGaussianEnvelope n rho r
  have hD : Measurable (fun t : ℝ =>
      routeBDiskBound kappa rho r (2 * Real.pi * t / r)) :=
    (measurable_routeBDiskBound kappa rho r).comp (by fun_prop)
  unfold routeBPowerDifferenceEnvelope
  change Measurable (fun t : ℝ => min
    ((n : ℝ) * rho * routeBUFrequency rho r t ^ 3 *
      routeBDiskBound kappa rho r (2 * Real.pi * t / r) *
        max (routeBModulusEnvelope kappa theta rho r t)
          (routeBGaussianEnvelope rho r t) ^ (n - 1))
    (routeBPowerModulusEnvelope kappa theta n rho r t +
      routeBPowerGaussianEnvelope n rho r t))
  exact (((((measurable_const.mul measurable_const).mul (hu.pow_const 3)).mul hD).mul
    ((hA.max hB).pow_const (n - 1))).min (hM.add hN))

theorem routeBPowerDifferenceEnvelope_nonneg
    (kappa theta : ℝ) (n : ℕ) {rho r t : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) (ht : 0 ≤ t) :
    0 ≤ routeBPowerDifferenceEnvelope kappa theta n rho r t := by
  have hu : 0 ≤ routeBUFrequency rho r t :=
    routeBUFrequency_nonneg hrho hr ht
  unfold routeBPowerDifferenceEnvelope
  dsimp only
  refine le_min ?_ ?_
  · have hbase : 0 ≤ (n : ℝ) * rho * routeBUFrequency rho r t ^ 3 *
        routeBDiskBound kappa rho r (2 * Real.pi * t / r) :=
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg n) hrho.le) (pow_nonneg hu 3))
        (routeBDiskBound_nonneg kappa rho r (2 * Real.pi * t / r))
    have hmax : 0 ≤ max (routeBModulusEnvelope kappa theta rho r t)
        (routeBGaussianEnvelope rho r t) :=
      (routeBModulusEnvelope_nonneg kappa theta rho r t).trans
        (le_max_left _ _)
    exact mul_nonneg hbase (pow_nonneg hmax (n - 1))
  · exact add_nonneg
      (routeBPowerModulusEnvelope_nonneg kappa theta n rho r t)
      (routeBPowerGaussianEnvelope_nonneg n rho r t)

/-- The `min` defining the power-difference envelope may always be bounded by
its one-step/telescoping branch. -/
theorem routeBPowerDifferenceEnvelope_le_diskTerm
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    (n : ℕ) {rho r t : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) (ht : 0 ≤ t) :
    routeBPowerDifferenceEnvelope kappa theta n rho r t ≤
      (n : ℝ) * rho * routeBUFrequency rho r t ^ 3 *
        routeBDiskBound kappa rho r (2 * Real.pi * t / r) := by
  let A := routeBModulusEnvelope kappa theta rho r t
  let B := routeBGaussianEnvelope rho r t
  let base := (n : ℝ) * rho * routeBUFrequency rho r t ^ 3 *
    routeBDiskBound kappa rho r (2 * Real.pi * t / r)
  have hu : 0 ≤ routeBUFrequency rho r t :=
    routeBUFrequency_nonneg hrho hr ht
  have hbase : 0 ≤ base := by
    dsimp only [base]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg n) hrho.le) (pow_nonneg hu 3))
      (routeBDiskBound_nonneg kappa rho r (2 * Real.pi * t / r))
  have hmaxNonneg : 0 ≤ max A B :=
    (routeBModulusEnvelope_nonneg kappa theta rho r t).trans
      (le_max_left A B)
  have hmaxLe : max A B ≤ 1 := by
    refine max_le ?_ ?_
    · exact routeBModulusEnvelope_le_one hcert rho r ht
    · exact routeBGaussianEnvelope_le_one rho r t
  have hpow : max A B ^ (n - 1) ≤ 1 :=
    pow_le_one₀ hmaxNonneg hmaxLe
  calc
    routeBPowerDifferenceEnvelope kappa theta n rho r t ≤
        base * max A B ^ (n - 1) := by
      exact min_le_left _ _
    _ ≤ base * 1 := mul_le_mul_of_nonneg_left hpow hbase
    _ = (n : ℝ) * rho * routeBUFrequency rho r t ^ 3 *
          routeBDiskBound kappa rho r (2 * Real.pi * t / r) := by
      dsimp only [base]
      ring

/-- The apparent `1/t` singularity of the Prawitz kernel is cancelled by the
one-step cubic factor.  The proof only needs the coarse bound
`routeBEpsilon rho c ≤ 1/(2c)`. -/
theorem prawitzKernel_mul_routeBPowerDifferenceEnvelope_le_endpointBound
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    (n : ℕ) {rho r t : ℝ}
    (hrho : 0 < rho) (hr : 0 < r)
    (ht : 0 < t) (htSplit : t ≤ prawitzSplit) :
    ‖prawitzKernel t‖ *
        routeBPowerDifferenceEnvelope kappa theta n rho r t ≤
      routeBLowerEndpointBound kappa n rho r := by
  let u := routeBUFrequency rho r t
  let c := 2 * Real.pi * t / r
  let a := 2 * Real.pi / (r * rho)
  let b := 2 * Real.pi / r
  let C := routeBDiskStaticConstant kappa r
  have hsplitHalf : prawitzSplit ≤ (1 : ℝ) / 2 := by
    norm_num [prawitzSplit]
  have hKernel : ‖prawitzKernel t‖ ≤ 2 / t :=
    norm_prawitzKernel_le_two_div ht (htSplit.trans hsplitHalf)
  have huPos : 0 < u := by
    dsimp only [u]
    unfold routeBUFrequency
    positivity
  have hcPos : 0 < c := by
    dsimp only [c]
    positivity
  have haPos : 0 < a := by
    dsimp only [a]
    positivity
  have hbPos : 0 < b := by
    dsimp only [b]
    positivity
  have hUeq : u = a * t := by
    dsimp only [u, a]
    unfold routeBUFrequency
    ring
  have hCeq : c = b * t := by
    dsimp only [c, b]
    ring
  have hepsilonNonneg : 0 ≤ routeBEpsilon rho c :=
    routeBEpsilon_nonneg hrho hcPos.le
  have hepsilonLe : routeBEpsilon rho c ≤ 1 / (2 * c) :=
    routeBEpsilon_le_inv_two_mul hrho hcPos
  have hinvNonneg : 0 ≤ 1 / (2 * c) := by positivity
  have hepsilonSq : routeBEpsilon rho c ^ 2 ≤ (1 / (2 * c)) ^ 2 :=
    pow_le_pow_left₀ hepsilonNonneg hepsilonLe 2
  have hD : routeBDiskBound kappa rho r c ≤ C + 1 / (2 * c ^ 2) := by
    calc
      routeBDiskBound kappa rho r c ≤
          C + 2 * routeBEpsilon rho c ^ 2 := by
        dsimp only [C]
        exact routeBDiskBound_le_static_add_epsilon_sq kappa rho r c
      _ ≤ C + 2 * (1 / (2 * c)) ^ 2 := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hepsilonSq (by norm_num : (0 : ℝ) ≤ 2))
      _ = C + 1 / (2 * c ^ 2) := by
        field_simp [hcPos.ne']
  have hDifference :
      routeBPowerDifferenceEnvelope kappa theta n rho r t ≤
        (n : ℝ) * rho * u ^ 3 * routeBDiskBound kappa rho r c := by
    simpa only [u, c] using
      routeBPowerDifferenceEnvelope_le_diskTerm hcert n hrho hr ht.le
  have hDifferenceNonneg :
      0 ≤ routeBPowerDifferenceEnvelope kappa theta n rho r t :=
    routeBPowerDifferenceEnvelope_nonneg kappa theta n hrho hr ht.le
  have hcoefficient : 0 ≤ (n : ℝ) * rho * u ^ 3 := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hrho.le)
      (pow_nonneg huPos.le 3)
  have hstatic : 0 ≤ C := by
    dsimp only [C]
    exact routeBDiskStaticConstant_nonneg kappa r
  have hpointwise :
      ‖prawitzKernel t‖ *
          routeBPowerDifferenceEnvelope kappa theta n rho r t ≤
        2 * (n : ℝ) * rho * a ^ 3 *
          (C * t ^ 2 + 1 / (2 * b ^ 2)) := by
    calc
      ‖prawitzKernel t‖ *
          routeBPowerDifferenceEnvelope kappa theta n rho r t ≤
          (2 / t) *
            routeBPowerDifferenceEnvelope kappa theta n rho r t :=
        mul_le_mul_of_nonneg_right hKernel hDifferenceNonneg
      _ ≤ (2 / t) *
            ((n : ℝ) * rho * u ^ 3 * routeBDiskBound kappa rho r c) :=
        mul_le_mul_of_nonneg_left hDifference (by positivity)
      _ ≤ (2 / t) *
            ((n : ℝ) * rho * u ^ 3 * (C + 1 / (2 * c ^ 2))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hD hcoefficient) (by positivity)
      _ = 2 * (n : ℝ) * rho * a ^ 3 *
            (C * t ^ 2 + 1 / (2 * b ^ 2)) := by
        rw [hUeq, hCeq]
        field_simp [ht.ne', hbPos.ne']
  have htSq : t ^ 2 ≤ prawitzSplit ^ 2 :=
    pow_le_pow_left₀ ht.le htSplit 2
  have hinside :
      C * t ^ 2 + 1 / (2 * b ^ 2) ≤
        C * prawitzSplit ^ 2 + 1 / (2 * b ^ 2) := by
    exact add_le_add (mul_le_mul_of_nonneg_left htSq hstatic) le_rfl
  have hprefactor : 0 ≤ 2 * (n : ℝ) * rho * a ^ 3 := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hrho.le)
      (pow_nonneg haPos.le 3)
  calc
    ‖prawitzKernel t‖ *
        routeBPowerDifferenceEnvelope kappa theta n rho r t ≤
      2 * (n : ℝ) * rho * a ^ 3 *
        (C * t ^ 2 + 1 / (2 * b ^ 2)) := hpointwise
    _ ≤ 2 * (n : ℝ) * rho * a ^ 3 *
        (C * prawitzSplit ^ 2 + 1 / (2 * b ^ 2)) :=
      mul_le_mul_of_nonneg_left hinside hprefactor
    _ = routeBLowerEndpointBound kappa n rho r := by
      rfl

theorem routeBGaussianEnvelope_pos (rho r t : ℝ) :
    0 < routeBGaussianEnvelope rho r t := by
  unfold routeBGaussianEnvelope
  exact Real.exp_pos _

theorem routeBPowerGaussianEnvelope_eq_smoothing_gaussian
    {n : ℕ} {rho r t : ℝ}
    (hn : 0 < n) (hrho : 0 < rho) (hr : 0 < r) :
    routeBPowerGaussianEnvelope n rho r t =
      Real.exp (-(routeBSmoothingT n rho r ^ 2 * t ^ 2) / 2) := by
  unfold routeBPowerGaussianEnvelope routeBGaussianEnvelope
  rw [← Real.exp_nat_mul]
  congr 1
  exact routeBGaussian_exponent_scale hn hrho hr

theorem complex_gaussian_pow_eq_smoothing_gaussian
    {n : ℕ} {rho r t : ℝ}
    (hn : 0 < n) (hrho : 0 < rho) (hr : 0 < r) :
    Complex.exp (-(routeBUFrequency rho r t : ℂ) ^ 2 / 2) ^ n =
      Complex.exp (-(routeBSmoothingT n rho r * t : ℂ) ^ 2 / 2) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  norm_cast
  have hscale := routeBGaussian_exponent_scale
    (n := n) (rho := rho) (r := r) (t := t) hn hrho hr
  calc
    (n : ℝ) * (-(routeBUFrequency rho r t) ^ 2 / 2) =
        -(routeBSmoothingT n rho r ^ 2 * t ^ 2) / 2 := hscale
    _ = -(routeBSmoothingT n rho r * t) ^ 2 / 2 := by ring

theorem norm_complex_gaussian_eq_routeBGaussianEnvelope
    (rho r t : ℝ) :
    ‖Complex.exp (-(routeBUFrequency rho r t : ℂ) ^ 2 / 2)‖ =
      routeBGaussianEnvelope rho r t := by
  rw [complex_gaussian_eq_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rfl

theorem routeB_charFun_norm_le_modulusEnvelope
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖charFun mu
        (routeBUFrequency (thirdAbsoluteMoment mu)
          (symmetrizationRatio mu) t)‖ ≤
      routeBModulusEnvelope kappa theta (thirdAbsoluteMoment mu)
        (symmetrizationRatio mu) t := by
  have hrho : 0 < thirdAbsoluteMoment mu := by
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have hr : 0 < symmetrizationRatio mu := by
    linarith [symmetrizationRatio_lower mu hX hmean hsecond]
  have hu : 0 ≤ routeBUFrequency (thirdAbsoluteMoment mu)
      (symmetrizationRatio mu) t := routeBUFrequency_nonneg hrho hr ht
  have harg :
      symmetrizationRatio mu * thirdAbsoluteMoment mu *
          |routeBUFrequency (thirdAbsoluteMoment mu)
            (symmetrizationRatio mu) t| =
        2 * Real.pi * t := by
    rw [abs_of_nonneg hu]
    exact routeBUFrequency_mul_parameters hrho hr
  have hmod := routeB_modulus_sq_le_of_certificate mu hX hmean hsecond hcert
    (routeBUFrequency (thirdAbsoluteMoment mu) (symmetrizationRatio mu) t)
  rw [harg] at hmod
  apply (sq_le_sq₀ (norm_nonneg _)
    (routeBModulusEnvelope_nonneg kappa theta (thirdAbsoluteMoment mu)
      (symmetrizationRatio mu) t)).mp
  unfold routeBModulusEnvelope
  rw [Real.sq_sqrt (le_max_right _ _)]
  exact hmod.trans (le_max_left _ _)

theorem routeB_charFun_pow_norm_le_powerModulusEnvelope
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖charFun mu
        (routeBUFrequency (thirdAbsoluteMoment mu)
          (symmetrizationRatio mu) t) ^ n‖ ≤
      routeBPowerModulusEnvelope kappa theta n (thirdAbsoluteMoment mu)
        (symmetrizationRatio mu) t := by
  rw [norm_pow]
  unfold routeBPowerModulusEnvelope
  exact pow_le_pow_left₀ (norm_nonneg _)
    (routeB_charFun_norm_le_modulusEnvelope mu hX hmean hsecond hcert ht) n

theorem routeB_one_step_at_smoothing_frequency
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let r := symmetrizationRatio mu
    let u := routeBUFrequency rho r t
    ‖charFun mu u - Complex.exp (-(u : ℂ) ^ 2 / 2)‖ ≤
      rho * u ^ 3 * routeBDiskBound kappa rho r (2 * Real.pi * t / r) := by
  dsimp only
  have hrho : 0 < thirdAbsoluteMoment mu := by
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have hr : 0 < symmetrizationRatio mu := by
    linarith [symmetrizationRatio_lower mu hX hmean hsecond]
  have hu : 0 ≤ routeBUFrequency (thirdAbsoluteMoment mu)
      (symmetrizationRatio mu) t := routeBUFrequency_nonneg hrho hr ht
  have hc := routeBUFrequency_scaled (rho := thirdAbsoluteMoment mu)
    (r := symmetrizationRatio mu) (t := t) hrho hr
  have hone := routeB_one_step_disk mu hX hmean hsecond hcert
    (routeBUFrequency (thirdAbsoluteMoment mu) (symmetrizationRatio mu) t)
  rw [abs_of_nonneg hu, hc] at hone
  exact hone

theorem routeB_charFun_power_difference_le_envelope
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let r := symmetrizationRatio mu
    let u := routeBUFrequency rho r t
    ‖charFun mu u ^ n - Complex.exp (-(u : ℂ) ^ 2 / 2) ^ n‖ ≤
      routeBPowerDifferenceEnvelope kappa theta n rho r t := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let u := routeBUFrequency rho r t
  let A := routeBModulusEnvelope kappa theta rho r t
  let B := routeBGaussianEnvelope rho r t
  have hA : ‖charFun mu u‖ ≤ A := by
    dsimp only [rho, r, u, A]
    exact routeB_charFun_norm_le_modulusEnvelope mu hX hmean hsecond hcert ht
  have hB : ‖Complex.exp (-(u : ℂ) ^ 2 / 2)‖ = B := by
    dsimp only [u, B]
    exact norm_complex_gaussian_eq_routeBGaussianEnvelope rho r t
  have hmaxNonneg : 0 ≤ max A B := by
    exact (routeBModulusEnvelope_nonneg kappa theta rho r t).trans
      (le_max_left A B)
  have hpower := norm_pow_sub_pow_le_nat hn
    (hA.trans (le_max_left A B))
    (hB.le.trans (le_max_right A B))
  have hone :
      ‖charFun mu u - Complex.exp (-(u : ℂ) ^ 2 / 2)‖ ≤
        rho * u ^ 3 * routeBDiskBound kappa rho r (2 * Real.pi * t / r) := by
    dsimp only [rho, r, u]
    exact routeB_one_step_at_smoothing_frequency mu hX hmean hsecond hcert ht
  have hfirst :
      ‖charFun mu u ^ n - Complex.exp (-(u : ℂ) ^ 2 / 2) ^ n‖ ≤
        (n : ℝ) * rho * u ^ 3 *
          routeBDiskBound kappa rho r (2 * Real.pi * t / r) *
          max A B ^ (n - 1) := by
    calc
      ‖charFun mu u ^ n - Complex.exp (-(u : ℂ) ^ 2 / 2) ^ n‖ ≤
          (n : ℝ) *
            ‖charFun mu u - Complex.exp (-(u : ℂ) ^ 2 / 2)‖ *
              max A B ^ (n - 1) := hpower
      _ ≤ (n : ℝ) *
            (rho * u ^ 3 *
              routeBDiskBound kappa rho r (2 * Real.pi * t / r)) *
              max A B ^ (n - 1) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg n))
              (pow_nonneg hmaxNonneg _)
      _ = (n : ℝ) * rho * u ^ 3 *
            routeBDiskBound kappa rho r (2 * Real.pi * t / r) *
              max A B ^ (n - 1) := by ring
  have htrivial :
      ‖charFun mu u ^ n - Complex.exp (-(u : ℂ) ^ 2 / 2) ^ n‖ ≤
        routeBPowerModulusEnvelope kappa theta n rho r t +
          routeBPowerGaussianEnvelope n rho r t := by
    calc
      ‖charFun mu u ^ n - Complex.exp (-(u : ℂ) ^ 2 / 2) ^ n‖ ≤
          ‖charFun mu u ^ n‖ +
            ‖Complex.exp (-(u : ℂ) ^ 2 / 2) ^ n‖ := norm_sub_le _ _
      _ = ‖charFun mu u‖ ^ n +
            ‖Complex.exp (-(u : ℂ) ^ 2 / 2)‖ ^ n := by
              rw [norm_pow, norm_pow]
      _ ≤ A ^ n + B ^ n := by
        exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) hA n)
          (by rw [hB])
      _ = routeBPowerModulusEnvelope kappa theta n rho r t +
            routeBPowerGaussianEnvelope n rho r t := rfl
  change ‖charFun mu u ^ n - Complex.exp (-(u : ℂ) ^ 2 / 2) ^ n‖ ≤
    routeBPowerDifferenceEnvelope kappa theta n rho r t
  unfold routeBPowerDifferenceEnvelope
  dsimp only
  exact le_min hfirst htrivial

theorem routeB_standardizedSum_charFun_norm_le_envelope
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    let r := symmetrizationRatio (P.map (X 0))
    let T := routeBSmoothingT n rho r
    ‖charFun (standardizedSumLaw P X n) (T * t)‖ ≤
      routeBPowerModulusEnvelope kappa theta n rho r t := by
  let mu := P.map (X 0)
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let T := routeBSmoothingT n rho r
  let u := routeBUFrequency rho r t
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  have hnPos : 0 < n := by omega
  have hrho : 0 < rho := by
    dsimp only [rho, mu]
    linarith [thirdAbsoluteMoment_ge_one (P.map (X 0)) hX hsecond]
  have hr : 0 < r := by
    dsimp only [r, mu]
    linarith [symmetrizationRatio_lower (P.map (X 0)) hX hmean hsecond]
  have harg : (Real.sqrt (n : ℝ))⁻¹ * (T * t) = u := by
    have hscale := routeBSmoothingT_mul_div_sqrt
      (n := n) (rho := rho) (r := r) (t := t) hnPos hrho hr
    simpa only [T, u, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscale
  change ‖charFun (standardizedSumLaw P X n) (T * t)‖ ≤
    routeBPowerModulusEnvelope kappa theta n rho r t
  rw [charFun_standardizedSumLaw P X hindep hident n (T * t), harg]
  dsimp only [mu, rho, r]
  exact routeB_charFun_pow_norm_le_powerModulusEnvelope
    (P.map (X 0)) hX hmean hsecond hcert n ht

theorem routeB_standardizedSum_charFun_difference_le_envelope
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    let r := symmetrizationRatio (P.map (X 0))
    let T := routeBSmoothingT n rho r
    ‖charFun (standardizedSumLaw P X n) (T * t) -
        Complex.exp (-(T * t : ℂ) ^ 2 / 2)‖ ≤
      routeBPowerDifferenceEnvelope kappa theta n rho r t := by
  let mu := P.map (X 0)
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let T := routeBSmoothingT n rho r
  let u := routeBUFrequency rho r t
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  have hnPos : 0 < n := by omega
  have hrho : 0 < rho := by
    dsimp only [rho, mu]
    linarith [thirdAbsoluteMoment_ge_one (P.map (X 0)) hX hsecond]
  have hr : 0 < r := by
    dsimp only [r, mu]
    linarith [symmetrizationRatio_lower (P.map (X 0)) hX hmean hsecond]
  have harg : (Real.sqrt (n : ℝ))⁻¹ * (T * t) = u := by
    have hscale := routeBSmoothingT_mul_div_sqrt
      (n := n) (rho := rho) (r := r) (t := t) hnPos hrho hr
    simpa only [T, u, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscale
  change ‖charFun (standardizedSumLaw P X n) (T * t) -
      Complex.exp (-(T * t : ℂ) ^ 2 / 2)‖ ≤
    routeBPowerDifferenceEnvelope kappa theta n rho r t
  rw [charFun_standardizedSumLaw P X hindep hident n (T * t), harg,
    ← complex_gaussian_pow_eq_smoothing_gaussian hnPos hrho hr]
  dsimp only [mu, rho, r, u]
  exact routeB_charFun_power_difference_le_envelope
    (P.map (X 0)) hX hmean hsecond hcert hn ht

/-- The lower-frequency Route B envelope is interval-integrable: its cubic
one-step factor cancels the Prawitz kernel's endpoint singularity. -/
theorem routeB_prawitz_difference_envelope_intervalIntegrable
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    (n : ℕ) {rho r : ℝ} (hrho : 0 < rho) (hr : 0 < r) :
    IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        routeBPowerDifferenceEnvelope kappa theta n rho r t)
      volume 0 prawitzSplit := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num [prawitzSplit] : (0 : ℝ) ≤ prawitzSplit)]
  apply Measure.integrableOn_of_bounded
    (M := routeBLowerEndpointBound kappa n rho r) measure_Ioc_lt_top.ne
  · exact ((measurable_prawitzKernel.norm).mul
      (measurable_routeBPowerDifferenceEnvelope kappa theta n rho r)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with t ht
    have hDifferenceNonneg :
        0 ≤ routeBPowerDifferenceEnvelope kappa theta n rho r t :=
      routeBPowerDifferenceEnvelope_nonneg kappa theta n hrho hr ht.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) hDifferenceNonneg)]
    exact prawitzKernel_mul_routeBPowerDifferenceEnvelope_le_endpointBound
      hcert n hrho hr ht.1 ht.2

/-- The first Prawitz integral is dominated by Route B's power-difference
envelope. -/
theorem routeB_prawitz_difference_integral_le
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    {n : ℕ} (hn : 1 ≤ n)
    (hEnvelopeIntegrable : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        routeBPowerDifferenceEnvelope kappa theta n
          (thirdAbsoluteMoment (P.map (X 0)))
          (symmetrizationRatio (P.map (X 0))) t)
      volume 0 prawitzSplit) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    let r := symmetrizationRatio (P.map (X 0))
    let T := routeBSmoothingT n rho r
    (∫ t in (0 : ℝ)..prawitzSplit,
        ‖prawitzKernel t‖ *
          ‖charFun (standardizedSumLaw P X n) (T * t) -
            Complex.exp (-(T * t : ℂ) ^ 2 / 2)‖) ≤
      ∫ t in (0 : ℝ)..prawitzSplit,
        ‖prawitzKernel t‖ *
          routeBPowerDifferenceEnvelope kappa theta n rho r t := by
  let rho := thirdAbsoluteMoment (P.map (X 0))
  let r := symmetrizationRatio (P.map (X 0))
  let T := routeBSmoothingT n rho r
  letI : IsProbabilityMeasure (standardizedSumLaw P X n) :=
    isProbabilityMeasure_standardizedSumLaw P X
      (fun k => (hident k).aemeasurable_fst) n
  change (∫ t in (0 : ℝ)..prawitzSplit,
      ‖prawitzKernel t‖ *
        ‖charFun (standardizedSumLaw P X n) (T * t) -
          Complex.exp (-(T * t : ℂ) ^ 2 / 2)‖) ≤
    ∫ t in (0 : ℝ)..prawitzSplit,
      ‖prawitzKernel t‖ *
        routeBPowerDifferenceEnvelope kappa theta n rho r t
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
      rw [Set.uIoc_of_le (by norm_num [prawitzSplit] : (0 : ℝ) ≤ prawitzSplit)] at ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left
        (routeB_standardizedSum_charFun_difference_le_envelope
          P X hindep hident hX hmean hsecond hcert hn ht.1.le)
        (norm_nonneg _)
  exact intervalIntegral.integral_mono_on
    (by norm_num [prawitzSplit]) hleftIntegrable hEnvelopeIntegrable fun t ht =>
      mul_le_mul_of_nonneg_left
        (routeB_standardizedSum_charFun_difference_le_envelope
          P X hindep hident hX hmean hsecond hcert hn ht.1)
        (norm_nonneg _)

/-- On the upper-frequency interval the Prawitz kernel is uniformly bounded,
while the Route B modulus envelope is at most one.  Hence the product is
interval-integrable without any numerical assumption. -/
theorem routeB_prawitz_modulus_envelope_intervalIntegrable
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    (n : ℕ) (rho r : ℝ) :
    IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        routeBPowerModulusEnvelope kappa theta n rho r t)
      volume prawitzSplit 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num [prawitzSplit] : prawitzSplit ≤ (1 : ℝ))]
  apply Measure.integrableOn_of_bounded (M := 2 / prawitzSplit)
    measure_Ioc_lt_top.ne
  · exact ((measurable_prawitzKernel.norm).mul
      (measurable_routeBPowerModulusEnvelope kappa theta n rho r)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with t ht
    have htNonneg : 0 ≤ t :=
      (by norm_num [prawitzSplit] : 0 ≤ prawitzSplit).trans ht.1.le
    have hKernel : ‖prawitzKernel t‖ ≤ 2 / prawitzSplit :=
      norm_prawitzKernel_le_on_split ht.1.le ht.2
    have hEnvelope :
        routeBPowerModulusEnvelope kappa theta n rho r t ≤ 1 :=
      routeBPowerModulusEnvelope_le_one hcert n rho r htNonneg
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _)
      (routeBPowerModulusEnvelope_nonneg kappa theta n rho r t))]
    simpa only [mul_one] using mul_le_mul hKernel hEnvelope
      (routeBPowerModulusEnvelope_nonneg kappa theta n rho r t)
      (by norm_num [prawitzSplit] : 0 ≤ 2 / prawitzSplit)

/-- The upper-frequency Prawitz integral is dominated by Route B's modulus
envelope. -/
theorem routeB_prawitz_modulus_integral_le
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    {n : ℕ} (hn : 1 ≤ n)
    (hEnvelopeIntegrable : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        routeBPowerModulusEnvelope kappa theta n
          (thirdAbsoluteMoment (P.map (X 0)))
          (symmetrizationRatio (P.map (X 0))) t)
      volume prawitzSplit 1) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    let r := symmetrizationRatio (P.map (X 0))
    let T := routeBSmoothingT n rho r
    (∫ t in prawitzSplit..(1 : ℝ),
        ‖prawitzKernel t‖ *
          ‖charFun (standardizedSumLaw P X n) (T * t)‖) ≤
      ∫ t in prawitzSplit..(1 : ℝ),
        ‖prawitzKernel t‖ *
          routeBPowerModulusEnvelope kappa theta n rho r t := by
  let rho := thirdAbsoluteMoment (P.map (X 0))
  let r := symmetrizationRatio (P.map (X 0))
  let T := routeBSmoothingT n rho r
  letI : IsProbabilityMeasure (standardizedSumLaw P X n) :=
    isProbabilityMeasure_standardizedSumLaw P X
      (fun k => (hident k).aemeasurable_fst) n
  change (∫ t in prawitzSplit..(1 : ℝ),
      ‖prawitzKernel t‖ *
        ‖charFun (standardizedSumLaw P X n) (T * t)‖) ≤
    ∫ t in prawitzSplit..(1 : ℝ),
      ‖prawitzKernel t‖ *
        routeBPowerModulusEnvelope kappa theta n rho r t
  have hleftIntegrable : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        ‖charFun (standardizedSumLaw P X n) (T * t)‖)
      volume prawitzSplit 1 := by
    refine hEnvelopeIntegrable.mono_fun' ?_ ?_
    · exact ((measurable_prawitzKernel.norm).mul
        ((measurable_charFun.comp (by fun_prop)).norm)).aestronglyMeasurable
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards with t ht
      rw [Set.uIoc_of_le (by norm_num [prawitzSplit] : prawitzSplit ≤ (1 : ℝ))] at ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left
        (routeB_standardizedSum_charFun_norm_le_envelope
          P X hindep hident hX hmean hsecond hcert hn
            (le_of_lt ((by norm_num [prawitzSplit] : 0 < prawitzSplit).trans ht.1)))
        (norm_nonneg _)
  exact intervalIntegral.integral_mono_on
    (by norm_num [prawitzSplit]) hleftIntegrable hEnvelopeIntegrable fun t ht =>
      mul_le_mul_of_nonneg_left
        (routeB_standardizedSum_charFun_norm_le_envelope
          P X hindep hident hX hmean hsecond hcert hn
            ((by norm_num [prawitzSplit] : 0 ≤ prawitzSplit).trans ht.1))
        (norm_nonneg _)

/-- Once the two explicit envelope integrals are known to be integrable,
Prawitz's four-term functional is bounded by the concrete Route B function
`routeBU`. -/
theorem prawitzFunctional_standardizedSum_le_routeBU_of_intervalIntegrable
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    {n : ℕ} (hn : 1 ≤ n)
    (hDifferenceIntegrable : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        routeBPowerDifferenceEnvelope kappa theta n
          (thirdAbsoluteMoment (P.map (X 0)))
          (symmetrizationRatio (P.map (X 0))) t)
      volume 0 prawitzSplit)
    (hModulusIntegrable : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        routeBPowerModulusEnvelope kappa theta n
          (thirdAbsoluteMoment (P.map (X 0)))
          (symmetrizationRatio (P.map (X 0))) t)
      volume prawitzSplit 1) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    let r := symmetrizationRatio (P.map (X 0))
    let T := routeBSmoothingT n rho r
    prawitzFunctional (standardizedSumLaw P X n) T prawitzSplit ≤
      routeBU kappa theta n rho r := by
  let rho := thirdAbsoluteMoment (P.map (X 0))
  let r := symmetrizationRatio (P.map (X 0))
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
  have hDifference := routeB_prawitz_difference_integral_le
    P X hindep hident hX hmean hsecond hcert hn hDifferenceIntegrable
  have hModulus := routeB_prawitz_modulus_integral_le
    P X hindep hident hX hmean hsecond hcert hn hModulusIntegrable
  change prawitzFunctional (standardizedSumLaw P X n) T prawitzSplit ≤
    routeBU kappa theta n rho r
  unfold prawitzFunctional routeBU
  simp_rw [routeBPowerGaussianEnvelope_eq_smoothing_gaussian hnPos hrho hr]
  dsimp only [rho, r, T] at hDifference hModulus
  linarith

/-- The complete source-to-`routeBU` analytic bridge.  Both endpoint
integrability obligations are discharged internally. -/
theorem prawitzFunctional_standardizedSum_le_routeBU
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    {n : ℕ} (hn : 1 ≤ n) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    let r := symmetrizationRatio (P.map (X 0))
    let T := routeBSmoothingT n rho r
    prawitzFunctional (standardizedSumLaw P X n) T prawitzSplit ≤
      routeBU kappa theta n rho r := by
  let rho := thirdAbsoluteMoment (P.map (X 0))
  let r := symmetrizationRatio (P.map (X 0))
  letI : IsProbabilityMeasure (P.map (X 0)) :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith [thirdAbsoluteMoment_ge_one (P.map (X 0)) hX hsecond]
  have hr : 0 < r := by
    dsimp only [r]
    linarith [symmetrizationRatio_lower (P.map (X 0)) hX hmean hsecond]
  have hDifference : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        routeBPowerDifferenceEnvelope kappa theta n rho r t)
      volume 0 prawitzSplit :=
    routeB_prawitz_difference_envelope_intervalIntegrable hcert n hrho hr
  have hModulus : IntervalIntegrable
      (fun t => ‖prawitzKernel t‖ *
        routeBPowerModulusEnvelope kappa theta n rho r t)
      volume prawitzSplit 1 :=
    routeB_prawitz_modulus_envelope_intervalIntegrable hcert n rho r
  simpa only [rho, r] using
    prawitzFunctional_standardizedSum_le_routeBU_of_intervalIntegrable
      P X hindep hident hX hmean hsecond hcert hn hDifference hModulus

/-- The unconditional analytic Route B reduction: the Kolmogorov distance
of the normalized sum is bounded by the explicit scalar function `routeBU`.
The Prawitz smoothing proposition is discharged by
`prawitzSmoothingBound`, rather than supplied as a theorem parameter. -/
theorem kolmogorovDistance_standardizedSum_le_routeBU
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {kappa theta : ℝ} (hcert : RouteBMinorantCertificate kappa theta)
    {n : ℕ} (hn : 1 ≤ n) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    let r := symmetrizationRatio (P.map (X 0))
    kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw ≤
      routeBU kappa theta n rho r := by
  let rho := thirdAbsoluteMoment (P.map (X 0))
  let r := symmetrizationRatio (P.map (X 0))
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
  have hfunctional := prawitzFunctional_standardizedSum_le_routeBU
    P X hindep hident hX hmean hsecond hcert hn
  dsimp only [rho, r, T] at hsmooth hfunctional ⊢
  exact hsmooth.trans hfunctional

/-- The Route B reduction specialized to the exact, axiom-clean breakpoint
and slope constructed in `BreakpointCertificate.lean`. Its only remaining
non-analytic obligation is the scalar L2 numerical bound for this `routeBU`. -/
theorem kolmogorovDistance_standardizedSum_le_exactRouteBU
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
    kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw ≤
      routeBU routeBKappa routeBTheta n rho r := by
  exact kolmogorovDistance_standardizedSum_le_routeBU
    P X hindep hident hX hmean hsecond routeB_exactMinorantCertificate hn

end

end BerryEsseen
