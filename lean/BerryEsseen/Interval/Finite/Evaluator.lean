import BerryEsseen.Smoothing.FiniteEnvelope
import BerryEsseen.DyadicPrawitzFiniteIntegral

/-!
# Interval / Finite / Evaluator
-/

namespace BerryEsseen

open MeasureTheory DyadicInterval

noncomputable section

set_option maxRecDepth 100000

structure CertifiedCellEnvelope where
  f : DyadicInterval
  errorToCos : DyadicInterval
  cosU : DyadicInterval
  cosAbs : DyadicInterval
  normalOne : DyadicInterval
  normalN : DyadicInterval

def certifiedCellEnvelope
    (n : ℕ) (rho z : DyadicInterval)
    (c : DyadicPrawitzCell) : CertifiedCellEnvelope :=
  let u := DyadicInterval.div c.v (dyadicCellW rho z)
  let trig := trigSinCos u
  let d := dUpper rho z
  let real := realInterval rho d u trig.1 trig.2
  let imag := imagInterval rho z d u trig.1 trig.2
  let rectangular := rectangularEnvelope real imag
  let routeA := dyadicCellA rho z c
  let f := minModulusEnvelope routeA rectangular
  let realRadius := finiteRealRadius d u trig.1
  let errorToCos :=
    errorToCosEnvelope real realRadius imag trig.2
  {
    f := f
    errorToCos := errorToCos
    cosU := trig.2
    cosAbs := absHull trig.2
    normalOne := normalOne u
    normalN := normalN n u
  }

def certifiedRademacherDifference
    (n : ℕ) (env : CertifiedCellEnvelope) : DyadicInterval :=
  rademacherDifferenceIntervals n env.f env.errorToCos
    env.cosU env.cosAbs env.normalN

def certifiedSharedHighCellValue
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  let env := certifiedCellEnvelope n rho z c
  DyadicInterval.mul state.snP
    (DyadicInterval.mul c.kh2 (powi env.f n))

def certifiedCorrectionCellValue
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  let env := certifiedCellEnvelope n rho z c
  DyadicInterval.mul state.snP
    (DyadicInterval.mul c.kd2 env.normalN)

def certifiedTelescopingCellValue
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  let env := certifiedCellEnvelope n rho z c
  let H := powi (dyadicCellNonnegativeHull env.f env.normalOne) (n - 1)
  let D := dyadicRouteBDboundFromBoxState state c.v
  let withKernel := DyadicInterval.mul state.prefactor c.k0
  let frequency := DyadicInterval.mul (DyadicInterval.sqr c.t)
    dyadicCellTwoPiCubed
  let withFrequency := DyadicInterval.mul withKernel frequency
  let diskScale := DyadicInterval.div D state.w3
  DyadicInterval.mul (DyadicInterval.mul withFrequency diskScale) H

def certifiedTrivialCellValue
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  let env := certifiedCellEnvelope n rho z c
  let M := powi env.f n
  if 0 < c.t.lo then
    DyadicInterval.mul state.twoSnP
      (DyadicInterval.mul c.k0
        (DyadicInterval.div (DyadicInterval.add M env.normalN) c.t))
  else dyadicCellHuge

def certifiedRademacherCellValue
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  let env := certifiedCellEnvelope n rho z c
  if 0 < c.t.lo then
    DyadicInterval.mul state.twoSnP
      (DyadicInterval.mul c.k0
        (DyadicInterval.div
          (certifiedRademacherDifference n env) c.t))
  else dyadicCellHuge

def certifiedSharedLowCellValue
    (state : DyadicRouteBBoxState) (n : ℕ)
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  let telescoping := certifiedTelescopingCellValue state n rho z c
  let trivial := certifiedTrivialCellValue state n rho z c
  let rademacher := certifiedRademacherCellValue state n rho z c
  let f1 : DyadicInterval :=
    ⟨0, min telescoping.hi (min trivial.hi rademacher.hi)⟩
  DyadicInterval.add f1
    (certifiedCorrectionCellValue state n rho z c)

def lawNormalizedDifferenceIntegrand
    (n : ℕ) (mu : Measure ℝ) (t : ℝ) : ℝ :=
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let u := routeBUFrequency rho r t
  let normalN := Real.exp (-((n : ℝ) * (u ^ 2 / 2)))
  2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖ *
    ‖charFun mu u ^ n - (normalN : ℂ)‖

def lawNormalizedCorrectionIntegrand
    (n : ℕ) (mu : Measure ℝ) (t : ℝ) : ℝ :=
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let u := routeBUFrequency rho r t
  let normalN := Real.exp (-((n : ℝ) * (u ^ 2 / 2)))
  2 * Real.sqrt (n : ℝ) / rho *
    ‖prawitzKernelCorrection t‖ * normalN

def lawNormalizedLowIntegrand
    (n : ℕ) (mu : Measure ℝ) (t : ℝ) : ℝ :=
  lawNormalizedDifferenceIntegrand n mu t +
    lawNormalizedCorrectionIntegrand n mu t

def lawNormalizedHighIntegrand
    (n : ℕ) (mu : Measure ℝ) (t : ℝ) : ℝ :=
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let u := routeBUFrequency rho r t
  2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖ *
    ‖charFun mu u ^ n‖

structure CertifiedLowCellAdmissible
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : Prop where
  base : DyadicLowCellAdmissible n rho z c
  frequencyNonnegative :
    0 ≤ (DyadicInterval.div c.v (dyadicCellW rho z)).lo
  hugeFallback : ¬ 0 < c.t.lo →
    (certifiedTelescopingCellValue
      (dyadicRouteBBuildBoxState n rho z) n rho z c).hi ≤
      dyadicCellHuge.hi
  valueOrdered :
    (certifiedSharedLowCellValue
      (dyadicRouteBBuildBoxState n rho z) n rho z c).lo ≤
      (certifiedSharedLowCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).hi

structure CertifiedHighCellAdmissible
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : Prop where
  base : DyadicHighCellAdmissible n rho z c
  frequencyNonnegative :
    0 ≤ (DyadicInterval.div c.v (dyadicCellW rho z)).lo
  valueOrdered :
    (certifiedSharedHighCellValue
      (dyadicRouteBBuildBoxState n rho z) n rho z c).lo ≤
      (certifiedSharedHighCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).hi

instance (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) :
    Decidable (CertifiedLowCellAdmissible n rho z c) :=
  decidable_of_iff
    (DyadicLowCellAdmissible n rho z c ∧
      0 ≤ (DyadicInterval.div c.v (dyadicCellW rho z)).lo ∧
      (¬ 0 < c.t.lo →
        (certifiedTelescopingCellValue
          (dyadicRouteBBuildBoxState n rho z) n rho z c).hi ≤
          dyadicCellHuge.hi) ∧
      (certifiedSharedLowCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).lo ≤
        (certifiedSharedLowCellValue
          (dyadicRouteBBuildBoxState n rho z) n rho z c).hi) <| by
    constructor
    · rintro ⟨hbase, hfrequency, hhuge, hordered⟩
      exact ⟨hbase, hfrequency, hhuge, hordered⟩
    · intro h
      exact ⟨h.base, h.frequencyNonnegative, h.hugeFallback, h.valueOrdered⟩

instance (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) :
    Decidable (CertifiedHighCellAdmissible n rho z c) :=
  decidable_of_iff
    (DyadicHighCellAdmissible n rho z c ∧
      0 ≤ (DyadicInterval.div c.v (dyadicCellW rho z)).lo ∧
      (certifiedSharedHighCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).lo ≤
        (certifiedSharedHighCellValue
          (dyadicRouteBBuildBoxState n rho z) n rho z c).hi) <| by
    constructor
    · rintro ⟨hbase, hfrequency, hordered⟩
      exact ⟨hbase, hfrequency, hordered⟩
    · intro h
      exact ⟨h.base, h.frequencyNonnegative, h.valueOrdered⟩

def certifiedLowSum
    (n : ℕ) (rho z : DyadicInterval) (N : ℕ) : DyadicInterval :=
  intervalNatSum (fun i =>
    let c := dyadicRouteBLowCell N i
    DyadicInterval.mul c.wid
      (certifiedSharedLowCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c)) N

def certifiedHighSum
    (n : ℕ) (rho z : DyadicInterval) (N : ℕ) : DyadicInterval :=
  intervalNatSum (fun i =>
    let c := dyadicRouteBHighCell N i
    DyadicInterval.mul c.wid
      (certifiedSharedHighCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c)) N

theorem certifiedLowSum_eq_intervalNatSum
    (n : ℕ) (rho z : DyadicInterval) (N : ℕ) :
    certifiedLowSum n rho z N =
      intervalNatSum (fun i =>
        DyadicInterval.mul (dyadicRouteBLowCell N i).wid
          (certifiedSharedLowCellValue
            (dyadicRouteBBuildBoxState n rho z) n rho z
              (dyadicRouteBLowCell N i))) N := by
  rfl

theorem certifiedHighSum_eq_intervalNatSum
    (n : ℕ) (rho z : DyadicInterval) (N : ℕ) :
    certifiedHighSum n rho z N =
      intervalNatSum (fun i =>
        DyadicInterval.mul (dyadicRouteBHighCell N i).wid
          (certifiedSharedHighCellValue
            (dyadicRouteBBuildBoxState n rho z) n rho z
              (dyadicRouteBHighCell N i))) N := by
  rfl

def certifiedFiniteBound
    (n : ℕ) (rho z : DyadicInterval) (N : ℕ) : DyadicInterval :=
  DyadicInterval.add (certifiedLowSum n rho z N)
    (certifiedHighSum n rho z N)

def certifiedFullBound
    (n : ℕ) (rho z : DyadicInterval) (N : ℕ) : DyadicInterval :=
  DyadicInterval.add (certifiedFiniteBound n rho z N)
    (dyadicRouteBTailValue n rho z)

lemma scalarNormalN_eq_real_exp
    (n : ℕ) (rho z t : ℝ) :
    scalarNormalN n rho z t =
      Real.exp (-((n : ℝ) * (scalarU rho z t ^ 2 / 2))) := by
  unfold scalarNormalN routeBPowerGaussianEnvelope
    routeBGaussianEnvelope scalarU
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem lawNormalizedDifferenceIntegrand_le_envelope
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let r := symmetrizationRatio mu
    let z := rho * (r - 1)
    lawNormalizedDifferenceIntegrand n mu t ≤
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ *
        scalarPowerDifference n rho z t := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  let u := routeBUFrequency rho r t
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrho.ne'
  have hu : scalarU rho z t = u := by
    dsimp only [scalarU, u]
    rw [hrouteR]
  have hraw := scalar_power_difference_actual
    mu hX hmean hsecond hn ht
  have hraw' :
      ‖charFun mu u ^ n -
        (Real.exp (-((n : ℝ) * (u ^ 2 / 2))) : ℂ)‖ ≤
        scalarPowerDifference n rho z t := by
    calc
      ‖charFun mu u ^ n -
          (Real.exp (-((n : ℝ) * (u ^ 2 / 2))) : ℂ)‖ =
        ‖charFun mu (scalarU rho z t) ^ n -
          (scalarNormalN n rho z t : ℂ)‖ := by
            rw [scalarNormalN_eq_real_exp, hu]
      _ ≤ scalarPowerDifference n rho z t := by
        simpa only [rho, r, z] using hraw
  have hscale : 0 ≤
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ := by
    positivity
  simpa only [lawNormalizedDifferenceIntegrand, rho, r, u,
    mul_assoc] using mul_le_mul_of_nonneg_left hraw' hscale

theorem lawNormalizedHighIntegrand_le_envelope
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let r := symmetrizationRatio mu
    let z := rho * (r - 1)
    lawNormalizedHighIntegrand n mu t ≤
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ *
        scalarPowerModulus n rho z t := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  let u := routeBUFrequency rho r t
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrho.ne'
  have hmod := scalar_modulus_actual mu hX hmean hsecond ht
  have hmod' : ‖charFun mu u‖ ≤ scalarModulus rho z t := by
    simpa only [rho, r, z, u, scalarU, hrouteR] using hmod
  have hpow : ‖charFun mu u‖ ^ n ≤
      scalarPowerModulus n rho z t := by
    unfold scalarPowerModulus
    exact pow_le_pow_left₀ (norm_nonneg _) hmod' n
  have hscale : 0 ≤
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ := by
    positivity
  rw [lawNormalizedHighIntegrand, norm_pow]
  simpa only [rho, r, u, mul_assoc] using
    mul_le_mul_of_nonneg_left hpow hscale

theorem intervalIntegrable_lawNormalizedDifferenceIntegrand
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    IntervalIntegrable (lawNormalizedDifferenceIntegrand n mu)
      volume 0 prawitzSplit := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have hr : 0 < r := by
    dsimp only [r]
    linarith [symmetrizationRatio_lower mu hX hmean hsecond]
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrho.ne'
  have hrouteRPos : 0 < routeBDboundR rho z := by
    rw [hrouteR]
    exact hr
  have hbase := prawitz_difference_envelope_intervalIntegrable
    n hrho hrouteRPos
  have hscaled := hbase.const_mul (2 * Real.sqrt (n : ℝ) / rho)
  refine hscaled.mono_fun' ?_ ?_
  · unfold lawNormalizedDifferenceIntegrand
    have hu : Measurable (routeBUFrequency
        (thirdAbsoluteMoment mu) (symmetrizationRatio mu)) :=
      measurable_routeBUFrequency _ _
    have hnormalR : Measurable (fun t : ℝ =>
        Real.exp (-((n : ℝ) *
          (routeBUFrequency (thirdAbsoluteMoment mu)
            (symmetrizationRatio mu) t ^ 2 / 2)))) :=
      ((measurable_const.mul ((hu.pow_const 2).div_const 2)).neg).exp
    have hnormalC : Measurable (fun t : ℝ =>
        (Real.exp (-((n : ℝ) *
          (routeBUFrequency (thirdAbsoluteMoment mu)
            (symmetrizationRatio mu) t ^ 2 / 2))) : ℂ)) :=
      Complex.measurable_ofReal.comp hnormalR
    exact ((measurable_const.mul measurable_prawitzKernel.norm).mul
      ((((measurable_charFun (μ := mu)).comp hu).pow_const n).sub
        hnormalC).norm).aestronglyMeasurable
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with t ht
    rw [Set.uIoc_of_le (by norm_num [prawitzSplit] :
      (0 : ℝ) ≤ prawitzSplit)] at ht
    have hnonneg : 0 ≤ lawNormalizedDifferenceIntegrand n mu t := by
      unfold lawNormalizedDifferenceIntegrand
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa only [rho, r, z, mul_assoc] using
      lawNormalizedDifferenceIntegrand_le_envelope
        mu hX hmean hsecond hn ht.1.le

theorem lawNormalizedCorrectionIntegrand_eq_routeB
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (n : ℕ) :
    let rho := thirdAbsoluteMoment mu
    let r := symmetrizationRatio mu
    let z := rho * (r - 1)
    lawNormalizedCorrectionIntegrand n mu =
      routeBNormalizedCorrectionIntegrand n rho z := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrho.ne'
  funext t
  unfold lawNormalizedCorrectionIntegrand
    routeBNormalizedCorrectionIntegrand
  dsimp only
  rw [hrouteR]
  unfold routeBPowerGaussianEnvelope routeBGaussianEnvelope
  rw [← Real.exp_nat_mul]
  congr 2
  ring

theorem intervalIntegrable_lawNormalizedCorrectionIntegrand
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    IntervalIntegrable (lawNormalizedCorrectionIntegrand n mu)
      volume 0 prawitzSplit := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have hz0 : 0 ≤ z := by
    dsimp only [z, rho, r]
    exact mul_nonneg hrho.le <|
      sub_nonneg.mpr (symmetrizationRatio_lower mu hX hmean hsecond)
  have hsource := intervalIntegrable_routeBNormalizedCorrectionIntegrand
    (lt_of_lt_of_le Nat.zero_lt_one hn) hrho hz0
  rw [lawNormalizedCorrectionIntegrand_eq_routeB mu hX hsecond n]
  simpa only [rho, z] using hsource

theorem intervalIntegrable_lawNormalizedLowIntegrand
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    IntervalIntegrable (lawNormalizedLowIntegrand n mu)
      volume 0 prawitzSplit := by
  unfold lawNormalizedLowIntegrand
  exact (intervalIntegrable_lawNormalizedDifferenceIntegrand
    mu hX hmean hsecond hn).add
    (intervalIntegrable_lawNormalizedCorrectionIntegrand
      mu hX hmean hsecond hn)

theorem intervalIntegrable_lawNormalizedHighIntegrand
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (n : ℕ) :
    IntervalIntegrable (lawNormalizedHighIntegrand n mu)
      volume prawitzSplit 1 := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have hbase := prawitz_modulus_envelope_intervalIntegrable n rho z
  have hscaled := hbase.const_mul (2 * Real.sqrt (n : ℝ) / rho)
  refine hscaled.mono_fun' ?_ ?_
  · unfold lawNormalizedHighIntegrand
    have hu : Measurable (routeBUFrequency
        (thirdAbsoluteMoment mu) (symmetrizationRatio mu)) :=
      measurable_routeBUFrequency _ _
    exact ((measurable_const.mul measurable_prawitzKernel.norm).mul
      (((measurable_charFun (μ := mu)).comp
        hu).pow_const n).norm).aestronglyMeasurable
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with t ht
    rw [Set.uIoc_of_le (by norm_num [prawitzSplit] :
      prawitzSplit ≤ (1 : ℝ))] at ht
    have hnonneg : 0 ≤ lawNormalizedHighIntegrand n mu t := by
      unfold lawNormalizedHighIntegrand
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    have ht0 : 0 ≤ t :=
      (by norm_num [prawitzSplit] : 0 ≤ prawitzSplit).trans
        ht.1.le
    simpa only [rho, r, z, mul_assoc] using
      lawNormalizedHighIntegrand_le_envelope
        mu hX hmean hsecond n ht0

lemma certified_w_lo_pos
    {rho z : DyadicInterval}
    (hbox : DyadicRouteBBoxAdmissible rho z) :
    0 < (dyadicCellW rho z).lo := by
  have hrho := hbox.rhoPos
  have hz := hbox.zNonnegative
  change 0 < rho.lo + z.lo
  omega

lemma routeBDboundR_actual
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1) :
    routeBDboundR (thirdAbsoluteMoment mu)
        (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)) =
      symmetrizationRatio mu := by
  have hrho : 0 < thirdAbsoluteMoment mu := by
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  exact routeBDboundR_mul_excess hrho.ne'

/-- Full law-level soundness of one certified the first-absolute-moment bounds cell envelope.  The cell
frequency is the same normalized frequency used by the Prawitz integrand.
No assumption beyond the classical law hypotheses and the ordinary dyadic
cell admissibility facts is introduced. -/
theorem certifiedCellEnvelope_sound
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    {tR : ℝ} (ht0 : 0 ≤ tR)
    (hv : c.v.Contains (routeBCellV tR))
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hW2Den : 0 < (dyadicCellW2 rho z).lo)
    (huBoxLo : 0 ≤
      (DyadicInterval.div c.v (dyadicCellW rho z)).lo) :
    let rhoR := thirdAbsoluteMoment mu
    let rR := symmetrizationRatio mu
    let zR := rhoR * (rR - 1)
    let uR := routeBUFrequency rhoR rR tR
    let env := certifiedCellEnvelope n rho z c
    env.f.Contains ‖charFun mu uR‖ ∧
      env.errorToCos.Contains
        ‖charFun mu uR - (Real.cos uR : ℂ)‖ ∧
      env.cosU.Contains (Real.cos uR) ∧
      env.cosAbs.Contains |Real.cos uR| ∧
      env.normalOne.Contains (Real.exp (-(uR ^ 2 / 2))) ∧
      env.normalN.Contains
        (Real.exp (-((n : ℝ) * (uR ^ 2 / 2)))) := by
  let rhoR := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let zR := rhoR * (rR - 1)
  let uR := routeBUFrequency rhoR rR tR
  let uBox := DyadicInterval.div c.v (dyadicCellW rho z)
  let trig := trigSinCos uBox
  let d := dUpper rho z
  let real := realInterval rho d uBox trig.1 trig.2
  let imag := imagInterval rho z d uBox trig.1 trig.2
  let rectangular := rectangularEnvelope real imag
  let routeA := dyadicCellA rho z c
  let f := minModulusEnvelope routeA rectangular
  let realRadius := finiteRealRadius d uBox trig.1
  let errorToCos :=
    errorToCosEnvelope real realRadius imag trig.2
  let env := certifiedCellEnvelope n rho z c
  have hrhoR : 0 < rhoR := by
    dsimp only [rhoR]
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have hzR0 : 0 ≤ zR := hbox.real_z_nonnegative hz
  have hW : (dyadicCellW rho z).Contains
      (routeBDboundW rhoR zR) := dyadicCellW_sound hrho hz
  have hWLo : 0 < (dyadicCellW rho z).lo :=
    certified_w_lo_pos hbox
  have hWPos : 0 < routeBDboundW rhoR zR := by
    unfold routeBDboundW
    linarith
  have hrouteR : routeBDboundR rhoR zR = rR := by
    dsimp only [rhoR, rR, zR]
    exact routeBDboundR_actual mu hX hsecond
  have huEq : uR = routeBCellV tR / routeBDboundW rhoR zR := by
    have hfreq := routeBCell_frequency_identity
      (rho := rhoR) (z := zR) (t := tR) hrhoR
    rw [hrouteR] at hfreq
    exact hfreq
  have hu : uBox.Contains uR := by
    have hdiv := hv.div hW hW.ordered hWLo
    simpa only [uBox, huEq] using hdiv
  have hradial := finiteRadialEnvelopes_sound
    mu hX hmean hsecond hrho hz hbox.rhoPos huBoxLo hu
  have hrouteA : routeA.Contains
      (routeBCellA rhoR zR c.hq.lower) := by
    simpa only [routeA] using dyadicCellA_sound hrho hz hW2Den
  have hrouteBase : ‖charFun mu uR‖ ≤
      routeBModulusEnvelope routeBKappa routeBTheta rhoR rR tR := by
    simpa only [rhoR, rR, uR] using
      routeB_charFun_norm_le_modulusEnvelope
        mu hX hmean hsecond routeB_exactMinorantCertificate ht0
  have hrouteCell :
      routeBModulusEnvelope routeBKappa routeBTheta rhoR rR tR ≤
        routeBCellA rhoR zR c.hq.lower := by
    have h := routeBCell_modulus_le hrhoR hWPos hhq
    rw [hrouteR] at h
    exact h
  have hrect : rectangular.Contains ‖charFun mu uR‖ := by
    simpa only [trig, d, real, imag, rectangular] using hradial.1
  have herror : errorToCos.Contains
      ‖charFun mu uR - (Real.cos uR : ℂ)‖ := by
    simpa only [trig, d, real, imag, realRadius, errorToCos] using hradial.2
  have hf : f.Contains ‖charFun mu uR‖ := by
    exact minModulusEnvelope_sound hrouteA hrect
      (norm_nonneg _) (norm_charFun_le_one uR)
      (hrouteBase.trans hrouteCell) le_rfl
  have htrig := trigSinCos_sound hu huBoxLo
  have hcosAbs : (absHull trig.2).Contains |Real.cos uR| := by
    simpa only [trig] using absHull_sound htrig.2
  have hnormalOne : (normalOne uBox).Contains
      (Real.exp (-(uR ^ 2 / 2))) := normalOne_sound hu
  have hnormalN : (normalN n uBox).Contains
      (Real.exp (-((n : ℝ) * (uR ^ 2 / 2)))) := normalN_sound hu
  simpa only [env, certifiedCellEnvelope, uBox, trig, d, real,
    imag, rectangular, routeA, f, realRadius, errorToCos] using
    ⟨hf, herror, htrig.2, hcosAbs, hnormalOne, hnormalN⟩

/-- The additional Rademacher-reference branch evaluated by the exact checker
is a rigorous upper bound for the one-step power difference. -/
theorem certifiedRademacherDifference_upper
    {n : ℕ} (hn : 1 ≤ n)
    {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    {tR : ℝ} (ht0 : 0 ≤ tR)
    (hv : c.v.Contains (routeBCellV tR))
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hW2Den : 0 < (dyadicCellW2 rho z).lo)
    (huBoxLo : 0 ≤
      (DyadicInterval.div c.v (dyadicCellW rho z)).lo) :
    let rhoR := thirdAbsoluteMoment mu
    let rR := symmetrizationRatio mu
    let uR := routeBUFrequency rhoR rR tR
    let env := certifiedCellEnvelope n rho z c
    ‖(charFun mu uR) ^ n -
        (Real.exp (-((n : ℝ) * (uR ^ 2 / 2))) : ℂ)‖ ≤
      (certifiedRademacherDifference n env).upper := by
  let rhoR := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let uR := routeBUFrequency rhoR rR tR
  let env := certifiedCellEnvelope n rho z c
  have henv := certifiedCellEnvelope_sound
    (n := n) mu hX hmean hsecond hrho hz hbox ht0 hv hhq hW2Den huBoxLo
  change ‖(charFun mu uR) ^ n -
      (Real.exp (-((n : ℝ) * (uR ^ 2 / 2))) : ℂ)‖ ≤
    (certifiedRademacherDifference n env).upper
  dsimp only [rhoR, rR, uR, env] at henv
  rcases henv with ⟨hf, herror, hcos, hcosAbs, _hnormalOne, hnormalN⟩
  simpa only [certifiedRademacherDifference,
    rademacherDifferenceIntervals] using
    rademacherDifferenceIntervals_upper hn hf herror hcos hcosAbs hnormalN

/-- Soundness of the high-frequency loop body used by the discovery checker,
now stated directly for the actual characteristic function. -/
theorem certified_high_integrand_le_cell_upper
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    {tR : ℝ} (ht0 : 0 < tR) (ht1 : tR ≤ 1)
    (hv : c.v.Contains (routeBCellV tR))
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hkh2 : c.kh2.Contains (prawitzKH2Envelope tR))
    (hW2Den : 0 < (dyadicCellW2 rho z).lo)
    (huBoxLo : 0 ≤
      (DyadicInterval.div c.v (dyadicCellW rho z)).lo) :
    let rhoR := thirdAbsoluteMoment mu
    let rR := symmetrizationRatio mu
    let uR := routeBUFrequency rhoR rR tR
    2 * Real.sqrt (n : ℝ) / rhoR * ‖prawitzKernel tR‖ *
        ‖charFun mu uR ^ n‖ ≤
      (certifiedSharedHighCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).upper := by
  let rhoR := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let uR := routeBUFrequency rhoR rR tR
  let env := certifiedCellEnvelope n rho z c
  have henv := certifiedCellEnvelope_sound
    (n := n) mu hX hmean hsecond hrho hz hbox ht0.le hv hhq
      hW2Den huBoxLo
  dsimp only [rhoR, rR, uR] at henv
  rcases henv with ⟨hf, _herror, _hcos, _hcosAbs,
    _hnormalOne, _hnormalN⟩
  have hsn := dyadicCellSqrtN_sound n
  have hp := dyadicCellP_sound hrho hbox.rhoPos
  have hsnP :
      (dyadicRouteBBuildBoxState n rho z).snP.Contains
        (Real.sqrt (n : ℝ) * (1 / rhoR)) := by
    simpa only [dyadicRouteBBuildBoxState, rhoR] using hsn.mul hp
  have hM : (powi env.f n).Contains (‖charFun mu uR‖ ^ n) := by
    simpa only [env, rhoR, rR, uR] using powi_sound hf n
  have hproduct := hsnP.mul (hkh2.mul hM)
  have hrhoR : 0 < rhoR := by
    dsimp only [rhoR]
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have hkernel : 2 * ‖prawitzKernel tR‖ ≤
      prawitzKH2Envelope tR :=
    two_mul_norm_prawitzKernel_le_KH2Envelope ht0 ht1
  have hscale0 : 0 ≤ Real.sqrt (n : ℝ) * (1 / rhoR) := by positivity
  have hpow0 : 0 ≤ ‖charFun mu uR‖ ^ n := pow_nonneg (norm_nonneg _) n
  calc
    2 * Real.sqrt (n : ℝ) / rhoR * ‖prawitzKernel tR‖ *
        ‖charFun mu uR ^ n‖ =
      (Real.sqrt (n : ℝ) * (1 / rhoR)) *
        (2 * ‖prawitzKernel tR‖) * ‖charFun mu uR‖ ^ n := by
          rw [norm_pow]
          ring
    _ ≤ (Real.sqrt (n : ℝ) * (1 / rhoR)) *
        prawitzKH2Envelope tR * ‖charFun mu uR‖ ^ n := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkernel hscale0) hpow0
    _ ≤ (certifiedSharedHighCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).upper := by
      simpa only [certifiedSharedHighCellValue, env, mul_assoc] using
        hproduct.2

/-- Soundness of the unchanged Gaussian correction term in the low-frequency
loop, using the the first-absolute-moment bounds cell's exact Gaussian enclosure. -/
theorem certified_correction_integrand_le_cell_upper
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    {tR : ℝ} (ht0 : 0 ≤ tR) (ht1 : tR < 1)
    (hv : c.v.Contains (routeBCellV tR))
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hkd2 : c.kd2.Contains (prawitzKD2Envelope tR))
    (hW2Den : 0 < (dyadicCellW2 rho z).lo)
    (huBoxLo : 0 ≤
      (DyadicInterval.div c.v (dyadicCellW rho z)).lo) :
    let rhoR := thirdAbsoluteMoment mu
    let rR := symmetrizationRatio mu
    let uR := routeBUFrequency rhoR rR tR
    2 * Real.sqrt (n : ℝ) / rhoR *
        ‖prawitzKernelCorrection tR‖ *
        Real.exp (-((n : ℝ) * (uR ^ 2 / 2))) ≤
      (certifiedCorrectionCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).upper := by
  let rhoR := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let uR := routeBUFrequency rhoR rR tR
  let env := certifiedCellEnvelope n rho z c
  have henv := certifiedCellEnvelope_sound
    (n := n) mu hX hmean hsecond hrho hz hbox ht0 hv hhq
      hW2Den huBoxLo
  dsimp only [rhoR, rR, uR] at henv
  rcases henv with ⟨_hf, _herror, _hcos, _hcosAbs,
    _hnormalOne, hnormalN⟩
  have hsn := dyadicCellSqrtN_sound n
  have hp := dyadicCellP_sound hrho hbox.rhoPos
  have hsnP :
      (dyadicRouteBBuildBoxState n rho z).snP.Contains
        (Real.sqrt (n : ℝ) * (1 / rhoR)) := by
    simpa only [dyadicRouteBBuildBoxState, rhoR] using hsn.mul hp
  have hproduct := hsnP.mul (hkd2.mul hnormalN)
  have hrhoR : 0 < rhoR := by
    dsimp only [rhoR]
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have hkernel : 2 * ‖prawitzKernelCorrection tR‖ ≤
      prawitzKD2Envelope tR :=
    two_mul_norm_prawitzKernelCorrection_le_KD2Envelope ht0 ht1
  have hscale0 : 0 ≤ Real.sqrt (n : ℝ) * (1 / rhoR) := by positivity
  have hnormal0 :
      0 ≤ Real.exp (-((n : ℝ) * (uR ^ 2 / 2))) :=
    (Real.exp_pos _).le
  calc
    2 * Real.sqrt (n : ℝ) / rhoR *
        ‖prawitzKernelCorrection tR‖ *
        Real.exp (-((n : ℝ) * (uR ^ 2 / 2))) =
      (Real.sqrt (n : ℝ) * (1 / rhoR)) *
        (2 * ‖prawitzKernelCorrection tR‖) *
        Real.exp (-((n : ℝ) * (uR ^ 2 / 2))) := by ring
    _ ≤ (Real.sqrt (n : ℝ) * (1 / rhoR)) *
        prawitzKD2Envelope tR *
        Real.exp (-((n : ℝ) * (uR ^ 2 / 2))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkernel hscale0) hnormal0
    _ ≤ (certifiedCorrectionCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).upper := by
      simpa only [certifiedCorrectionCellValue, env, mul_assoc] using
        hproduct.2

/-- After dividing by the positive cell coordinate, the exact Rademacher
branch bounds the normalized low-frequency power-difference integrand. -/
theorem certified_rademacher_integrand_le_cell_upper
    {n : ℕ} (hn : 1 ≤ n)
    {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    {tR : ℝ} (ht : c.t.Contains tR) (ht1 : tR < 1)
    (hv : c.v.Contains (routeBCellV tR))
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hk0 : c.k0.Contains (prawitzK0Envelope tR))
    (hW2Den : 0 < (dyadicCellW2 rho z).lo)
    (huBoxLo : 0 ≤
      (DyadicInterval.div c.v (dyadicCellW rho z)).lo)
    (htLo : 0 < c.t.lo) :
    let rhoR := thirdAbsoluteMoment mu
    let rR := symmetrizationRatio mu
    let uR := routeBUFrequency rhoR rR tR
    let normalR := Real.exp (-((n : ℝ) * (uR ^ 2 / 2)))
    2 * Real.sqrt (n : ℝ) / rhoR * ‖prawitzKernel tR‖ *
        ‖charFun mu uR ^ n - (normalR : ℂ)‖ ≤
      (certifiedRademacherCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).upper := by
  let rhoR := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let uR := routeBUFrequency rhoR rR tR
  let normalR := Real.exp (-((n : ℝ) * (uR ^ 2 / 2)))
  let env := certifiedCellEnvelope n rho z c
  let radR :=
    (n : ℝ) * ‖charFun mu uR - (Real.cos uR : ℂ)‖ *
        max ‖charFun mu uR‖ |Real.cos uR| ^ (n - 1) +
      |Real.cos uR ^ n - normalR|
  have hcLowerPos : 0 < c.t.lower := by
    unfold DyadicInterval.lower
    exact div_pos (by exact_mod_cast htLo)
      (by exact_mod_cast dyadicScale_pos)
  have htRPos : 0 < tR := hcLowerPos.trans_le ht.1
  have henv := certifiedCellEnvelope_sound
    (n := n) mu hX hmean hsecond hrho hz hbox htRPos.le hv hhq
      hW2Den huBoxLo
  dsimp only [rhoR, rR, uR] at henv
  rcases henv with ⟨hf, herror, hcos, hcosAbs,
    _hnormalOne, hnormalN⟩
  have hrad : (certifiedRademacherDifference n env).Contains radR := by
    simpa only [certifiedRademacherDifference, env, radR, normalR] using
      rademacherDifferenceIntervals_sound hf herror hcos hcosAbs
        hnormalN (norm_nonneg _) (norm_nonneg _)
  have hdiff : ‖charFun mu uR ^ n - (normalR : ℂ)‖ ≤ radR := by
    simpa only [radR] using
      rademacher_power_difference_le
        (a := charFun mu uR) (c := Real.cos uR) (g := normalR) hn
  have hrad0 : 0 ≤ radR := (norm_nonneg _).trans hdiff
  have hquot := hrad.div ht ht.ordered htLo
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hsn := dyadicCellSqrtN_sound n
  have hp := dyadicCellP_sound hrho hbox.rhoPos
  have htwoSnP :
      (dyadicRouteBBuildBoxState n rho z).twoSnP.Contains
        (2 * Real.sqrt (n : ℝ) * (1 / rhoR)) := by
    simpa only [dyadicRouteBBuildBoxState, rhoR,
      DyadicInterval.mulPoint_eq_mul, mul_assoc] using (htwo.mul hsn).mul hp
  have hbranch := htwoSnP.mul (hk0.mul hquot)
  have hrhoR : 0 < rhoR := by
    dsimp only [rhoR]
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have hkernel : tR * ‖prawitzKernel tR‖ ≤
      prawitzK0Envelope tR :=
    t_mul_norm_prawitzKernel_le_K0Envelope htRPos.le ht1
  have hk0R0 : 0 ≤ prawitzK0Envelope tR :=
    (mul_nonneg htRPos.le (norm_nonneg _)).trans hkernel
  have hkdiv : ‖prawitzKernel tR‖ ≤
      prawitzK0Envelope tR / tR := by
    apply (le_div_iff₀ htRPos).2
    simpa only [mul_comm] using hkernel
  have hscale0 : 0 ≤ 2 * Real.sqrt (n : ℝ) / rhoR := by positivity
  have hkdiv0 : 0 ≤ prawitzK0Envelope tR / tR :=
    div_nonneg hk0R0 htRPos.le
  calc
    2 * Real.sqrt (n : ℝ) / rhoR * ‖prawitzKernel tR‖ *
        ‖charFun mu uR ^ n - (normalR : ℂ)‖ ≤
      (2 * Real.sqrt (n : ℝ) / rhoR) *
        (prawitzK0Envelope tR / tR) * radR := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hkdiv hscale0) hdiff
        (norm_nonneg _)
        (mul_nonneg hscale0 hkdiv0)
    _ = (2 * Real.sqrt (n : ℝ) * (1 / rhoR)) *
        (prawitzK0Envelope tR * (radR / tR)) := by
      field_simp [htRPos.ne']
    _ ≤ (certifiedRademacherCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).upper := by
      simpa only [certifiedRademacherCellValue, env, if_pos htLo,
        mul_assoc] using hbranch.2

/-- The direct triangle-inequality branch remains sound after replacing the
old modulus envelope by the smaller certified the first-absolute-moment bounds modulus enclosure. -/
theorem certified_trivial_integrand_le_cell_upper
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    {tR : ℝ} (ht : c.t.Contains tR) (ht1 : tR < 1)
    (hv : c.v.Contains (routeBCellV tR))
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hk0 : c.k0.Contains (prawitzK0Envelope tR))
    (hW2Den : 0 < (dyadicCellW2 rho z).lo)
    (huBoxLo : 0 ≤
      (DyadicInterval.div c.v (dyadicCellW rho z)).lo)
    (htLo : 0 < c.t.lo) :
    let rhoR := thirdAbsoluteMoment mu
    let rR := symmetrizationRatio mu
    let uR := routeBUFrequency rhoR rR tR
    let normalR := Real.exp (-((n : ℝ) * (uR ^ 2 / 2)))
    2 * Real.sqrt (n : ℝ) / rhoR * ‖prawitzKernel tR‖ *
        ‖charFun mu uR ^ n - (normalR : ℂ)‖ ≤
      (certifiedTrivialCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).upper := by
  let rhoR := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let uR := routeBUFrequency rhoR rR tR
  let normalR := Real.exp (-((n : ℝ) * (uR ^ 2 / 2)))
  let env := certifiedCellEnvelope n rho z c
  let sumR := ‖charFun mu uR‖ ^ n + normalR
  have hcLowerPos : 0 < c.t.lower := by
    unfold DyadicInterval.lower
    exact div_pos (by exact_mod_cast htLo)
      (by exact_mod_cast dyadicScale_pos)
  have htRPos : 0 < tR := hcLowerPos.trans_le ht.1
  have henv := certifiedCellEnvelope_sound
    (n := n) mu hX hmean hsecond hrho hz hbox htRPos.le hv hhq
      hW2Den huBoxLo
  dsimp only [rhoR, rR, uR] at henv
  rcases henv with ⟨hf, _herror, _hcos, _hcosAbs,
    _hnormalOne, hnormalN⟩
  have hM : (powi env.f n).Contains (‖charFun mu uR‖ ^ n) := by
    simpa only [env] using powi_sound hf n
  have hsum : (DyadicInterval.add (powi env.f n) env.normalN).Contains
      sumR := by
    simpa only [env, sumR] using hM.add hnormalN
  have hquot := hsum.div ht ht.ordered htLo
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hsn := dyadicCellSqrtN_sound n
  have hp := dyadicCellP_sound hrho hbox.rhoPos
  have htwoSnP :
      (dyadicRouteBBuildBoxState n rho z).twoSnP.Contains
        (2 * Real.sqrt (n : ℝ) * (1 / rhoR)) := by
    simpa only [dyadicRouteBBuildBoxState, rhoR,
      DyadicInterval.mulPoint_eq_mul, mul_assoc] using (htwo.mul hsn).mul hp
  have hbranch := htwoSnP.mul (hk0.mul hquot)
  have hrhoR : 0 < rhoR := by
    dsimp only [rhoR]
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have hnormal0 : 0 ≤ normalR := by
    dsimp only [normalR]
    exact (Real.exp_pos _).le
  have hsum0 : 0 ≤ sumR := by
    dsimp only [sumR]
    exact add_nonneg (pow_nonneg (norm_nonneg _) n) hnormal0
  have hdiff : ‖charFun mu uR ^ n - (normalR : ℂ)‖ ≤ sumR := by
    calc
      ‖charFun mu uR ^ n - (normalR : ℂ)‖ ≤
          ‖charFun mu uR ^ n‖ + ‖(normalR : ℂ)‖ := norm_sub_le _ _
      _ = sumR := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hnormal0]
  have hkernel : tR * ‖prawitzKernel tR‖ ≤
      prawitzK0Envelope tR :=
    t_mul_norm_prawitzKernel_le_K0Envelope htRPos.le ht1
  have hk0R0 : 0 ≤ prawitzK0Envelope tR :=
    (mul_nonneg htRPos.le (norm_nonneg _)).trans hkernel
  have hkdiv : ‖prawitzKernel tR‖ ≤
      prawitzK0Envelope tR / tR := by
    apply (le_div_iff₀ htRPos).2
    simpa only [mul_comm] using hkernel
  have hscale0 : 0 ≤ 2 * Real.sqrt (n : ℝ) / rhoR := by positivity
  have hkdiv0 : 0 ≤ prawitzK0Envelope tR / tR :=
    div_nonneg hk0R0 htRPos.le
  calc
    2 * Real.sqrt (n : ℝ) / rhoR * ‖prawitzKernel tR‖ *
        ‖charFun mu uR ^ n - (normalR : ℂ)‖ ≤
      (2 * Real.sqrt (n : ℝ) / rhoR) *
        (prawitzK0Envelope tR / tR) * sumR := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hkdiv hscale0) hdiff
        (norm_nonneg _)
        (mul_nonneg hscale0 hkdiv0)
    _ = (2 * Real.sqrt (n : ℝ) * (1 / rhoR)) *
        (prawitzK0Envelope tR * (sumR / tR)) := by
      field_simp [htRPos.ne']
    _ ≤ (certifiedTrivialCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).upper := by
      simpa only [certifiedTrivialCellValue, env, if_pos htLo,
        mul_assoc] using hbranch.2

/-- Endpoint-safe telescoping branch.  The proof exposes the cancellation
`t * ‖K(t)‖` and certifies every remaining box-dependent factor. -/
theorem certified_telescoping_integrand_le_cell_upper
    {n : ℕ} (hn : 1 ≤ n)
    {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    {tR : ℝ} (ht : c.t.Contains tR) (ht0 : 0 ≤ tR) (ht1 : tR < 1)
    (hv : c.v.Contains (routeBCellV tR))
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hk0 : c.k0.Contains (prawitzK0Envelope tR))
    (hW2Den : 0 < (dyadicCellW2 rho z).lo)
    (hBDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (dyadicCellW2 rho z)).lo)
    (hCDen : 0 < (DyadicInterval.mul (DyadicInterval.point 4)
      (dyadicCellW rho z)).lo)
    (hW3Den : 0 < (powi (dyadicCellW rho z) 3).lo)
    (hy3 : routeBDboundY (thirdAbsoluteMoment mu)
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1))
      (routeBCellV tR) ≤ 3)
    (huBoxLo : 0 ≤
      (DyadicInterval.div c.v (dyadicCellW rho z)).lo) :
    let rhoR := thirdAbsoluteMoment mu
    let rR := symmetrizationRatio mu
    let uR := routeBUFrequency rhoR rR tR
    let normalOneR := Real.exp (-(uR ^ 2 / 2))
    let normalNR := Real.exp (-((n : ℝ) * (uR ^ 2 / 2)))
    2 * Real.sqrt (n : ℝ) / rhoR * ‖prawitzKernel tR‖ *
        ‖charFun mu uR ^ n - (normalNR : ℂ)‖ ≤
      (certifiedTelescopingCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).upper := by
  let rhoR := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let zR := rhoR * (rR - 1)
  let W := routeBDboundW rhoR zR
  let uR := routeBUFrequency rhoR rR tR
  let normalOneR := Real.exp (-(uR ^ 2 / 2))
  let normalNR := Real.exp (-((n : ℝ) * (uR ^ 2 / 2)))
  let env := certifiedCellEnvelope n rho z c
  let H := max ‖charFun mu uR‖ normalOneR ^ (n - 1)
  let D := routeBDiskBound routeBKappa rhoR rR (2 * Real.pi * tR / rR)
  let branchR :=
    2 * (n : ℝ) * Real.sqrt (n : ℝ) * prawitzK0Envelope tR *
      (tR ^ 2 * (2 * Real.pi) ^ 3) * (D / W ^ 3) * H
  have hrhoR : 0 < rhoR := by
    dsimp only [rhoR]
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have hrR : 0 < rR := by
    dsimp only [rR]
    linarith [symmetrizationRatio_lower mu hX hmean hsecond]
  have hzR0 : 0 ≤ zR := hbox.real_z_nonnegative hz
  have hzRle : zR ≤ rhoR := hbox.real_z_le_rho hrho hz
  have hWPos : 0 < W := by
    dsimp only [W, routeBDboundW]
    linarith
  have hWEq : W = rhoR * rR := by
    dsimp only [W, zR, routeBDboundW]
    ring
  have hrouteR : routeBDboundR rhoR zR = rR := by
    dsimp only [rhoR, rR, zR]
    exact routeBDboundR_actual mu hX hsecond
  have huCell : uR = routeBCellV tR / W := by
    have hfreq := routeBCell_frequency_identity
      (rho := rhoR) (z := zR) (t := tR) hrhoR
    rw [hrouteR] at hfreq
    simpa only [uR, W] using hfreq
  have henv := certifiedCellEnvelope_sound
    (n := n) mu hX hmean hsecond hrho hz hbox ht0 hv hhq
      hW2Den huBoxLo
  dsimp only [rhoR, rR, uR] at henv
  rcases henv with ⟨hf, _herror, _hcos, _hcosAbs,
    hnormalOne, _hnormalN⟩
  have hbase :
      (dyadicCellNonnegativeHull env.f env.normalOne).Contains
        (max ‖charFun mu uR‖ normalOneR) := by
    simpa only [env, normalOneR] using
      dyadicCellNonnegativeHull_contains hf hnormalOne
        (norm_nonneg _) (Real.exp_pos _).le
  have hH :
      (powi (dyadicCellNonnegativeHull env.f env.normalOne) (n - 1)).Contains H := by
    simpa only [H] using powi_sound hbase (n - 1)
  have hyDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (DyadicInterval.sqr (dyadicCellW rho z))).lo := by
    simpa only [dyadicCellW2] using hBDen
  have hv0 : 0 ≤ routeBCellV tR := by
    unfold routeBCellV
    positivity
  have hDCanonical := dyadicCellD_sound hrho hz hv hbox.rhoPos
    hyDen hCDen hrhoR hzR0 hzRle hv0 hy3
  have hD :
      (dyadicRouteBDboundFromBoxState
        (dyadicRouteBBuildBoxState n rho z) c.v).Contains D := by
    rw [dyadicRouteBDboundFromBoxState_eq, dyadicPrawitzDboundShared_eq]
    have hfrequency :
        routeBDboundFrequency rhoR zR (routeBCellV tR) =
          2 * Real.pi * tR / rR := by
      unfold routeBDboundFrequency routeBCellV
      rw [hrouteR]
    rw [hrouteR, hfrequency] at hDCanonical
    simpa only [D] using hDCanonical
  have h2n : (DyadicInterval.point (Int.ofNat (2 * n))).Contains
      (2 * (n : ℝ)) := by
    convert DyadicInterval.contains_point (Int.ofNat (2 * n)) using 1
    norm_num [Nat.cast_mul]
  have hsn := dyadicCellSqrtN_sound n
  have hprefactor :
      (dyadicRouteBBuildBoxState n rho z).prefactor.Contains
        (2 * (n : ℝ) * Real.sqrt (n : ℝ)) := by
    simpa only [dyadicRouteBBuildBoxState,
      DyadicInterval.mulPoint_eq_mul] using h2n.mul hsn
  have hwithKernel := hprefactor.mul hk0
  have ht2 := ht.sqr ht.ordered
  have hfrequency := ht2.mul dyadicCellTwoPiCubed_sound
  have hwithFrequency := hwithKernel.mul hfrequency
  have hWBox := dyadicCellW_sound hrho hz
  have hW3 := powi_sound hWBox 3
  have hDScale := hD.div hW3 hW3.ordered hW3Den
  have hbranchContains := (hwithFrequency.mul hDScale).mul hH
  have hbranchUpper : branchR ≤
      (certifiedTelescopingCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).upper := by
    simpa only [certifiedTelescopingCellValue, env, branchR, W,
      mul_assoc] using hbranchContains.2
  have hgaussianNorm :
      ‖Complex.exp (-(uR : ℂ) ^ 2 / 2)‖ = normalOneR := by
    rw [complex_gaussian_eq_real, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    dsimp only [normalOneR]
    congr 1
    ring
  have hpower := norm_pow_sub_pow_le_nat
    (a := charFun mu uR) (b := Complex.exp (-(uR : ℂ) ^ 2 / 2))
    (M := max ‖charFun mu uR‖ normalOneR) hn
    (le_max_left ‖charFun mu uR‖ normalOneR)
    (by rw [hgaussianNorm]
        exact le_max_right _ _)
  have hone := routeB_one_step_at_smoothing_frequency
    mu hX hmean hsecond routeB_exactMinorantCertificate ht0
  have hone' :
      ‖charFun mu uR - Complex.exp (-(uR : ℂ) ^ 2 / 2)‖ ≤
        rhoR * uR ^ 3 * D := by
    simpa only [rhoR, rR, uR, D] using hone
  have hH0 : 0 ≤ H := by
    dsimp only [H]
    exact pow_nonneg ((norm_nonneg _).trans (le_max_left _ _)) (n - 1)
  have hraw :
      ‖charFun mu uR ^ n - (normalNR : ℂ)‖ ≤
        (n : ℝ) * (rhoR * uR ^ 3 * D) * H := by
    have hnormalPow :
        (Complex.exp (-(uR : ℂ) ^ 2 / 2)) ^ n = (normalNR : ℂ) := by
      rw [← Complex.exp_nat_mul]
      rw [show (n : ℂ) * (-(uR : ℂ) ^ 2 / 2) =
          (-((n : ℝ) * (uR ^ 2 / 2)) : ℝ) by
        push_cast
        ring]
      exact (Complex.ofReal_exp _).symm
    rw [← hnormalPow]
    exact hpower.trans <| mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hone' (Nat.cast_nonneg n)) hH0
  have hkernel : tR * ‖prawitzKernel tR‖ ≤
      prawitzK0Envelope tR :=
    t_mul_norm_prawitzKernel_le_K0Envelope ht0 ht1
  have hscale0 :
      0 ≤ 2 * Real.sqrt (n : ℝ) / rhoR * ‖prawitzKernel tR‖ := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hraw hscale0
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact routeBDiskBound_nonneg _ _ _ _
  have hfreqFactor0 : 0 ≤ tR ^ 2 * (2 * Real.pi) ^ 3 :=
    mul_nonneg (sq_nonneg tR) (pow_nonneg (by positivity) 3)
  have hDScale0 : 0 ≤ D / W ^ 3 :=
    div_nonneg hD0 (pow_nonneg hWPos.le 3)
  have htail0 :
      0 ≤ (tR ^ 2 * (2 * Real.pi) ^ 3) * (D / W ^ 3) * H :=
    mul_nonneg (mul_nonneg hfreqFactor0 hDScale0) hH0
  have hpref0 : 0 ≤ 2 * (n : ℝ) * Real.sqrt (n : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
      (Real.sqrt_nonneg _)
  calc
    2 * Real.sqrt (n : ℝ) / rhoR * ‖prawitzKernel tR‖ *
        ‖charFun mu uR ^ n - (normalNR : ℂ)‖ ≤
      (2 * Real.sqrt (n : ℝ) / rhoR * ‖prawitzKernel tR‖) *
        ((n : ℝ) * (rhoR * uR ^ 3 * D) * H) := by
      simpa only [mul_assoc] using hscaled
    _ = 2 * (n : ℝ) * Real.sqrt (n : ℝ) *
        (tR * ‖prawitzKernel tR‖) *
        (tR ^ 2 * (2 * Real.pi) ^ 3) * (D / W ^ 3) * H := by
      rw [huCell]
      simp only [routeBCellV]
      field_simp [hrhoR.ne', hWPos.ne']
    _ = (2 * (n : ℝ) * Real.sqrt (n : ℝ)) *
        (tR * ‖prawitzKernel tR‖) *
        ((tR ^ 2 * (2 * Real.pi) ^ 3) * (D / W ^ 3) * H) := by ring
    _ ≤ (2 * (n : ℝ) * Real.sqrt (n : ℝ)) *
        prawitzK0Envelope tR *
        ((tR ^ 2 * (2 * Real.pi) ^ 3) * (D / W ^ 3) * H) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkernel hpref0) htail0
    _ = branchR := by
      dsimp only [branchR]
      ring
    _ ≤ (certifiedTelescopingCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).upper :=
      hbranchUpper

/-- Complete low-frequency loop body: the minimum of the endpoint-safe,
triangle, and Rademacher branches plus the Gaussian correction.  The explicit
`hHuge` hypothesis is a new checker-side obligation for the cell touching
zero; unlike the discovery prototype, the certified checker must verify it. -/
theorem certified_low_integrand_le_cell_upper
    {n : ℕ} (hn : 1 ≤ n)
    {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    {tR : ℝ} (ht : c.t.Contains tR) (ht0 : 0 ≤ tR) (ht1 : tR < 1)
    (hv : c.v.Contains (routeBCellV tR))
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hk0 : c.k0.Contains (prawitzK0Envelope tR))
    (hkd2 : c.kd2.Contains (prawitzKD2Envelope tR))
    (hW2Den : 0 < (dyadicCellW2 rho z).lo)
    (hBDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (dyadicCellW2 rho z)).lo)
    (hCDen : 0 < (DyadicInterval.mul (DyadicInterval.point 4)
      (dyadicCellW rho z)).lo)
    (hW3Den : 0 < (powi (dyadicCellW rho z) 3).lo)
    (hy3 : routeBDboundY (thirdAbsoluteMoment mu)
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1))
      (routeBCellV tR) ≤ 3)
    (huBoxLo : 0 ≤
      (DyadicInterval.div c.v (dyadicCellW rho z)).lo)
    (hHuge : ¬ 0 < c.t.lo →
      (certifiedTelescopingCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).hi ≤
        dyadicCellHuge.hi) :
    let rhoR := thirdAbsoluteMoment mu
    let rR := symmetrizationRatio mu
    let uR := routeBUFrequency rhoR rR tR
    let normalNR := Real.exp (-((n : ℝ) * (uR ^ 2 / 2)))
    2 * Real.sqrt (n : ℝ) / rhoR * ‖prawitzKernel tR‖ *
          ‖charFun mu uR ^ n - (normalNR : ℂ)‖ +
        2 * Real.sqrt (n : ℝ) / rhoR *
          ‖prawitzKernelCorrection tR‖ * normalNR ≤
      (certifiedSharedLowCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).upper := by
  let rhoR := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let uR := routeBUFrequency rhoR rR tR
  let normalNR := Real.exp (-((n : ℝ) * (uR ^ 2 / 2)))
  let state := dyadicRouteBBuildBoxState n rho z
  let telescoping := certifiedTelescopingCellValue state n rho z c
  let trivial := certifiedTrivialCellValue state n rho z c
  let rademacher := certifiedRademacherCellValue state n rho z c
  let correction := certifiedCorrectionCellValue state n rho z c
  let differenceR :=
    2 * Real.sqrt (n : ℝ) / rhoR * ‖prawitzKernel tR‖ *
      ‖charFun mu uR ^ n - (normalNR : ℂ)‖
  have hTel : differenceR ≤ telescoping.upper := by
    simpa only [rhoR, rR, uR, normalNR, state, telescoping, differenceR] using
      certified_telescoping_integrand_le_cell_upper
        (n := n) (rho := rho) (z := z) (c := c) hn
        mu hX hmean hsecond hrho hz hbox ht ht0 ht1 hv hhq hk0
        hW2Den hBDen hCDen hW3Den hy3 huBoxLo
  have hCorrection :
      2 * Real.sqrt (n : ℝ) / rhoR *
          ‖prawitzKernelCorrection tR‖ * normalNR ≤ correction.upper := by
    simpa only [rhoR, rR, uR, normalNR, state, correction] using
      certified_correction_integrand_le_cell_upper
        (n := n) (rho := rho) (z := z) (c := c)
        mu hX hmean hsecond hrho hz hbox ht0 ht1 hv hhq hkd2
        hW2Den huBoxLo
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  have hF1 : differenceR ≤
      ((min telescoping.hi (min trivial.hi rademacher.hi) : ℤ) : ℝ) /
        (dyadicScale : ℝ) := by
    rw [Int.cast_min, Int.cast_min,
      ← min_div_div_right hscale.le, ← min_div_div_right hscale.le]
    by_cases htLo : 0 < c.t.lo
    · have hTrivial : differenceR ≤ trivial.upper := by
        simpa only [rhoR, rR, uR, normalNR, state, trivial, differenceR] using
          certified_trivial_integrand_le_cell_upper
            (n := n) (rho := rho) (z := z) (c := c)
            mu hX hmean hsecond hrho hz hbox ht ht1 hv hhq hk0
            hW2Den huBoxLo htLo
      have hRademacher : differenceR ≤ rademacher.upper := by
        simpa only [rhoR, rR, uR, normalNR, state, rademacher,
          differenceR] using
          certified_rademacher_integrand_le_cell_upper
            (n := n) (rho := rho) (z := z) (c := c) hn
            mu hX hmean hsecond hrho hz hbox ht ht1 hv hhq hk0
            hW2Den huBoxLo htLo
      exact le_min hTel (le_min hTrivial hRademacher)
    · have hTelHuge : telescoping.upper ≤ dyadicCellHuge.upper := by
        exact div_le_div_of_nonneg_right
          (by exact_mod_cast hHuge htLo) hscale.le
      have hTrivial : differenceR ≤ trivial.upper := by
        rw [show trivial = dyadicCellHuge by
          simp only [trivial, certifiedTrivialCellValue, htLo,
            if_false]]
        exact hTel.trans hTelHuge
      have hRademacher : differenceR ≤ rademacher.upper := by
        rw [show rademacher = dyadicCellHuge by
          simp only [rademacher, certifiedRademacherCellValue, htLo,
            if_false]]
        exact hTel.trans hTelHuge
      exact le_min hTel (le_min hTrivial hRademacher)
  have hsum := add_le_add hF1 hCorrection
  simpa only [certifiedSharedLowCellValue, state, telescoping, trivial,
    rademacher, correction, DyadicInterval.add, DyadicInterval.upper,
    Int.cast_add, add_div, differenceR, rhoR, rR, uR, normalNR] using hsum

theorem lawNormalizedLowIntegrand_le_partition_cell_upper
    {n N i : ℕ} (hn : 1 ≤ n) (hN : 0 < N) (hi : i < N)
    {rho z : DyadicInterval}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (hcell : CertifiedLowCellAdmissible n rho z
      (dyadicRouteBLowCell N i))
    {x : ℝ}
    (hx : x ∈ Set.Icc (routeBEqualPartitionPoint 0 prawitzSplit N i)
      (routeBEqualPartitionPoint 0 prawitzSplit N (i + 1))) :
    lawNormalizedLowIntegrand n mu x ≤
      (certifiedSharedLowCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z
        (dyadicRouteBLowCell N i)).upper := by
  let c := dyadicRouteBLowCell N i
  have hbase : DyadicLowCellAdmissible n rho z c := hcell.base
  have huBoxLo : 0 ≤
      (DyadicInterval.div c.v (dyadicCellW rho z)).lo :=
    hcell.frequencyNonnegative
  have hHuge : ¬ 0 < c.t.lo →
      (certifiedTelescopingCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z c).hi ≤
        dyadicCellHuge.hi := hcell.hugeFallback
  have ht := dyadicRouteBLowCell_t_contains hN hi hx
  have htRaw :
      (dyadicPrawitzCellAt (DyadicInterval.point 0)
        dyadicRouteBSplit N true i).t.Contains x := by
    simpa only [c, dyadicRouteBLowCell] using ht
  have hpLeft := routeBEqualPartitionPoint_mem_Icc
    (a := (0 : ℝ)) (b := prawitzSplit)
    (by norm_num [prawitzSplit]) hN (Nat.le_of_lt hi)
  have hpRight := routeBEqualPartitionPoint_mem_Icc
    (a := (0 : ℝ)) (b := prawitzSplit)
    (by norm_num [prawitzSplit]) hN (Nat.succ_le_iff.mpr hi)
  have hx0 : 0 ≤ x := hpLeft.1.trans hx.1
  have hx1 : x < 1 :=
    lt_of_le_of_lt (hx.2.trans hpRight.2) (by norm_num [prawitzSplit])
  have hvRaw := dyadicPrawitzCellAt_v_contains htRaw
  have hv : c.v.Contains (routeBCellV x) := by
    simpa only [c, dyadicRouteBLowCell] using hvRaw
  have hCot : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1)
        (DyadicInterval.sqr
          (dyadicPrawitzCellAt (DyadicInterval.point 0)
            dyadicRouteBSplit N true i).t))).lo := by
    simpa only [c, dyadicRouteBLowCell] using hbase.cotDenom
  have hk0Raw := dyadicPrawitzLowCell_k0_sound htRaw hCot
  have hkd2Raw := dyadicPrawitzLowCell_kd2_sound htRaw hCot
  have hk0 : c.k0.Contains (prawitzK0Envelope x) := by
    simpa only [c, dyadicRouteBLowCell] using hk0Raw
  have hkd2 : c.kd2.Contains (prawitzKD2Envelope x) := by
    simpa only [c, dyadicRouteBLowCell] using hkd2Raw
  have hhqRaw := dyadicPrawitzCellAt_hq_lower_le htRaw hx0 hx1.le
  have hhq : c.hq.lower ≤ routeBCellV x ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV x) := by
    simpa only [c, dyadicRouteBLowCell] using hhqRaw
  have hy3 := hbase.real_y_le_three hrho hz hv
  have hbound := certified_low_integrand_le_cell_upper
    (n := n) (rho := rho) (z := z) (c := c) hn
    mu hX hmean hsecond hrho hz hbox ht hx0 hx1 hv hhq hk0 hkd2
    hbase.w2Den hbase.bDen hbase.cDen hbase.w3Den hy3 huBoxLo hHuge
  simpa only [lawNormalizedLowIntegrand,
    lawNormalizedDifferenceIntegrand,
    lawNormalizedCorrectionIntegrand, c] using hbound

theorem lawNormalizedHighIntegrand_le_partition_cell_upper
    {n N i : ℕ} (hN : 0 < N) (hi : i < N)
    {rho z : DyadicInterval}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (hcell : CertifiedHighCellAdmissible n rho z
      (dyadicRouteBHighCell N i))
    {x : ℝ}
    (hx : x ∈ Set.Icc (routeBEqualPartitionPoint prawitzSplit 1 N i)
      (routeBEqualPartitionPoint prawitzSplit 1 N (i + 1))) :
    lawNormalizedHighIntegrand n mu x ≤
      (certifiedSharedHighCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z
        (dyadicRouteBHighCell N i)).upper := by
  let c := dyadicRouteBHighCell N i
  have hbase : DyadicHighCellAdmissible n rho z c := hcell.base
  have huBoxLo : 0 ≤
      (DyadicInterval.div c.v (dyadicCellW rho z)).lo :=
    hcell.frequencyNonnegative
  have ht := dyadicRouteBHighCell_t_contains hN hi hx
  have htRaw :
      (dyadicPrawitzCellAt dyadicRouteBSplit
        (DyadicInterval.point 1) N false i).t.Contains x := by
    simpa only [c, dyadicRouteBHighCell] using ht
  have hpLeft := routeBEqualPartitionPoint_mem_Icc
    (a := prawitzSplit) (b := (1 : ℝ))
    (by norm_num [prawitzSplit]) hN (Nat.le_of_lt hi)
  have hpRight := routeBEqualPartitionPoint_mem_Icc
    (a := prawitzSplit) (b := (1 : ℝ))
    (by norm_num [prawitzSplit]) hN (Nat.succ_le_iff.mpr hi)
  have hx0 : 0 < x :=
    (by norm_num [prawitzSplit] : (0 : ℝ) < prawitzSplit).trans_le
      (hpLeft.1.trans hx.1)
  have hx1 : x ≤ 1 := hx.2.trans hpRight.2
  have hvRaw := dyadicPrawitzCellAt_v_contains htRaw
  have hv : c.v.Contains (routeBCellV x) := by
    simpa only [c, dyadicRouteBHighCell] using hvRaw
  have hCot : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1)
        (DyadicInterval.sqr (DyadicInterval.sub (DyadicInterval.point 1)
          (dyadicPrawitzCellAt dyadicRouteBSplit
            (DyadicInterval.point 1) N false i).t)))).lo := by
    simpa only [c, dyadicRouteBHighCell] using hbase.cotDenom
  have hkh2Raw := dyadicPrawitzHighCell_kh2_sound htRaw hCot
  have hkh2 : c.kh2.Contains (prawitzKH2Envelope x) := by
    simpa only [c, dyadicRouteBHighCell] using hkh2Raw
  have hhqRaw := dyadicPrawitzCellAt_hq_lower_le htRaw hx0.le hx1
  have hhq : c.hq.lower ≤ routeBCellV x ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV x) := by
    simpa only [c, dyadicRouteBHighCell] using hhqRaw
  have hbound := certified_high_integrand_le_cell_upper
    (n := n) (rho := rho) (z := z) (c := c)
    mu hX hmean hsecond hrho hz hbox hx0 hx1 hv hhq hkh2
    hbase.w2Den huBoxLo
  simpa only [lawNormalizedHighIntegrand, c] using hbound

set_option maxRecDepth 100000 in
theorem lawNormalizedLowIntegral_le_certifiedLowSum_upper
    {n N : ℕ} (hn : 1 ≤ n) (hN : 0 < N)
    {rho z : DyadicInterval}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (hadmissible : ∀ i < N,
      CertifiedLowCellAdmissible n rho z
        (dyadicRouteBLowCell N i)) :
    (∫ t in (0 : ℝ)..prawitzSplit,
      lawNormalizedLowIntegrand n mu t) ≤
      (certifiedLowSum n rho z N).upper := by
  let p := routeBEqualPartitionPoint (0 : ℝ) prawitzSplit N
  have hint := intervalIntegrable_lawNormalizedLowIntegrand
    mu hX hmean hsecond hn
  have hbound := intervalIntegral_le_intervalNatSum_upper
    (f := lawNormalizedLowIntegrand n mu) (p := p) (N := N)
    (fun i hi => routeBEqualPartitionPoint_mono
      (by norm_num [prawitzSplit]) hN (Nat.le_succ i))
    (fun i hi => intervalIntegrable_equalPartitionCell hint
      (by norm_num [prawitzSplit]) hN hi)
    (fun i => certifiedSharedLowCellValue
      (dyadicRouteBBuildBoxState n rho z) n rho z
        (dyadicRouteBLowCell N i))
    (fun i => (dyadicRouteBLowCell N i).wid)
    (fun i hi => (hadmissible i hi).valueOrdered)
    (fun i hi x hx =>
      lawNormalizedLowIntegrand_le_partition_cell_upper
        hn hN hi mu hX hmean hsecond hrho hz hbox
          (hadmissible i hi) hx)
    (fun i hi => dyadicRouteBLowCell_wid_contains hN hi)
  rw [certifiedLowSum_eq_intervalNatSum]
  simpa only [p, routeBEqualPartitionPoint_zero,
    routeBEqualPartitionPoint_at_N hN] using hbound

/- Split into a follow-on module so the certified evaluator base remains a
small kernel-checking unit.
set_option maxRecDepth 100000 in
theorem lawNormalizedHighIntegral_le_certifiedHighSum_upper
    {n N : ℕ} (hN : 0 < N)
    {rho z : DyadicInterval}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (hadmissible : ∀ i < N,
      CertifiedHighCellAdmissible n rho z
        (dyadicRouteBHighCell N i)) :
    (∫ t in prawitzSplit..(1 : ℝ),
      lawNormalizedHighIntegrand n mu t) ≤
      (certifiedHighSum n rho z N).upper := by
  let p := routeBEqualPartitionPoint prawitzSplit (1 : ℝ) N
  have hint := intervalIntegrable_lawNormalizedHighIntegrand
    mu hX hmean hsecond n
  rw [certifiedHighSum_eq_intervalNatSum]
  calc
    (∫ t in prawitzSplit..(1 : ℝ),
        lawNormalizedHighIntegrand n mu t) =
        ∫ t in p 0..p N,
          lawNormalizedHighIntegrand n mu t := by
      simp only [p, routeBEqualPartitionPoint_zero,
        routeBEqualPartitionPoint_at_N hN]
    _ ≤ (intervalNatSum (fun i =>
          DyadicInterval.mul (dyadicRouteBHighCell N i).wid
            (certifiedSharedHighCellValue
              (dyadicRouteBBuildBoxState n rho z) n rho z
                (dyadicRouteBHighCell N i))) N).upper := by
      exact intervalIntegral_le_intervalNatSum_upper
        (f := lawNormalizedHighIntegrand n mu) (p := p) (N := N)
        (fun i hi => routeBEqualPartitionPoint_mono
          (by norm_num [prawitzSplit]) hN (Nat.le_succ i))
        (fun i hi => intervalIntegrable_equalPartitionCell hint
          (by norm_num [prawitzSplit]) hN hi)
        (fun i => certifiedSharedHighCellValue
          (dyadicRouteBBuildBoxState n rho z) n rho z
            (dyadicRouteBHighCell N i))
        (fun i => (dyadicRouteBHighCell N i).wid)
        (fun i hi => (hadmissible i hi).valueOrdered)
        (fun i hi x hx =>
          lawNormalizedHighIntegrand_le_partition_cell_upper
            hN hi mu hX hmean hsecond hrho hz hbox
              (hadmissible i hi) hx)
        (fun i hi => dyadicRouteBHighCell_wid_contains hN hi)

set_option maxRecDepth 100000 in
theorem lawNormalizedFiniteIntegrals_le_certifiedFiniteBound_upper
    {n N : ℕ} (hn : 1 ≤ n) (hN : 0 < N)
    {rho z : DyadicInterval}
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (hrho : rho.Contains (thirdAbsoluteMoment mu))
    (hz : z.Contains
      (thirdAbsoluteMoment mu * (symmetrizationRatio mu - 1)))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (hlow : ∀ i < N,
      CertifiedLowCellAdmissible n rho z
        (dyadicRouteBLowCell N i))
    (hhigh : ∀ i < N,
      CertifiedHighCellAdmissible n rho z
        (dyadicRouteBHighCell N i)) :
    (∫ t in (0 : ℝ)..prawitzSplit,
        lawNormalizedLowIntegrand n mu t) +
      (∫ t in prawitzSplit..(1 : ℝ),
        lawNormalizedHighIntegrand n mu t) ≤
      (certifiedFiniteBound n rho z N).upper := by
  have hlo := lawNormalizedLowIntegral_le_certifiedLowSum_upper
    hn hN mu hX hmean hsecond hrho hz hbox hlow
  have hhi := lawNormalizedHighIntegral_le_certifiedHighSum_upper
    hN mu hX hmean hsecond hrho hz hbox hhigh
  have hsum := add_le_add hlo hhi
  simpa [certifiedFiniteBound, DyadicInterval.add,
    DyadicInterval.upper, Int.cast_add, add_div] using hsum
-/

end

end BerryEsseen
