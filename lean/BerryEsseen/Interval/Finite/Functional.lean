import BerryEsseen.Interval.Finite.Integral
import BerryEsseen.Interval.Prawitz.GaussianTail

namespace BerryEsseen

open MeasureTheory ProbabilityTheory intervalIntegral DyadicInterval

noncomputable section

theorem lawNormalizedDifferenceIntegrand_eq_standardizedSum
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    let mu := P.map (X 0)
    let rho := thirdAbsoluteMoment mu
    let r := symmetrizationRatio mu
    let T := routeBSmoothingT n rho r
    lawNormalizedDifferenceIntegrand n mu t =
      2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖ *
        ‖charFun (standardizedSumLaw P X n) (T * t) -
          Complex.exp (-(T * t : ℂ) ^ 2 / 2)‖ := by
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
  unfold lawNormalizedDifferenceIntegrand
  dsimp only [mu, rho, r, T]
  rw [charFun_standardizedSumLaw P X hindep hident n (T * t), harg,
    ← complex_gaussian_pow_eq_smoothing_gaussian hnPos hrho hr,
    ← huEq, ← scalarNormalN_complex_eq,
    scalarNormalN_eq_real_exp]

theorem lawNormalizedHighIntegrand_eq_standardizedSum
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    let mu := P.map (X 0)
    let rho := thirdAbsoluteMoment mu
    let r := symmetrizationRatio mu
    let T := routeBSmoothingT n rho r
    lawNormalizedHighIntegrand n mu t =
      2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖ *
        ‖charFun (standardizedSumLaw P X n) (T * t)‖ := by
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
  unfold lawNormalizedHighIntegrand
  dsimp only [mu, rho, r, T]
  rw [charFun_standardizedSumLaw P X hindep hident n (T * t),
    harg, huEq]

theorem lawNormalizedCorrectionIntegrand_eq_smoothingGaussian
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    let rho := thirdAbsoluteMoment mu
    let r := symmetrizationRatio mu
    let T := routeBSmoothingT n rho r
    lawNormalizedCorrectionIntegrand n mu t =
      2 * Real.sqrt (n : ℝ) / rho *
        ‖prawitzKernelCorrection t‖ *
          Real.exp (-(T ^ 2 * t ^ 2) / 2) := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let T := routeBSmoothingT n rho r
  have hnPos : 0 < n := by omega
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith [thirdAbsoluteMoment_ge_one mu hX hsecond]
  have hr : 0 < r := by
    dsimp only [r]
    linarith [symmetrizationRatio_lower mu hX hmean hsecond]
  have hexponent := routeBGaussian_exponent_scale
    (n := n) (rho := rho) (r := r) (t := t) hnPos hrho hr
  unfold lawNormalizedCorrectionIntegrand
  dsimp only [rho, r, T]
  rw [show -((n : ℝ) *
        (routeBUFrequency rho r t ^ 2 / 2)) =
      -(T ^ 2 * t ^ 2) / 2 by
    calc
      -((n : ℝ) * (routeBUFrequency rho r t ^ 2 / 2)) =
          (n : ℝ) * (-(routeBUFrequency rho r t) ^ 2 / 2) := by ring
      _ = -(T ^ 2 * t ^ 2) / 2 := hexponent]

def lawNormalizedPrawitzFunctional
    (n : ℕ) (mu : Measure ℝ) : ℝ :=
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  (∫ t in (0 : ℝ)..prawitzSplit,
      lawNormalizedLowIntegrand n mu t) +
    (∫ t in prawitzSplit..(1 : ℝ),
      lawNormalizedHighIntegrand n mu t) +
    Real.sqrt (n : ℝ) / rho *
      ((1 / Real.pi) * ∫ t in Set.Ici prawitzSplit,
        routeBPowerGaussianEnvelope n rho (routeBDboundR rho z) t / t)

theorem normalizedPrawitzFunctional_eq_law
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    let mu := P.map (X 0)
    let rho := thirdAbsoluteMoment mu
    let r := symmetrizationRatio mu
    let T := routeBSmoothingT n rho r
    Real.sqrt (n : ℝ) / rho *
        prawitzFunctional (standardizedSumLaw P X n) T prawitzSplit =
      lawNormalizedPrawitzFunctional n mu := by
  let mu := P.map (X 0)
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  let T := routeBSmoothingT n rho r
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
  have hdiffEq :
      (∫ t in (0 : ℝ)..prawitzSplit,
        lawNormalizedDifferenceIntegrand n mu t) =
      (2 * Real.sqrt (n : ℝ) / rho) *
        ∫ t in (0 : ℝ)..prawitzSplit,
          ‖prawitzKernel t‖ *
            ‖charFun (standardizedSumLaw P X n) (T * t) -
              Complex.exp (-(T * t : ℂ) ^ 2 / 2)‖ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    simpa only [mu, rho, r, T, mul_assoc] using
      lawNormalizedDifferenceIntegrand_eq_standardizedSum
        P X hindep hident hX hmean hsecond hn t
  have hcorrectionEq :
      (∫ t in (0 : ℝ)..prawitzSplit,
        lawNormalizedCorrectionIntegrand n mu t) =
      (2 * Real.sqrt (n : ℝ) / rho) *
        ∫ t in (0 : ℝ)..prawitzSplit,
          ‖prawitzKernelCorrection t‖ *
            Real.exp (-(T ^ 2 * t ^ 2) / 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    simpa only [rho, r, T, mul_assoc] using
      lawNormalizedCorrectionIntegrand_eq_smoothingGaussian
        mu hX hmean hsecond hn t
  have hhighEq :
      (∫ t in prawitzSplit..(1 : ℝ),
        lawNormalizedHighIntegrand n mu t) =
      (2 * Real.sqrt (n : ℝ) / rho) *
        ∫ t in prawitzSplit..(1 : ℝ),
          ‖prawitzKernel t‖ *
            ‖charFun (standardizedSumLaw P X n) (T * t)‖ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    simpa only [mu, rho, r, T, mul_assoc] using
      lawNormalizedHighIntegrand_eq_standardizedSum
        P X hindep hident hX hmean hsecond hn t
  have hlowEq :
      (∫ t in (0 : ℝ)..prawitzSplit,
        lawNormalizedLowIntegrand n mu t) =
      (2 * Real.sqrt (n : ℝ) / rho) *
          (∫ t in (0 : ℝ)..prawitzSplit,
            ‖prawitzKernel t‖ *
              ‖charFun (standardizedSumLaw P X n) (T * t) -
                Complex.exp (-(T * t : ℂ) ^ 2 / 2)‖) +
        (2 * Real.sqrt (n : ℝ) / rho) *
          (∫ t in (0 : ℝ)..prawitzSplit,
            ‖prawitzKernelCorrection t‖ *
              Real.exp (-(T ^ 2 * t ^ 2) / 2)) := by
    unfold lawNormalizedLowIntegrand
    rw [intervalIntegral.integral_add
      (intervalIntegrable_lawNormalizedDifferenceIntegrand
        mu hX hmean hsecond hn)
      (intervalIntegrable_lawNormalizedCorrectionIntegrand
        mu hX hmean hsecond hn), hdiffEq, hcorrectionEq]
  have htailEq :
      (∫ t in Set.Ici prawitzSplit,
        routeBPowerGaussianEnvelope n rho (routeBDboundR rho z) t / t) =
      ∫ t in Set.Ici prawitzSplit,
        Real.exp (-(T ^ 2 * t ^ 2) / 2) / t := by
    apply setIntegral_congr_fun measurableSet_Ici
    intro t ht
    change routeBPowerGaussianEnvelope n rho (routeBDboundR rho z) t / t =
      Real.exp (-(T ^ 2 * t ^ 2) / 2) / t
    rw [hrouteR,
      routeBPowerGaussianEnvelope_eq_smoothing_gaussian hnPos hrho hr]
  change Real.sqrt (n : ℝ) / rho *
      prawitzFunctional (standardizedSumLaw P X n) T prawitzSplit =
    lawNormalizedPrawitzFunctional n mu
  unfold prawitzFunctional lawNormalizedPrawitzFunctional
  dsimp only [rho, r, z, T]
  rw [hlowEq, hhighEq, htailEq]
  ring

theorem lawNormalizedPrawitzFunctional_le_certifiedFullBound
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
        (dyadicRouteBHighCell N i))
    (htail : DyadicRouteBTailAdmissible n rho z) :
    lawNormalizedPrawitzFunctional n mu ≤
      (certifiedFullBound n rho z N).upper := by
  have hfinite :=
    lawNormalizedFiniteIntegrals_le_certifiedFiniteBound_upper
      hn hN mu hX hmean hsecond hrho hz hbox hlow hhigh
  have htailBound :=
    routeB_normalizedGaussianTail_le_dyadicRouteBTailValue_upper
      (lt_of_lt_of_le Nat.zero_lt_one hn) hrho hz hbox htail
  have hsum := add_le_add hfinite htailBound
  unfold lawNormalizedPrawitzFunctional
  dsimp only
  simpa [certifiedFullBound, DyadicInterval.add,
    DyadicInterval.upper, Int.cast_add, add_div, add_assoc] using hsum

theorem normalizedKolmogorovDistance_le_certifiedFullBound
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n N : ℕ} (hn : 1 ≤ n) (hN : 0 < N)
    {rho z : DyadicInterval}
    (hrho : rho.Contains (thirdAbsoluteMoment (P.map (X 0))))
    (hz : z.Contains
      (thirdAbsoluteMoment (P.map (X 0)) *
        (symmetrizationRatio (P.map (X 0)) - 1)))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (hlow : ∀ i < N,
      CertifiedLowCellAdmissible n rho z
        (dyadicRouteBLowCell N i))
    (hhigh : ∀ i < N,
      CertifiedHighCellAdmissible n rho z
        (dyadicRouteBHighCell N i))
    (htail : DyadicRouteBTailAdmissible n rho z) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw ≤
      (certifiedFullBound n rho z N).upper := by
  let mu := P.map (X 0)
  let rhoR := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let T := routeBSmoothingT n rhoR rR
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  letI : IsProbabilityMeasure (standardizedSumLaw P X n) :=
    isProbabilityMeasure_standardizedSumLaw P X
      (fun k => (hident k).aemeasurable_fst) n
  have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hrhoR : 0 < rhoR := by
    dsimp only [rhoR, mu]
    linarith [thirdAbsoluteMoment_ge_one (P.map (X 0)) hX hsecond]
  have hrR : 0 < rR := by
    dsimp only [rR, mu]
    linarith [symmetrizationRatio_lower
      (P.map (X 0)) hX hmean hsecond]
  have hT : 0 < T := by
    dsimp only [T]
    exact routeBSmoothingT_pos hnPos hrhoR hrR
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
  have hnormalized := normalizedPrawitzFunctional_eq_law
    P X hindep hident hX hmean hsecond hn
  have hcert :=
    lawNormalizedPrawitzFunctional_le_certifiedFullBound
      hn hN mu hX hmean hsecond hrho hz hbox hlow hhigh htail
  have hscale : 0 ≤ Real.sqrt (n : ℝ) / rhoR := by positivity
  dsimp only [rhoR, mu, T, rR] at hnormalized hsmooth hcert ⊢
  calc
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw ≤
      Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        prawitzFunctional (standardizedSumLaw P X n)
          (routeBSmoothingT n (thirdAbsoluteMoment (P.map (X 0)))
            (symmetrizationRatio (P.map (X 0)))) prawitzSplit :=
      mul_le_mul_of_nonneg_left hsmooth hscale
    _ = lawNormalizedPrawitzFunctional n (P.map (X 0)) := hnormalized
    _ ≤ (certifiedFullBound n rho z N).upper := hcert

end

end BerryEsseen
