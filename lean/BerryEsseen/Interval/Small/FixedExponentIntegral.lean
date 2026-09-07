import BerryEsseen.Interval.Small.FixedExponentCell
import BerryEsseen.Interval.Finite.Functional
import BerryEsseen.Analysis.TailBounds
import BerryEsseen.Interval.Prawitz.LargeNSmallTail

/-!
# Interval / Small / Fixed Exponent Integral
-/

namespace BerryEsseen

open DyadicInterval
open MeasureTheory ProbabilityTheory intervalIntegral

noncomputable section

def certifiedLargeSmallFiniteSum
    (L r : DyadicInterval) (N : ℕ) : DyadicInterval :=
  intervalNatSum (fun i =>
    DyadicInterval.mul (dyadicRouteBLargeSmallYWidth N i)
      (certifiedLargeSmallCellValue L r
        (dyadicRouteBLargeSmallYCell N i))) N

def certifiedLargeSmallBound
    (L r : DyadicInterval) (N : ℕ) : DyadicInterval :=
  DyadicInterval.add (certifiedLargeSmallFiniteSum L r N)
    dyadicRouteBLargeSmallOmission

theorem lawNormalizedDifferenceIntegrand_le_routeB
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let r := symmetrizationRatio mu
    let z := rho * (r - 1)
    lawNormalizedDifferenceIntegrand n mu t ≤
      routeBNormalizedLowerDifferenceIntegrand n rho z t := by
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
  have hrPos : 0 < r := zero_lt_one.trans_le hr
  have hrouteR : routeBDboundR rho z = r := by
    simpa only [z] using routeBDboundR_mul_excess hrhoPos.ne'
  have henvelope := lawNormalizedDifferenceIntegrand_le_envelope
    mu hX hmean hsecond hn ht0
  have hscalar := scalarPowerDifference_le_routeB n
    (rho := rho) (z := z) (t := t) hrhoPos
      (by rw [hrouteR]; exact hrPos) ht0
  have hscale : 0 ≤
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hscalar hscale
  exact henvelope.trans <| by
    simpa only [routeBNormalizedLowerDifferenceIntegrand,
      rho, r, z, mul_assoc] using hscaled

theorem lawNormalizedHighIntegrand_le_routeB
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let r := symmetrizationRatio mu
    let z := rho * (r - 1)
    lawNormalizedHighIntegrand n mu t ≤
      routeBNormalizedHighIntegrand n rho z t := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  have hrho : 1 ≤ rho := by
    dsimp only [rho]
    exact thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have henvelope := lawNormalizedHighIntegrand_le_envelope
    mu hX hmean hsecond n ht0
  have hscalar := scalarPowerModulus_le_routeB n rho z t
  have hscale : 0 ≤
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hscalar hscale
  exact henvelope.trans <| by
    simpa only [routeBNormalizedHighIntegrand,
      rho, r, z, mul_assoc] using hscaled

theorem lawNormalizedLowIntegrand_le_routeB
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) :
    let rho := thirdAbsoluteMoment mu
    let r := symmetrizationRatio mu
    let z := rho * (r - 1)
    lawNormalizedLowIntegrand n mu t ≤
      routeBNormalizedLowIntegrand n rho z t := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  have hdiff := lawNormalizedDifferenceIntegrand_le_routeB
    mu hX hmean hsecond hn ht0
  have hcorr := congrFun
    (lawNormalizedCorrectionIntegrand_eq_routeB mu hX hsecond n) t
  unfold lawNormalizedLowIntegrand routeBNormalizedLowIntegrand
  simpa only [rho, r, z] using add_le_add hdiff hcorr.le

theorem lawNormalizedPrawitzFunctional_le_routeB
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    let rho := thirdAbsoluteMoment mu
    let r := symmetrizationRatio mu
    let z := rho * (r - 1)
    lawNormalizedPrawitzFunctional n mu ≤
      Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho z) := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  let z := rho * (r - 1)
  let low := lawNormalizedLowIntegrand n mu
  let high := lawNormalizedHighIntegrand n mu
  let routeBLow := routeBNormalizedLowIntegrand n rho z
  let routeBHigh := routeBNormalizedHighIntegrand n rho z
  have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hrho : 1 ≤ rho := by
    dsimp only [rho]
    exact thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hr : 1 ≤ r := by
    dsimp only [r]
    exact symmetrizationRatio_lower mu hX hmean hsecond
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    exact mul_nonneg (zero_le_one.trans hrho) (sub_nonneg.mpr hr)
  have hLowPath : IntervalIntegrable low volume 0 prawitzSplit := by
    dsimp only [low]
    exact intervalIntegrable_lawNormalizedLowIntegrand
      mu hX hmean hsecond hn
  have hLowRouteB : IntervalIntegrable routeBLow volume 0 prawitzSplit := by
    dsimp only [routeBLow]
    exact intervalIntegrable_routeBNormalizedLowIntegrand
      hnPos hrhoPos hz0
  have hLowIntegral :
      (∫ t in (0 : ℝ)..prawitzSplit, low t) ≤
        ∫ t in (0 : ℝ)..prawitzSplit, routeBLow t := by
    apply intervalIntegral.integral_mono_on
      (by norm_num [prawitzSplit]) hLowPath hLowRouteB
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    simpa only [low, routeBLow, rho, r, z] using
      lawNormalizedLowIntegrand_le_routeB
        mu hX hmean hsecond hn ht0
  have hHighPath : IntervalIntegrable high volume prawitzSplit 1 := by
    dsimp only [high]
    exact intervalIntegrable_lawNormalizedHighIntegrand
      mu hX hmean hsecond n
  have hHighRouteB : IntervalIntegrable routeBHigh volume prawitzSplit 1 := by
    dsimp only [routeBHigh]
    exact intervalIntegrable_routeBNormalizedHighIntegrand n hrhoPos hz0
  have hHighIntegral :
      (∫ t in prawitzSplit..(1 : ℝ), high t) ≤
        ∫ t in prawitzSplit..(1 : ℝ), routeBHigh t := by
    apply intervalIntegral.integral_mono_on
      (by norm_num [prawitzSplit]) hHighPath hHighRouteB
    intro t ht
    have ht0 : 0 ≤ t :=
      (by norm_num [prawitzSplit] : (0 : ℝ) ≤ prawitzSplit).trans ht.1
    simpa only [high, routeBHigh, rho, r, z] using
      lawNormalizedHighIntegrand_le_routeB
        mu hX hmean hsecond n ht0
  change lawNormalizedPrawitzFunctional n mu ≤
    Real.sqrt (n : ℝ) / rho *
      routeBU routeBKappa routeBTheta n rho (routeBDboundR rho z)
  rw [routeB_normalizedRouteBU_eq_finiteIntegrals_add_tail
    hnPos hrhoPos hz0]
  unfold lawNormalizedPrawitzFunctional
  dsimp only [rho, r, z]
  exact add_le_add (add_le_add hLowIntegral hHighIntegral) le_rfl

theorem normalizedKolmogorovDistance_le_lawNormalizedPrawitzFunctional
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw ≤
      lawNormalizedPrawitzFunctional n (P.map (X 0)) := by
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
  have hscale : 0 ≤ Real.sqrt (n : ℝ) / rhoR := by positivity
  dsimp only [rhoR, mu, T, rR] at hnormalized hsmooth ⊢
  calc
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw ≤
      Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        prawitzFunctional (standardizedSumLaw P X n)
          (routeBSmoothingT n (thirdAbsoluteMoment (P.map (X 0)))
            (symmetrizationRatio (P.map (X 0)))) prawitzSplit :=
      mul_le_mul_of_nonneg_left hsmooth hscale
    _ = lawNormalizedPrawitzFunctional n (P.map (X 0)) := hnormalized

theorem intervalIntegral_lawNormalizedLargeSmallIntegrand_le_finiteSum
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (hbox : CertifiedLargeSmallBoxAdmissible L r)
    (hadmissible : ∀ i < N, CertifiedLargeSmallCellAdmissible L r
      (dyadicRouteBLargeSmallYCell N i))
    (hint : IntervalIntegrable
      (lawNormalizedLargeSmallIntegrand n mu) volume 0 4) :
    (∫ y in (0 : ℝ)..4,
        lawNormalizedLargeSmallIntegrand n mu y) ≤
      (certifiedLargeSmallFiniteSum L r N).upper := by
  let p := routeBEqualPartitionPoint (0 : ℝ) 4 N
  have hbound := intervalIntegral_le_intervalNatSum_upper
    (f := lawNormalizedLargeSmallIntegrand n mu) (p := p) (N := N)
    (fun i hi => routeBEqualPartitionPoint_mono
      (by norm_num) hN (Nat.le_succ i))
    (fun i hi => intervalIntegrable_equalPartitionCell hint
      (by norm_num) hN hi)
    (fun i => certifiedLargeSmallCellValue L r
      (dyadicRouteBLargeSmallYCell N i))
    (fun i => dyadicRouteBLargeSmallYWidth N i)
    (fun i hi => (hadmissible i hi).valueOrdered)
    (fun i hi y hy => by
      have hpLeft := routeBEqualPartitionPoint_mem_Icc
        (a := (0 : ℝ)) (b := (4 : ℝ)) (by norm_num) hN (Nat.le_of_lt hi)
      have hpRight := routeBEqualPartitionPoint_mem_Icc
        (a := (0 : ℝ)) (b := (4 : ℝ)) (by norm_num) hN
          (Nat.succ_le_iff.mpr hi)
      have hy0 : 0 ≤ y := hpLeft.1.trans hy.1
      have hy4 : y ≤ 4 := hy.2.trans hpRight.2
      have hyCell := dyadicRouteBLargeSmallYCell_contains hN hi hy
      exact lawNormalizedLargeSmallIntegrand_le_cell_upper
        mu hX hmean hsecond hn hL hr hyCell hbox
          (hadmissible i hi) hy0 hy4)
    (fun i hi => dyadicRouteBLargeSmallYWidth_contains hN hi)
  simpa [p, certifiedLargeSmallFiniteSum,
    routeBEqualPartitionPoint_zero,
    routeBEqualPartitionPoint_at_N hN] using hbound

theorem lawNormalizedEndpointIntegrals_le_smallFiniteSum_upper
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (hbox : CertifiedLargeSmallBoxAdmissible L r)
    (hadmissible : ∀ i < N, CertifiedLargeSmallCellAdmissible L r
      (dyadicRouteBLargeSmallYCell N i)) :
    (∫ t in (0 : ℝ)..4 * routeBSmoothingScale n (thirdAbsoluteMoment mu),
        lawNormalizedLowIntegrand n mu t) +
      (∫ t in 1 - 4 * routeBSmoothingScale n (thirdAbsoluteMoment mu)..(1 : ℝ),
        lawNormalizedHighIntegrand n mu t) ≤
      (certifiedLargeSmallFiniteSum L r N).upper := by
  let LR := routeBSmoothingScale n (thirdAbsoluteMoment mu)
  let low := lawNormalizedLowIntegrand n mu
  let high := lawNormalizedHighIntegrand n mu
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrho : 1 ≤ thirdAbsoluteMoment mu :=
    thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < thirdAbsoluteMoment mu := zero_lt_one.trans_le hrho
  have hLR : 0 < LR := by
    dsimp only [LR]
    exact routeBSmoothingScale_pos hnPos hrhoPos
  have hLu : LR ≤ 1 / 16 :=
    hbox.toDyadicLargeSmallBoxAdmissible.real_L_le_sixteenth hL
  have hfour : 4 * LR ≤ 1 / 4 := by nlinarith
  have hfourSplit : 4 * LR ≤ prawitzSplit := by
    norm_num [prawitzSplit] at hfour ⊢
    linarith
  have hLowBase : IntervalIntegrable low volume 0 prawitzSplit := by
    dsimp only [low]
    exact intervalIntegrable_lawNormalizedLowIntegrand
      mu hX hmean hsecond (by omega)
  have hLowRestricted : IntervalIntegrable low volume 0 (LR * 4) := by
    apply IntervalIntegrable.mono hLowBase
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc ?_) le_rfl
    exact Set.mem_uIcc_of_le (by positivity)
      (by simpa [mul_comm] using hfourSplit)
  have hLowComp : IntervalIntegrable
      (fun y => LR * low (LR * y)) volume 0 4 := by
    have hcomp := hLowRestricted.comp_mul_left (c := LR)
    have hscaled := hcomp.const_mul LR
    simpa [hLR.ne'] using hscaled
  have hhighLeft : prawitzSplit ≤ 1 - LR * 4 := by
    norm_num [prawitzSplit] at hfour ⊢
    nlinarith
  have hHighBase : IntervalIntegrable high volume prawitzSplit 1 := by
    dsimp only [high]
    exact intervalIntegrable_lawNormalizedHighIntegrand
      mu hX hmean hsecond n
  have hHighRestricted : IntervalIntegrable high volume (1 - LR * 4) 1 := by
    apply IntervalIntegrable.mono hHighBase
      (Set.uIcc_subset_uIcc ?_ Set.right_mem_uIcc) le_rfl
    exact Set.mem_uIcc_of_le hhighLeft (by nlinarith [hLR.le])
  have hHighComp : IntervalIntegrable
      (fun y => LR * high (1 - LR * y)) volume 0 4 := by
    have hsub := (hHighRestricted.comp_sub_left 1).symm
    have hcomp := hsub.comp_mul_left (c := LR)
    have hscaled := hcomp.const_mul LR
    simpa [hLR.ne'] using hscaled
  have hf : IntervalIntegrable
      (lawNormalizedLargeSmallIntegrand n mu) volume 0 4 := by
    simpa [lawNormalizedLargeSmallIntegrand, LR, low, high] using
      hLowComp.add hHighComp
  have hbound :=
    intervalIntegral_lawNormalizedLargeSmallIntegrand_le_finiteSum
      mu hX hmean hsecond hn hN hL hr hbox hadmissible hf
  have hLowChange :
      (∫ y in (0 : ℝ)..4, LR * low (LR * y)) =
        ∫ t in (0 : ℝ)..LR * 4, low t := by
    rw [intervalIntegral.integral_const_mul]
    simpa [smul_eq_mul] using
      (intervalIntegral.smul_integral_comp_mul_left
        (f := low) (a := (0 : ℝ)) (b := (4 : ℝ)) LR)
  have hHighChange :
      (∫ y in (0 : ℝ)..4, LR * high (1 - LR * y)) =
        ∫ t in 1 - LR * 4..(1 : ℝ), high t := by
    rw [intervalIntegral.integral_const_mul]
    simpa [smul_eq_mul] using
      (intervalIntegral.smul_integral_comp_sub_mul
        (f := high) (a := (0 : ℝ)) (b := (4 : ℝ)) LR 1)
  rw [show (∫ y in (0 : ℝ)..4,
      lawNormalizedLargeSmallIntegrand n mu y) =
      (∫ y in (0 : ℝ)..4, LR * low (LR * y)) +
        (∫ y in (0 : ℝ)..4, LR * high (1 - LR * y)) by
        rw [← intervalIntegral.integral_add hLowComp hHighComp]
        apply intervalIntegral.integral_congr
        intro y hy
        simp only [lawNormalizedLargeSmallIntegrand, LR, low, high],
    hLowChange, hHighChange] at hbound
  simpa only [LR, low, high, mul_comm] using hbound

theorem lawNormalizedPrawitzFunctional_le_smallBound_upper
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (hbox : CertifiedLargeSmallBoxAdmissible L r)
    (hadmissible : ∀ i < N, CertifiedLargeSmallCellAdmissible L r
      (dyadicRouteBLargeSmallYCell N i)) :
    lawNormalizedPrawitzFunctional n mu ≤
      (certifiedLargeSmallBound L r N).upper := by
  let rho := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let eta := rho * (rR - 1)
  let LR := routeBSmoothingScale n rho
  let low := lawNormalizedLowIntegrand n mu
  let high := lawNormalizedHighIntegrand n mu
  let routeBLow := routeBNormalizedLowIntegrand n rho eta
  let routeBHigh := routeBNormalizedHighIntegrand n rho eta
  let tail := Real.sqrt (n : ℝ) / rho *
    (routeBE1 (routeBTailArgument n rho eta) / (2 * Real.pi))
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrho1 : 1 ≤ rho := by
    dsimp only [rho]
    exact thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  have hrR1 : 1 ≤ rR := by
    dsimp only [rR]
    exact symmetrizationRatio_lower mu hX hmean hsecond
  have hrRUpper : rR ≤ 1 + 1 / rho := by
    dsimp only [rR, rho]
    exact symmetrizationRatio_upper mu hX hmean hsecond
  have heta0 : 0 ≤ eta := by
    dsimp only [eta]
    exact mul_nonneg (zero_le_one.trans hrho1) (sub_nonneg.mpr hrR1)
  have heta1 : eta ≤ 1 := by
    have hdiff : rR - 1 ≤ 1 / rho := by linarith
    have hmul := mul_le_mul_of_nonneg_left hdiff (zero_le_one.trans hrho1)
    have hcancel : rho * (1 / rho) = 1 := by field_simp
    dsimp only [eta]
    linarith
  have hLR : 0 < LR := routeBSmoothingScale_pos hnPos hrhoPos
  have hLRu : LR ≤ (1 : ℝ) / 16 := by
    dsimp only [LR, rho]
    exact hbox.toDyadicLargeSmallBoxAdmissible.real_L_le_sixteenth hL
  have hfourSplit : 4 * LR ≤ prawitzSplit := by
    have hquarter : 4 * LR ≤ (1 : ℝ) / 4 := by nlinarith
    norm_num [prawitzSplit] at hquarter ⊢
    linarith
  have hhighCut : (3 : ℝ) / 4 ≤ 1 - 4 * LR := by nlinarith

  have hLowBase : IntervalIntegrable low volume 0 prawitzSplit := by
    dsimp only [low]
    exact intervalIntegrable_lawNormalizedLowIntegrand
      mu hX hmean hsecond (by omega)
  have hLowFinite : IntervalIntegrable low volume 0 (4 * LR) := by
    apply IntervalIntegrable.mono hLowBase
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc ?_) le_rfl
    exact Set.mem_uIcc_of_le (by positivity) hfourSplit
  have hLowOmit : IntervalIntegrable low volume (4 * LR) prawitzSplit := by
    apply IntervalIntegrable.mono hLowBase
      (Set.uIcc_subset_uIcc ?_ Set.right_mem_uIcc) le_rfl
    exact Set.mem_uIcc_of_le (by positivity) hfourSplit
  have hLowSplit := intervalIntegral.integral_add_adjacent_intervals
    hLowFinite hLowOmit

  have hHighBase : IntervalIntegrable high volume prawitzSplit 1 := by
    dsimp only [high]
    exact intervalIntegrable_lawNormalizedHighIntegrand
      mu hX hmean hsecond n
  have hHighMiddle : IntervalIntegrable high volume
      prawitzSplit ((3 : ℝ) / 4) := by
    apply IntervalIntegrable.mono hHighBase
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc ?_) le_rfl
    exact Set.mem_uIcc_of_le (by norm_num [prawitzSplit]) (by norm_num)
  have hHighRest : IntervalIntegrable high volume ((3 : ℝ) / 4) 1 := by
    apply IntervalIntegrable.mono hHighBase
      (Set.uIcc_subset_uIcc ?_ Set.right_mem_uIcc) le_rfl
    exact Set.mem_uIcc_of_le (by norm_num [prawitzSplit]) (by norm_num)
  have hHighOmit : IntervalIntegrable high volume
      ((3 : ℝ) / 4) (1 - 4 * LR) := by
    apply IntervalIntegrable.mono hHighBase
      (Set.uIcc_subset_uIcc ?_ ?_) le_rfl
    · exact Set.mem_uIcc_of_le (by norm_num [prawitzSplit]) (by norm_num)
    · have hlower : prawitzSplit ≤ 1 - 4 * LR :=
        (by norm_num [prawitzSplit] : prawitzSplit ≤ (3 : ℝ) / 4).trans hhighCut
      have hupper : 1 - 4 * LR ≤ (1 : ℝ) := by
        have : 0 ≤ 4 * LR := by positivity
        linarith
      exact Set.mem_uIcc_of_le hlower hupper
  have hHighFinite : IntervalIntegrable high volume (1 - 4 * LR) 1 := by
    apply IntervalIntegrable.mono hHighBase
      (Set.uIcc_subset_uIcc ?_ Set.right_mem_uIcc) le_rfl
    have hlower : prawitzSplit ≤ 1 - 4 * LR :=
      (by norm_num [prawitzSplit] : prawitzSplit ≤ (3 : ℝ) / 4).trans hhighCut
    have hupper : 1 - 4 * LR ≤ (1 : ℝ) := by
      have : 0 ≤ 4 * LR := by positivity
      linarith
    exact Set.mem_uIcc_of_le hlower hupper
  have hHighSplit := intervalIntegral.integral_add_adjacent_intervals
    hHighMiddle hHighRest
  have hHighRestSplit := intervalIntegral.integral_add_adjacent_intervals
    hHighOmit hHighFinite

  have hRouteBLowBase : IntervalIntegrable routeBLow volume 0 prawitzSplit := by
    dsimp only [routeBLow]
    exact intervalIntegrable_routeBNormalizedLowIntegrand
      hnPos hrhoPos heta0
  have hRouteBLowOmit : IntervalIntegrable routeBLow volume
      (4 * LR) prawitzSplit := by
    apply IntervalIntegrable.mono hRouteBLowBase
      (Set.uIcc_subset_uIcc ?_ Set.right_mem_uIcc) le_rfl
    exact Set.mem_uIcc_of_le (by positivity) hfourSplit
  have hLowDom :
      (∫ t in 4 * LR..prawitzSplit, low t) ≤
        ∫ t in 4 * LR..prawitzSplit, routeBLow t := by
    apply intervalIntegral.integral_mono_on hfourSplit hLowOmit hRouteBLowOmit
    intro t ht
    have ht0 : 0 ≤ t := (by positivity : (0 : ℝ) ≤ 4 * LR).trans ht.1
    simpa only [low, routeBLow, rho, rR, eta] using
      lawNormalizedLowIntegrand_le_routeB
        mu hX hmean hsecond (by omega) ht0

  have hRouteBHighBase : IntervalIntegrable routeBHigh volume
      prawitzSplit 1 := by
    dsimp only [routeBHigh]
    exact intervalIntegrable_routeBNormalizedHighIntegrand n hrhoPos heta0
  have hRouteBHighMiddle : IntervalIntegrable routeBHigh volume
      prawitzSplit ((3 : ℝ) / 4) := by
    apply IntervalIntegrable.mono hRouteBHighBase
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc ?_) le_rfl
    exact Set.mem_uIcc_of_le (by norm_num [prawitzSplit]) (by norm_num)
  have hMiddleDom :
      (∫ t in prawitzSplit..(3 : ℝ) / 4, high t) ≤
        ∫ t in prawitzSplit..(3 : ℝ) / 4, routeBHigh t := by
    apply intervalIntegral.integral_mono_on
      (by norm_num [prawitzSplit]) hHighMiddle hRouteBHighMiddle
    intro t ht
    have ht0 : 0 ≤ t :=
      (by norm_num [prawitzSplit] : (0 : ℝ) ≤ prawitzSplit).trans ht.1
    simpa only [high, routeBHigh, rho, rR, eta] using
      lawNormalizedHighIntegrand_le_routeB
        mu hX hmean hsecond n ht0
  have hRouteBHighOmit : IntervalIntegrable routeBHigh volume
      ((3 : ℝ) / 4) (1 - 4 * LR) := by
    apply IntervalIntegrable.mono hRouteBHighBase
      (Set.uIcc_subset_uIcc ?_ ?_) le_rfl
    · exact Set.mem_uIcc_of_le (by norm_num [prawitzSplit]) (by norm_num)
    · have hlower : prawitzSplit ≤ 1 - 4 * LR :=
        (by norm_num [prawitzSplit] : prawitzSplit ≤ (3 : ℝ) / 4).trans hhighCut
      have hupper : 1 - 4 * LR ≤ (1 : ℝ) := by
        have : 0 ≤ 4 * LR := by positivity
        linarith
      exact Set.mem_uIcc_of_le hlower hupper
  have hEndpointDom :
      (∫ t in (3 : ℝ) / 4..1 - 4 * LR, high t) ≤
        ∫ t in (3 : ℝ) / 4..1 - 4 * LR, routeBHigh t := by
    apply intervalIntegral.integral_mono_on hhighCut hHighOmit hRouteBHighOmit
    intro t ht
    have ht0 : 0 ≤ t := (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 4).trans ht.1
    simpa only [high, routeBHigh, rho, rR, eta] using
      lawNormalizedHighIntegrand_le_routeB
        mu hX hmean hsecond n ht0

  have hfinite := lawNormalizedEndpointIntegrals_le_smallFiniteSum_upper
    mu hX hmean hsecond hn hN hL hr hbox hadmissible
  have hrouteLowOmission := refinedRouteBNormalizedLow_omission_le
    hn hrho1 heta0 heta1 (by simpa only [LR] using hLRu)
  have hrouteMiddleOmission := refinedRouteBNormalizedHigh_middle_omission_le
    hn hrho1 heta0 heta1 (by simpa only [LR] using hLRu)
  have hrouteEndpointOmission := refinedRouteBNormalizedHigh_endpoint_omission_le
    hn hrho1 heta0 heta1 (by simpa only [LR] using hLRu)
  have htailOmission := refinedRouteBNormalizedE1Tail_small_le
    hn hrho1 heta0 heta1 (by simpa only [LR] using hLRu)
  have homissionContains : dyadicRouteBLargeSmallOmission.Contains
      ((3 : ℝ) / 100000000000) := by
    simpa [dyadicRouteBLargeSmallOmission] using
      DyadicInterval.contains_ofRat 3 (b := 100000000000) (by norm_num)
  have homissionBudget : (16 : ℝ) / 1000000000000 ≤
      dyadicRouteBLargeSmallOmission.upper := by
    exact (by norm_num : (16 : ℝ) / 1000000000000 ≤
      3 / 100000000000).trans homissionContains.2
  have hfinite' :
      (∫ t in (0 : ℝ)..4 * LR, low t) +
          (∫ t in 1 - 4 * LR..(1 : ℝ), high t) ≤
        (certifiedLargeSmallFiniteSum L r N).upper := by
    simpa only [LR, rho, low, high] using hfinite
  have hlowOmission' :
      (∫ t in 4 * LR..prawitzSplit, low t) ≤
        (13 : ℝ) / 1000000000000 := by
    exact hLowDom.trans <| by
      simpa only [LR, routeBLow] using hrouteLowOmission
  have hmiddleOmission' :
      (∫ t in prawitzSplit..(3 : ℝ) / 4, high t) ≤
        (1 : ℝ) / 1000000000000 := by
    exact hMiddleDom.trans <| by
      simpa only [routeBHigh] using hrouteMiddleOmission
  have hendpointOmission' :
      (∫ t in (3 : ℝ) / 4..1 - 4 * LR, high t) ≤
        (1 : ℝ) / 1000000000000 := by
    exact hEndpointDom.trans <| by
      simpa only [LR, routeBHigh] using hrouteEndpointOmission
  have htailOmission' : tail ≤ (1 : ℝ) / 1000000000000 := by
    simpa only [tail] using htailOmission

  unfold lawNormalizedPrawitzFunctional
  dsimp only
  change ((∫ t in (0 : ℝ)..prawitzSplit, low t) +
      ∫ t in prawitzSplit..(1 : ℝ), high t) +
        Real.sqrt (n : ℝ) / rho *
          ((1 / Real.pi) * ∫ t in Set.Ici prawitzSplit,
            routeBPowerGaussianEnvelope n rho
              (routeBDboundR rho eta) t / t) ≤ _
  rw [routeB_normalizedGaussianTail_eq hnPos hrhoPos heta0]
  change ((∫ t in (0 : ℝ)..prawitzSplit, low t) +
      ∫ t in prawitzSplit..(1 : ℝ), high t) + tail ≤ _
  rw [← hLowSplit, ← hHighSplit, ← hHighRestSplit]
  have htotal :
      (((∫ t in (0 : ℝ)..4 * LR, low t) +
          ∫ t in 4 * LR..prawitzSplit, low t) +
        ((∫ t in prawitzSplit..(3 : ℝ) / 4, high t) +
          ((∫ t in (3 : ℝ) / 4..1 - 4 * LR, high t) +
            ∫ t in 1 - 4 * LR..(1 : ℝ), high t))) + tail ≤
        (certifiedLargeSmallFiniteSum L r N).upper +
          dyadicRouteBLargeSmallOmission.upper := by
    linarith
  have haddUpper : (certifiedLargeSmallBound L r N).upper =
      (certifiedLargeSmallFiniteSum L r N).upper +
        dyadicRouteBLargeSmallOmission.upper := by
    simp [certifiedLargeSmallBound, DyadicInterval.add,
      DyadicInterval.upper, Int.cast_add, add_div]
  rw [haddUpper]
  exact htotal

end

end BerryEsseen
