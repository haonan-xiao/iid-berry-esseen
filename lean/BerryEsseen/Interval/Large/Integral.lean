import BerryEsseen.Interval.Large.Cell
import BerryEsseen.Interval.Finite.Functional
import BerryEsseen.Interval.Prawitz.LargeNTail

/-!
# Interval / Large / Integral
-/

open MeasureTheory intervalIntegral

namespace BerryEsseen

open DyadicInterval
open ProbabilityTheory

def certifiedLargeDirectLowSum
    (L r : DyadicInterval) (N : ℕ) : DyadicInterval :=
  intervalNatSum (fun i =>
    DyadicInterval.mul (dyadicRouteBLowCell N i).wid
      (certifiedLargeDirectLowCellValue L r
        (dyadicRouteBLowCell N i))) N

def certifiedLargeDirectFiniteBound
    (L r : DyadicInterval) (N : ℕ) : DyadicInterval :=
  DyadicInterval.add (certifiedLargeDirectLowSum L r N)
    (dyadicRouteBLargeHighSum L r N)

def certifiedLargeDirectFullBound
    (L r : DyadicInterval) (N : ℕ) : DyadicInterval :=
  DyadicInterval.add (certifiedLargeDirectFiniteBound L r N)
    (dyadicRouteBLargeTailValue L r)

def CertifiedLargeDirectFullAdmissible
    (L r : DyadicInterval) (N : ℕ) : Prop :=
  CertifiedLargeBoxAdmissible L r ∧
    DyadicLargeTailAdmissible L r ∧
    (∀ i : Fin N,
      CertifiedLargeLowCellAdmissible L r
        (dyadicRouteBLowCell N i.1)) ∧
    (∀ i : Fin N,
      DyadicLargeHighCellAdmissible L r
        (dyadicRouteBHighCell N i.1))

instance (L r : DyadicInterval) (N : ℕ) :
    Decidable (CertifiedLargeDirectFullAdmissible L r N) := by
  unfold CertifiedLargeDirectFullAdmissible
  infer_instance

noncomputable section

theorem lawNormalizedLowIntegrand_le_directPartitionCell_upper
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N i : ℕ} (hn : 100 ≤ n)
    {L r : DyadicInterval} {x : ℝ}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (hbox : CertifiedLargeBoxAdmissible L r)
    (hcell : CertifiedLargeLowCellAdmissible L r
      (dyadicRouteBLowCell N i))
    (hN : 0 < N) (hi : i < N)
    (hx : x ∈ Set.Icc (routeBEqualPartitionPoint 0 prawitzSplit N i)
      (routeBEqualPartitionPoint 0 prawitzSplit N (i + 1))) :
    lawNormalizedLowIntegrand n mu x ≤
      (certifiedLargeDirectLowCellValue L r
        (dyadicRouteBLowCell N i)).upper := by
  have ht := dyadicRouteBLowCell_t_contains hN hi hx
  have htRaw :
      (dyadicPrawitzCellAt (DyadicInterval.point 0)
        dyadicRouteBSplit N true i).t.Contains x := by
    simpa [dyadicRouteBLowCell] using ht
  have hpLeft := routeBEqualPartitionPoint_mem_Icc
    (a := (0 : ℝ)) (b := prawitzSplit)
    (by norm_num [prawitzSplit]) hN (Nat.le_of_lt hi)
  have hpRight := routeBEqualPartitionPoint_mem_Icc
    (a := (0 : ℝ)) (b := prawitzSplit)
    (by norm_num [prawitzSplit]) hN (Nat.succ_le_iff.mpr hi)
  have hx0 : 0 ≤ x := hpLeft.1.trans hx.1
  have hxSplit : x ≤ prawitzSplit := hx.2.trans hpRight.2
  have hvRaw := dyadicPrawitzCellAt_v_contains htRaw
  have hv : (dyadicRouteBLowCell N i).v.Contains (routeBCellV x) := by
    simpa [dyadicRouteBLowCell] using hvRaw
  have hCot : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1)
        (DyadicInterval.sqr
          (dyadicPrawitzCellAt (DyadicInterval.point 0)
            dyadicRouteBSplit N true i).t))).lo := by
    simpa [dyadicRouteBLowCell] using hcell.base.cotDenom
  have hk0Raw := dyadicPrawitzLowCell_k0_sound htRaw hCot
  have hkd2Raw := dyadicPrawitzLowCell_kd2_sound htRaw hCot
  have hk0 : (dyadicRouteBLowCell N i).k0.Contains
      (prawitzK0Envelope x) := by
    simpa [dyadicRouteBLowCell] using hk0Raw
  have hkd2 : (dyadicRouteBLowCell N i).kd2.Contains
      (prawitzKD2Envelope x) := by
    simpa [dyadicRouteBLowCell] using hkd2Raw
  have hhqRaw := dyadicPrawitzCellAt_hq_lower_le htRaw hx0
    (hxSplit.trans (by norm_num [prawitzSplit]))
  have hhq : (dyadicRouteBLowCell N i).hq.lower ≤
      routeBCellV x ^ 2 *
        routeBMinorant routeBKappa routeBTheta (routeBCellV x) := by
    simpa [dyadicRouteBLowCell] using hhqRaw
  exact lawNormalizedLowIntegrand_le_directCell_upper
    mu hX hmean hsecond hn hL hr ht hv hhq hk0 hkd2
      hbox hcell hx0 hxSplit

theorem lawNormalizedHighIntegrand_le_directPartitionCell_upper
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N i : ℕ} (hn : 100 ≤ n)
    {L r : DyadicInterval} {x : ℝ}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (hbox : CertifiedLargeBoxAdmissible L r)
    (hcell : DyadicLargeHighCellAdmissible L r
      (dyadicRouteBHighCell N i))
    (hN : 0 < N) (hi : i < N)
    (hx : x ∈ Set.Icc
      (routeBEqualPartitionPoint prawitzSplit 1 N i)
      (routeBEqualPartitionPoint prawitzSplit 1 N (i + 1))) :
    lawNormalizedHighIntegrand n mu x ≤
      (dyadicLargeHighCellValue L r
        (dyadicRouteBHighCell N i)).upper := by
  have ht := dyadicRouteBHighCell_t_contains hN hi hx
  have htRaw :
      (dyadicPrawitzCellAt dyadicRouteBSplit
        (DyadicInterval.point 1) N false i).t.Contains x := by
    simpa [dyadicRouteBHighCell] using ht
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
  have hCot : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1)
        (DyadicInterval.sqr (DyadicInterval.sub
          (DyadicInterval.point 1)
          (dyadicPrawitzCellAt dyadicRouteBSplit
            (DyadicInterval.point 1) N false i).t)))).lo := by
    simpa [dyadicRouteBHighCell] using hcell.cotDenom
  have hkh2Raw := dyadicPrawitzHighCell_kh2_sound htRaw hCot
  have hkh2 : (dyadicRouteBHighCell N i).kh2.Contains
      (prawitzKH2Envelope x) := by
    simpa [dyadicRouteBHighCell] using hkh2Raw
  have hhqRaw := dyadicPrawitzCellAt_hq_lower_le htRaw hx0.le hx1
  have hhq : (dyadicRouteBHighCell N i).hq.lower ≤
      routeBCellV x ^ 2 *
        routeBMinorant routeBKappa routeBTheta (routeBCellV x) := by
    simpa [dyadicRouteBHighCell] using hhqRaw
  exact lawNormalizedHighIntegrand_le_directCell_upper
    mu hX hmean hsecond hn hL hr hhq hkh2 hbox hcell hx0 hx1

theorem lawNormalizedLowIntegral_le_directSum_upper
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (hbox : CertifiedLargeBoxAdmissible L r)
    (hadmissible : ∀ i < N,
      CertifiedLargeLowCellAdmissible L r
        (dyadicRouteBLowCell N i)) :
    (∫ t in (0 : ℝ)..prawitzSplit,
      lawNormalizedLowIntegrand n mu t) ≤
      (certifiedLargeDirectLowSum L r N).upper := by
  let p := routeBEqualPartitionPoint (0 : ℝ) prawitzSplit N
  have hnOne : 1 ≤ n := by omega
  have hint := intervalIntegrable_lawNormalizedLowIntegrand
    mu hX hmean hsecond hnOne
  have hbound := intervalIntegral_le_intervalNatSum_upper
    (f := lawNormalizedLowIntegrand n mu) (p := p) (N := N)
    (fun i hi => routeBEqualPartitionPoint_mono
      (by norm_num [prawitzSplit]) hN (Nat.le_succ i))
    (fun i hi => intervalIntegrable_equalPartitionCell hint
      (by norm_num [prawitzSplit]) hN hi)
    (fun i => certifiedLargeDirectLowCellValue L r
      (dyadicRouteBLowCell N i))
    (fun i => (dyadicRouteBLowCell N i).wid)
    (fun i hi => (hadmissible i hi).valueOrdered)
    (fun i hi x hx =>
      lawNormalizedLowIntegrand_le_directPartitionCell_upper
        mu hX hmean hsecond hn hL hr hbox
          (hadmissible i hi) hN hi hx)
    (fun i hi => dyadicRouteBLowCell_wid_contains hN hi)
  simpa [p, certifiedLargeDirectLowSum,
    routeBEqualPartitionPoint_zero,
    routeBEqualPartitionPoint_at_N hN] using hbound

theorem lawNormalizedHighIntegral_le_directSum_upper
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (hbox : CertifiedLargeBoxAdmissible L r)
    (hadmissible : ∀ i < N,
      DyadicLargeHighCellAdmissible L r
        (dyadicRouteBHighCell N i)) :
    (∫ t in prawitzSplit..(1 : ℝ),
      lawNormalizedHighIntegrand n mu t) ≤
      (dyadicRouteBLargeHighSum L r N).upper := by
  let p := routeBEqualPartitionPoint prawitzSplit (1 : ℝ) N
  have hint := intervalIntegrable_lawNormalizedHighIntegrand
    mu hX hmean hsecond n
  have hbound := intervalIntegral_le_intervalNatSum_upper
    (f := lawNormalizedHighIntegrand n mu) (p := p) (N := N)
    (fun i hi => routeBEqualPartitionPoint_mono
      (by norm_num [prawitzSplit]) hN (Nat.le_succ i))
    (fun i hi => intervalIntegrable_equalPartitionCell hint
      (by norm_num [prawitzSplit]) hN hi)
    (fun i => dyadicLargeHighCellValue L r
      (dyadicRouteBHighCell N i))
    (fun i => (dyadicRouteBHighCell N i).wid)
    (fun i hi => (hadmissible i hi).valueOrdered)
    (fun i hi x hx =>
      lawNormalizedHighIntegrand_le_directPartitionCell_upper
        mu hX hmean hsecond hn hL hr hbox
          (hadmissible i hi) hN hi hx)
    (fun i hi => dyadicRouteBHighCell_wid_contains hN hi)
  simpa [p, dyadicRouteBLargeHighSum,
    routeBEqualPartitionPoint_zero,
    routeBEqualPartitionPoint_at_N hN] using hbound

theorem lawNormalizedFiniteIntegrals_le_directBound_upper
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (hbox : CertifiedLargeBoxAdmissible L r)
    (hlow : ∀ i < N,
      CertifiedLargeLowCellAdmissible L r
        (dyadicRouteBLowCell N i))
    (hhigh : ∀ i < N,
      DyadicLargeHighCellAdmissible L r
        (dyadicRouteBHighCell N i)) :
    (∫ t in (0 : ℝ)..prawitzSplit,
        lawNormalizedLowIntegrand n mu t) +
      (∫ t in prawitzSplit..(1 : ℝ),
        lawNormalizedHighIntegrand n mu t) ≤
      (certifiedLargeDirectFiniteBound L r N).upper := by
  have hlo := lawNormalizedLowIntegral_le_directSum_upper
    mu hX hmean hsecond hn hN hL hr hbox hlow
  have hhi := lawNormalizedHighIntegral_le_directSum_upper
    mu hX hmean hsecond hn hN hL hr hbox hhigh
  have hsum := add_le_add hlo hhi
  simpa [certifiedLargeDirectFiniteBound, DyadicInterval.add,
    DyadicInterval.upper, Int.cast_add, add_div] using hsum

theorem lawNormalizedPrawitzFunctional_le_largeDirectFullBound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (hbox : CertifiedLargeBoxAdmissible L r)
    (hlow : ∀ i < N,
      CertifiedLargeLowCellAdmissible L r
        (dyadicRouteBLowCell N i))
    (hhigh : ∀ i < N,
      DyadicLargeHighCellAdmissible L r
        (dyadicRouteBHighCell N i))
    (htail : DyadicLargeTailAdmissible L r) :
    lawNormalizedPrawitzFunctional n mu ≤
      (certifiedLargeDirectFullBound L r N).upper := by
  let rhoR := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let zR := rhoR * (rR - 1)
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrho : 1 ≤ rhoR := by
    dsimp only [rhoR]
    exact thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < rhoR := zero_lt_one.trans_le hrho
  have hrOne : 1 ≤ rR := by
    dsimp only [rR]
    exact symmetrizationRatio_lower mu hX hmean hsecond
  have hz0 : 0 ≤ zR := by
    dsimp only [zR]
    exact mul_nonneg (zero_le_one.trans hrho) (sub_nonneg.mpr hrOne)
  have hrouteR : routeBDboundR rhoR zR = rR := by
    simpa only [zR] using routeBDboundR_mul_excess hrhoPos.ne'
  have hfinite := lawNormalizedFiniteIntegrals_le_directBound_upper
    mu hX hmean hsecond hn hN hL hr hbox hlow hhigh
  have htailEq :
      Real.sqrt (n : ℝ) / rhoR *
          ((1 / Real.pi) * ∫ t in Set.Ici prawitzSplit,
            routeBPowerGaussianEnvelope n rhoR
              (routeBDboundR rhoR zR) t / t) =
        routeBLargeTailValue (routeBSmoothingScale n rhoR) rR := by
    rw [routeB_normalizedGaussianTail_eq hnPos hrhoPos hz0,
      routeBNormalizedE1Tail_eq_largeTailValue hnPos hrhoPos,
      hrouteR]
  have htailBound :
      Real.sqrt (n : ℝ) / rhoR *
          ((1 / Real.pi) * ∫ t in Set.Ici prawitzSplit,
            routeBPowerGaussianEnvelope n rhoR
              (routeBDboundR rhoR zR) t / t) ≤
        (dyadicRouteBLargeTailValue L r).upper := by
    rw [htailEq]
    exact routeBLargeTailValue_le_dyadic_upper
      hL hr hbox.toDyadicLargeBoxAdmissible htail
  have hsum := add_le_add hfinite htailBound
  unfold lawNormalizedPrawitzFunctional
  dsimp only [rhoR, rR, zR]
  simpa [certifiedLargeDirectFullBound, DyadicInterval.add,
    DyadicInterval.upper, Int.cast_add, add_div, add_assoc] using hsum

theorem lawNormalizedPrawitzFunctional_le_largeDirectFullBound_of_admissible
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (hfull : CertifiedLargeDirectFullAdmissible L r N) :
    lawNormalizedPrawitzFunctional n mu ≤
      (certifiedLargeDirectFullBound L r N).upper := by
  rcases hfull with ⟨hbox, htail, hlow, hhigh⟩
  exact lawNormalizedPrawitzFunctional_le_largeDirectFullBound
    mu hX hmean hsecond hn hN hL hr hbox
      (fun i hi => hlow ⟨i, hi⟩)
      (fun i hi => hhigh ⟨i, hi⟩) htail

theorem normalizedKolmogorovDistance_le_certifiedLargeDirectFullBound
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n
        (thirdAbsoluteMoment (P.map (X 0)))))
    (hr : r.Contains (symmetrizationRatio (P.map (X 0))))
    (hfull : CertifiedLargeDirectFullAdmissible L r N) :
    let rhoR := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rhoR *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw ≤
      (certifiedLargeDirectFullBound L r N).upper := by
  let mu := P.map (X 0)
  let rhoR := thirdAbsoluteMoment mu
  let rR := symmetrizationRatio mu
  let T := routeBSmoothingT n rhoR rR
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  letI : IsProbabilityMeasure (standardizedSumLaw P X n) :=
    isProbabilityMeasure_standardizedSumLaw P X
      (fun k => (hident k).aemeasurable_fst) n
  have hnOne : 1 ≤ n := by omega
  have hnPos : 0 < n := by omega
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
    P X hindep hident hX hmean hsecond hnOne
  have hcert :=
    lawNormalizedPrawitzFunctional_le_largeDirectFullBound_of_admissible
      (mu := mu) hX hmean hsecond hn hN hL hr hfull
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
    _ ≤ (certifiedLargeDirectFullBound L r N).upper := hcert

end

end BerryEsseen
