import BerryEsseen.Certificate.LargeN.Cell
import BerryEsseen.Certificate.Finite.Integral
/-!
# Direct large-`n` Darboux sums

This module connects the verifier-matching `tail_direct` cells to the canonical
equal-width Prawitz partition.  It composes the analytic large-`n` reduction
with each cell bound and therefore controls the original finite-`n`
integrands directly; no integrability assertion for the auxiliary envelope is
needed.
-/

open MeasureTheory intervalIntegral

namespace BerryEsseen

open DyadicInterval

def dyadicRouteBLargeLowSum
    (L r : DyadicInterval) (N : ℕ) : DyadicInterval :=
  intervalNatSum (fun i => DyadicInterval.mul (dyadicRouteBLowCell N i).wid
    (dyadicLargeLowCellValue L r (dyadicRouteBLowCell N i))) N

def dyadicRouteBLargeHighSum
    (L r : DyadicInterval) (N : ℕ) : DyadicInterval :=
  intervalNatSum (fun i => DyadicInterval.mul (dyadicRouteBHighCell N i).wid
    (dyadicLargeHighCellValue L r (dyadicRouteBHighCell N i))) N

def dyadicRouteBLargeFiniteBound
    (L r : DyadicInterval) (N : ℕ) : DyadicInterval :=
  DyadicInterval.add (dyadicRouteBLargeLowSum L r N)
    (dyadicRouteBLargeHighSum L r N)

noncomputable section

theorem routeBNormalizedLowIntegrand_le_dyadicRouteBLargeLowCell_upper
    {n N i : ℕ} (hn : 100 ≤ n)
    {rho z : ℝ} {L r : DyadicInterval} {x : ℝ}
    (hrho1 : 1 ≤ rho) (hz0 : 0 ≤ z)
    (hL : L.Contains (routeBSmoothingScale n rho))
    (hr : r.Contains (routeBDboundR rho z))
    (hbox : DyadicLargeBoxAdmissible L r)
    (hcell : DyadicLargeLowCellAdmissible L r (dyadicRouteBLowCell N i))
    (hN : 0 < N) (hi : i < N)
    (hx : x ∈ Set.Icc (routeBEqualPartitionPoint 0 prawitzSplit N i)
      (routeBEqualPartitionPoint 0 prawitzSplit N (i + 1))) :
    routeBNormalizedLowIntegrand n rho z x ≤
      (dyadicLargeLowCellValue L r (dyadicRouteBLowCell N i)).upper := by
  have ht := dyadicRouteBLowCell_t_contains hN hi hx
  have htRaw :
      (dyadicPrawitzCellAt (DyadicInterval.point 0) dyadicRouteBSplit N true i).t.Contains x := by
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
    simpa [dyadicRouteBLowCell] using hcell.cotDenom
  have hk0Raw := dyadicPrawitzLowCell_k0_sound htRaw hCot
  have hkd2Raw := dyadicPrawitzLowCell_kd2_sound htRaw hCot
  have hk0 : (dyadicRouteBLowCell N i).k0.Contains (prawitzK0Envelope x) := by
    simpa [dyadicRouteBLowCell] using hk0Raw
  have hkd2 : (dyadicRouteBLowCell N i).kd2.Contains (prawitzKD2Envelope x) := by
    simpa [dyadicRouteBLowCell] using hkd2Raw
  have hhqRaw := dyadicPrawitzCellAt_hq_lower_le htRaw hx0
    (hxSplit.trans (by norm_num [prawitzSplit]))
  have hhq : (dyadicRouteBLowCell N i).hq.lower ≤ routeBCellV x ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV x) := by
    simpa [dyadicRouteBLowCell] using hhqRaw
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  have hr1 := hbox.real_one_le_r hr
  have hdiff := routeBNormalizedLowerDifference_le_largeIntegrand
    hn hrho1 hr1 hx0
  have hcorr := routeBNormalizedCorrection_le_largeIntegrand
    (t := x) hn hrho1 hr1
  have hlarge := routeBLargeLowIntegrand_le_dyadicLargeLowCellValue_upper
    hL hr ht hv hhq hk0 hkd2 hbox hcell hx0 hxSplit
  unfold routeBNormalizedLowIntegrand
  exact (add_le_add hdiff hcorr).trans hlarge

theorem routeBNormalizedHighIntegrand_le_dyadicRouteBLargeHighCell_upper
    {n N i : ℕ} (hn : 100 ≤ n)
    {rho z : ℝ} {L r : DyadicInterval} {x : ℝ}
    (hrho1 : 1 ≤ rho) (hz0 : 0 ≤ z)
    (hL : L.Contains (routeBSmoothingScale n rho))
    (hr : r.Contains (routeBDboundR rho z))
    (hbox : DyadicLargeBoxAdmissible L r)
    (hcell : DyadicLargeHighCellAdmissible L r (dyadicRouteBHighCell N i))
    (hN : 0 < N) (hi : i < N)
    (hx : x ∈ Set.Icc (routeBEqualPartitionPoint prawitzSplit 1 N i)
      (routeBEqualPartitionPoint prawitzSplit 1 N (i + 1))) :
    routeBNormalizedHighIntegrand n rho z x ≤
      (dyadicLargeHighCellValue L r (dyadicRouteBHighCell N i)).upper := by
  have ht := dyadicRouteBHighCell_t_contains hN hi hx
  have htRaw :
      (dyadicPrawitzCellAt dyadicRouteBSplit (DyadicInterval.point 1) N false i).t.Contains x := by
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
        (DyadicInterval.sqr (DyadicInterval.sub (DyadicInterval.point 1)
          (dyadicPrawitzCellAt dyadicRouteBSplit
            (DyadicInterval.point 1) N false i).t)))).lo := by
    simpa [dyadicRouteBHighCell] using hcell.cotDenom
  have hkh2Raw := dyadicPrawitzHighCell_kh2_sound htRaw hCot
  have hkh2 : (dyadicRouteBHighCell N i).kh2.Contains (prawitzKH2Envelope x) := by
    simpa [dyadicRouteBHighCell] using hkh2Raw
  have hhqRaw := dyadicPrawitzCellAt_hq_lower_le htRaw hx0.le hx1
  have hhq : (dyadicRouteBHighCell N i).hq.lower ≤ routeBCellV x ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV x) := by
    simpa [dyadicRouteBHighCell] using hhqRaw
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  have hr1 := hbox.real_one_le_r hr
  have hfinite := routeBNormalizedHigh_le_largeIntegrand hn hrho1 hr1 hx0.le
  have hlarge := routeBLargeHighIntegrand_le_dyadicLargeHighCellValue_upper
    hL hr hhq hkh2 hbox hcell hx0 hx1
  exact hfinite.trans hlarge

theorem routeBNormalizedLowIntegral_le_dyadicRouteBLargeLowSum_upper
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {rho z : ℝ} {L r : DyadicInterval}
    (hrho1 : 1 ≤ rho) (hz0 : 0 ≤ z)
    (hL : L.Contains (routeBSmoothingScale n rho))
    (hr : r.Contains (routeBDboundR rho z))
    (hbox : DyadicLargeBoxAdmissible L r)
    (hadmissible : ∀ i < N,
      DyadicLargeLowCellAdmissible L r (dyadicRouteBLowCell N i)) :
    (∫ t in (0 : ℝ)..prawitzSplit,
      routeBNormalizedLowIntegrand n rho z t) ≤
      (dyadicRouteBLargeLowSum L r N).upper := by
  let p := routeBEqualPartitionPoint (0 : ℝ) prawitzSplit N
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hint := intervalIntegrable_routeBNormalizedLowIntegrand hnPos hrhoPos hz0
  have hbound := intervalIntegral_le_intervalNatSum_upper
    (f := routeBNormalizedLowIntegrand n rho z) (p := p) (N := N)
    (fun i hi => routeBEqualPartitionPoint_mono
      (by norm_num [prawitzSplit]) hN (Nat.le_succ i))
    (fun i hi => intervalIntegrable_equalPartitionCell hint
      (by norm_num [prawitzSplit]) hN hi)
    (fun i => dyadicLargeLowCellValue L r (dyadicRouteBLowCell N i))
    (fun i => (dyadicRouteBLowCell N i).wid)
    (fun i hi => (hadmissible i hi).valueOrdered)
    (fun i hi x hx =>
      routeBNormalizedLowIntegrand_le_dyadicRouteBLargeLowCell_upper
        hn hrho1 hz0 hL hr hbox (hadmissible i hi) hN hi hx)
    (fun i hi => dyadicRouteBLowCell_wid_contains hN hi)
  simpa [p, dyadicRouteBLargeLowSum, routeBEqualPartitionPoint_zero,
    routeBEqualPartitionPoint_at_N hN] using hbound

theorem routeBNormalizedHighIntegral_le_dyadicRouteBLargeHighSum_upper
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {rho z : ℝ} {L r : DyadicInterval}
    (hrho1 : 1 ≤ rho) (hz0 : 0 ≤ z)
    (hL : L.Contains (routeBSmoothingScale n rho))
    (hr : r.Contains (routeBDboundR rho z))
    (hbox : DyadicLargeBoxAdmissible L r)
    (hadmissible : ∀ i < N,
      DyadicLargeHighCellAdmissible L r (dyadicRouteBHighCell N i)) :
    (∫ t in prawitzSplit..(1 : ℝ),
      routeBNormalizedHighIntegrand n rho z t) ≤
      (dyadicRouteBLargeHighSum L r N).upper := by
  let p := routeBEqualPartitionPoint prawitzSplit (1 : ℝ) N
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  have hint := intervalIntegrable_routeBNormalizedHighIntegrand n hrhoPos hz0
  have hbound := intervalIntegral_le_intervalNatSum_upper
    (f := routeBNormalizedHighIntegrand n rho z) (p := p) (N := N)
    (fun i hi => routeBEqualPartitionPoint_mono
      (by norm_num [prawitzSplit]) hN (Nat.le_succ i))
    (fun i hi => intervalIntegrable_equalPartitionCell hint
      (by norm_num [prawitzSplit]) hN hi)
    (fun i => dyadicLargeHighCellValue L r (dyadicRouteBHighCell N i))
    (fun i => (dyadicRouteBHighCell N i).wid)
    (fun i hi => (hadmissible i hi).valueOrdered)
    (fun i hi x hx =>
      routeBNormalizedHighIntegrand_le_dyadicRouteBLargeHighCell_upper
        hn hrho1 hz0 hL hr hbox (hadmissible i hi) hN hi hx)
    (fun i hi => dyadicRouteBHighCell_wid_contains hN hi)
  simpa [p, dyadicRouteBLargeHighSum, routeBEqualPartitionPoint_zero,
    routeBEqualPartitionPoint_at_N hN] using hbound

theorem routeBNormalizedFiniteIntegrals_le_dyadicRouteBLargeFiniteBound_upper
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {rho z : ℝ} {L r : DyadicInterval}
    (hrho1 : 1 ≤ rho) (hz0 : 0 ≤ z)
    (hL : L.Contains (routeBSmoothingScale n rho))
    (hr : r.Contains (routeBDboundR rho z))
    (hbox : DyadicLargeBoxAdmissible L r)
    (hlow : ∀ i < N,
      DyadicLargeLowCellAdmissible L r (dyadicRouteBLowCell N i))
    (hhigh : ∀ i < N,
      DyadicLargeHighCellAdmissible L r (dyadicRouteBHighCell N i)) :
    (∫ t in (0 : ℝ)..prawitzSplit,
        routeBNormalizedLowIntegrand n rho z t) +
      (∫ t in prawitzSplit..(1 : ℝ),
        routeBNormalizedHighIntegrand n rho z t) ≤
      (dyadicRouteBLargeFiniteBound L r N).upper := by
  have hlo := routeBNormalizedLowIntegral_le_dyadicRouteBLargeLowSum_upper
    hn hN hrho1 hz0 hL hr hbox hlow
  have hhi := routeBNormalizedHighIntegral_le_dyadicRouteBLargeHighSum_upper
    hn hN hrho1 hz0 hL hr hbox hhigh
  have hsum := add_le_add hlo hhi
  simpa [dyadicRouteBLargeFiniteBound, DyadicInterval.add, DyadicInterval.upper,
    Int.cast_add, add_div] using hsum

end

end BerryEsseen
