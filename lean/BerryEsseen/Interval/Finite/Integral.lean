import BerryEsseen.Interval.Finite.Evaluator

namespace BerryEsseen

open Finset MeasureTheory intervalIntegral DyadicInterval

noncomputable section

set_option maxRecDepth 100000

theorem lawNormalizedHighCellIntegral_le
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
      (dyadicRouteBHighCell N i)) :
    let p := routeBEqualPartitionPoint prawitzSplit (1 : ℝ) N
    (∫ t in p i..p (i + 1),
      lawNormalizedHighIntegrand n mu t) ≤
      (p (i + 1) - p i) *
        (certifiedSharedHighCellValue
          (dyadicRouteBBuildBoxState n rho z) n rho z
            (dyadicRouteBHighCell N i)).upper := by
  let p := routeBEqualPartitionPoint prawitzSplit (1 : ℝ) N
  have hmono : p i ≤ p (i + 1) :=
    routeBEqualPartitionPoint_mono
      (by norm_num [prawitzSplit]) hN (Nat.le_succ i)
  have hint := intervalIntegrable_equalPartitionCell
    (intervalIntegrable_lawNormalizedHighIntegrand
      mu hX hmean hsecond n)
    (by norm_num [prawitzSplit]) hN hi
  calc
    (∫ t in p i..p (i + 1),
        lawNormalizedHighIntegrand n mu t) ≤
        ∫ _ in p i..p (i + 1),
          (certifiedSharedHighCellValue
            (dyadicRouteBBuildBoxState n rho z) n rho z
              (dyadicRouteBHighCell N i)).upper := by
      apply intervalIntegral.integral_mono_on hmono hint
        intervalIntegrable_const
      intro x hx
      exact lawNormalizedHighIntegrand_le_partition_cell_upper
        hN hi mu hX hmean hsecond hrho hz hbox hcell hx
    _ = (p (i + 1) - p i) *
        (certifiedSharedHighCellValue
          (dyadicRouteBBuildBoxState n rho z) n rho z
            (dyadicRouteBHighCell N i)).upper := by
      rw [intervalIntegral.integral_const]
      rfl

theorem certifiedHighCellProduct_contains
    {n N i : ℕ} (hN : 0 < N) (hi : i < N)
    {rho z : DyadicInterval}
    (hcell : CertifiedHighCellAdmissible n rho z
      (dyadicRouteBHighCell N i)) :
    let p := routeBEqualPartitionPoint prawitzSplit (1 : ℝ) N
    (DyadicInterval.mul (dyadicRouteBHighCell N i).wid
      (certifiedSharedHighCellValue
        (dyadicRouteBBuildBoxState n rho z) n rho z
          (dyadicRouteBHighCell N i))).Contains
      ((p (i + 1) - p i) *
        (certifiedSharedHighCellValue
          (dyadicRouteBBuildBoxState n rho z) n rho z
            (dyadicRouteBHighCell N i)).upper) := by
  exact (dyadicRouteBHighCell_wid_contains hN hi).mul
    (DyadicInterval.contains_upper hcell.valueOrdered)

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
  have hintCell : ∀ i < N, IntervalIntegrable
      (lawNormalizedHighIntegrand n mu) volume
        (p i) (p (i + 1)) := fun i hi =>
    intervalIntegrable_equalPartitionCell hint
      (by norm_num [prawitzSplit]) hN hi
  have hterm : ∀ i < N,
      (DyadicInterval.mul (dyadicRouteBHighCell N i).wid
        (certifiedSharedHighCellValue
          (dyadicRouteBBuildBoxState n rho z) n rho z
            (dyadicRouteBHighCell N i))).Contains
        ((p (i + 1) - p i) *
          (certifiedSharedHighCellValue
            (dyadicRouteBBuildBoxState n rho z) n rho z
              (dyadicRouteBHighCell N i)).upper) := by
    intro i hi
    simpa only [p] using certifiedHighCellProduct_contains
      hN hi (hadmissible i hi)
  have hsum := intervalNatSum_sound N hterm
  rw [certifiedHighSum_eq_intervalNatSum]
  calc
    (∫ t in prawitzSplit..(1 : ℝ),
        lawNormalizedHighIntegrand n mu t) =
        ∫ t in p 0..p N,
          lawNormalizedHighIntegrand n mu t := by
      simp only [p, routeBEqualPartitionPoint_zero,
        routeBEqualPartitionPoint_at_N hN]
    _ = ∑ i ∈ Finset.range N,
        ∫ t in p i..p (i + 1),
          lawNormalizedHighIntegrand n mu t := by
      symm
      exact intervalIntegral.sum_integral_adjacent_intervals hintCell
    _ ≤ ∑ i ∈ Finset.range N,
        (p (i + 1) - p i) *
          (certifiedSharedHighCellValue
            (dyadicRouteBBuildBoxState n rho z) n rho z
              (dyadicRouteBHighCell N i)).upper := by
      exact Finset.sum_le_sum fun i hi => by
        simpa only [p] using lawNormalizedHighCellIntegral_le
          hN (Finset.mem_range.mp hi) mu hX hmean hsecond hrho hz hbox
            (hadmissible i (Finset.mem_range.mp hi))
    _ ≤ (intervalNatSum (fun i =>
          DyadicInterval.mul (dyadicRouteBHighCell N i).wid
            (certifiedSharedHighCellValue
              (dyadicRouteBBuildBoxState n rho z) n rho z
                (dyadicRouteBHighCell N i))) N).upper := hsum.2

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

end

end BerryEsseen
