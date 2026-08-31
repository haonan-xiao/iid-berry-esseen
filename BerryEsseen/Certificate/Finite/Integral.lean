import BerryEsseen.Certificate.Dyadic.CellPartition
/-!
# Certified finite Route B integrals

The exact checker's real-parameter boxes and per-cell arithmetic side conditions are recorded
here as decidable integer propositions.  The main pointwise theorems turn those propositions
into upper bounds for the normalized low- and high-frequency Route B integrands.  The remaining
step is finite Darboux summation over all cells.
-/

open MeasureTheory intervalIntegral

namespace BerryEsseen

open DyadicInterval

structure DyadicRouteBBoxAdmissible
    (rho z : DyadicInterval) : Prop where
  rhoPos : 0 < rho.lo
  zNonnegative : 0 ≤ z.lo
  zLeRho : z.hi ≤ rho.lo

structure DyadicLowCellAdmissible
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : Prop where
  cotDenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
    (DyadicInterval.sub (DyadicInterval.point 1) (DyadicInterval.sqr c.t))).lo
  w2Den : 0 < (dyadicCellW2 rho z).lo
  bDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
    (dyadicCellW2 rho z)).lo
  bArgNonnegative : 0 ≤ (dyadicCellBArg rho z c).lo
  nArgNonnegative : 0 ≤ (dyadicCellNArg n rho z c).lo
  cDen : 0 < (DyadicInterval.mul (DyadicInterval.point 4)
    (dyadicCellW rho z)).lo
  w3Den : 0 < (powi (dyadicCellW rho z) 3).lo
  yLeThree : (dyadicDboundY rho z c.v).hi ≤ (DyadicInterval.point 3).lo
  hugeFallback : ¬ 0 < c.t.lo →
    (dyadicCellTelescoping n rho z c).hi ≤ dyadicCellHuge.hi
  valueOrdered : (dyadicLowCellValue n rho z c).Ordered

structure DyadicHighCellAdmissible
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : Prop where
  cotDenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
    (DyadicInterval.sub (DyadicInterval.point 1)
      (DyadicInterval.sqr (DyadicInterval.sub (DyadicInterval.point 1) c.t)))).lo
  w2Den : 0 < (dyadicCellW2 rho z).lo
  valueOrdered : (dyadicHighCellValue n rho z c).Ordered

instance (rho z : DyadicInterval) :
    Decidable (DyadicRouteBBoxAdmissible rho z) :=
  decidable_of_iff
    (0 < rho.lo ∧ 0 ≤ z.lo ∧ z.hi ≤ rho.lo) <| by
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, h3⟩
      · intro h
        exact ⟨h.rhoPos, h.zNonnegative, h.zLeRho⟩

instance (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) :
    Decidable (DyadicLowCellAdmissible n rho z c) :=
  decidable_of_iff
    (0 < (DyadicInterval.mul (DyadicInterval.point 4725)
        (DyadicInterval.sub (DyadicInterval.point 1) (DyadicInterval.sqr c.t))).lo ∧
      0 < (dyadicCellW2 rho z).lo ∧
      0 < (DyadicInterval.mul (DyadicInterval.point 2) (dyadicCellW2 rho z)).lo ∧
      0 ≤ (dyadicCellBArg rho z c).lo ∧
      0 ≤ (dyadicCellNArg n rho z c).lo ∧
      0 < (DyadicInterval.mul (DyadicInterval.point 4) (dyadicCellW rho z)).lo ∧
      0 < (powi (dyadicCellW rho z) 3).lo ∧
      (dyadicDboundY rho z c.v).hi ≤ (DyadicInterval.point 3).lo ∧
      (¬ 0 < c.t.lo →
        (dyadicCellTelescoping n rho z c).hi ≤ dyadicCellHuge.hi) ∧
      (dyadicLowCellValue n rho z c).lo ≤
        (dyadicLowCellValue n rho z c).hi) <| by
        constructor
        · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
          exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
        · intro h
          exact ⟨h.cotDenom, h.w2Den, h.bDen, h.bArgNonnegative,
            h.nArgNonnegative, h.cDen, h.w3Den, h.yLeThree,
            h.hugeFallback, h.valueOrdered⟩

instance (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) :
    Decidable (DyadicHighCellAdmissible n rho z c) :=
  decidable_of_iff
      (0 < (DyadicInterval.mul (DyadicInterval.point 4725)
        (DyadicInterval.sub (DyadicInterval.point 1)
          (DyadicInterval.sqr (DyadicInterval.sub (DyadicInterval.point 1) c.t)))).lo ∧
      0 < (dyadicCellW2 rho z).lo ∧
      (dyadicHighCellValue n rho z c).lo ≤
        (dyadicHighCellValue n rho z c).hi) <| by
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, h2, h3⟩
        · intro h
          exact ⟨h.cotDenom, h.w2Den, h.valueOrdered⟩

def dyadicRouteBLowSum
    (n : ℕ) (rho z : DyadicInterval) (N : ℕ) : DyadicInterval :=
  intervalNatSum (fun i => DyadicInterval.mul (dyadicRouteBLowCell N i).wid
    (dyadicLowCellValue n rho z (dyadicRouteBLowCell N i))) N

def dyadicRouteBHighSum
    (n : ℕ) (rho z : DyadicInterval) (N : ℕ) : DyadicInterval :=
  intervalNatSum (fun i => DyadicInterval.mul (dyadicRouteBHighCell N i).wid
    (dyadicHighCellValue n rho z (dyadicRouteBHighCell N i))) N

/-- The exact `finite_bound` accumulator, split into its low and high loops. -/
def dyadicRouteBFiniteBound
    (n : ℕ) (rho z : DyadicInterval) (N : ℕ) : DyadicInterval :=
  DyadicInterval.add (dyadicRouteBLowSum n rho z N)
    (dyadicRouteBHighSum n rho z N)

noncomputable section

theorem DyadicRouteBBoxAdmissible.real_rho_pos
    {rho z : DyadicInterval} (hbox : DyadicRouteBBoxAdmissible rho z)
    {rhoR : ℝ} (hrho : rho.Contains rhoR) :
    0 < rhoR := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  have hlower : 0 < rho.lower := by
    unfold DyadicInterval.lower
    exact div_pos (by exact_mod_cast hbox.rhoPos) hscale
  exact hlower.trans_le hrho.1

theorem DyadicRouteBBoxAdmissible.real_z_nonnegative
    {rho z : DyadicInterval} (hbox : DyadicRouteBBoxAdmissible rho z)
    {zR : ℝ} (hz : z.Contains zR) :
    0 ≤ zR := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  have hlower : 0 ≤ z.lower := by
    unfold DyadicInterval.lower
    exact div_nonneg (by exact_mod_cast hbox.zNonnegative) hscale.le
  exact hlower.trans hz.1

theorem DyadicRouteBBoxAdmissible.real_z_le_rho
    {rho z : DyadicInterval} (hbox : DyadicRouteBBoxAdmissible rho z)
    {rhoR zR : ℝ} (hrho : rho.Contains rhoR) (hz : z.Contains zR) :
    zR ≤ rhoR := by
  have hmiddle : z.upper ≤ rho.lower :=
    dyadic_upper_le_lower_of_hi_le_lo hbox.zLeRho
  exact hz.2.trans (hmiddle.trans hrho.1)

theorem DyadicLowCellAdmissible.real_y_le_three
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    (hcell : DyadicLowCellAdmissible n rho z c)
    {rhoR zR vR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (hv : c.v.Contains vR) :
    routeBDboundY rhoR zR vR ≤ 3 := by
  have hyDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (DyadicInterval.sqr (dyadicDboundW rho z))).lo := by
    simpa [dyadicCellW2, dyadicCellW, dyadicDboundW] using hcell.bDen
  have hy := dyadicDboundY_sound hrho hz hv hyDen
  have hupper : (dyadicDboundY rho z c.v).upper ≤
      (DyadicInterval.point 3).lower :=
    dyadic_upper_le_lower_of_hi_le_lo hcell.yLeThree
  have hthree : (DyadicInterval.point 3).lower = (3 : ℝ) := by
    simp [DyadicInterval.lower, DyadicInterval.point, dyadicScale_pos.ne']
  rw [hthree] at hupper
  exact hy.2.trans hupper

theorem routeBNormalizedLowIntegrand_le_dyadicLowCellValue_upper_of_admissible
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    {rhoR zR tR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (ht : c.t.Contains tR)
    (hv : c.v.Contains (routeBCellV tR))
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hk0 : c.k0.Contains (prawitzK0Envelope tR))
    (hkd2 : c.kd2.Contains (prawitzKD2Envelope tR))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (hcell : DyadicLowCellAdmissible n rho z c)
    (ht0 : 0 ≤ tR) (ht1 : tR < 1) :
    routeBNormalizedLowIntegrand n rhoR zR tR ≤
      (dyadicLowCellValue n rho z c).upper := by
  have hrhoR := hbox.real_rho_pos hrho
  have hz0 := hbox.real_z_nonnegative hz
  have hz1 := hbox.real_z_le_rho hrho hz
  have hy3 := hcell.real_y_le_three hrho hz hv
  have hF1 :=
    routeBNormalizedLowerDifferenceIntegrand_le_dyadicCellF1_upper
      hrho hz ht hv hbox.rhoPos hrhoR hz0 hz1 ht0 ht1 hhq hk0
      hcell.w2Den hcell.bDen hcell.bArgNonnegative hcell.nArgNonnegative
      hcell.cDen hcell.w3Den hy3 hcell.hugeFallback
  have hF3 :=
    routeBNormalizedCorrectionIntegrand_le_dyadicCellF3_upper
      hrho hz ht hv hbox.rhoPos hrhoR ht0 ht1 hkd2
      hcell.bDen hcell.nArgNonnegative
  exact routeBNormalizedLowIntegrand_le_dyadicLowCellValue_upper hF1 hF3

theorem routeBNormalizedHighIntegrand_le_dyadicHighCellValue_upper_of_admissible
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    {rhoR zR tR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (ht : c.t.Contains tR)
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hkh2 : c.kh2.Contains (prawitzKH2Envelope tR))
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (hcell : DyadicHighCellAdmissible n rho z c)
    (ht0 : 0 < tR) (ht1 : tR ≤ 1) :
    routeBNormalizedHighIntegrand n rhoR zR tR ≤
      (dyadicHighCellValue n rho z c).upper := by
  have hrhoR := hbox.real_rho_pos hrho
  have hz0 := hbox.real_z_nonnegative hz
  simpa [dyadicHighCellValue] using
    routeBNormalizedHighIntegrand_le_dyadicCellF2_upper
      hrho hz ht hbox.rhoPos hrhoR hz0 ht0 ht1 hhq hkh2 hcell.w2Den

theorem routeBNormalizedLowIntegrand_le_dyadicRouteBLowCell_upper
    {n N i : ℕ} {rho z : DyadicInterval} {rhoR zR x : ℝ}
    (hN : 0 < N) (hi : i < N)
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (hcell : DyadicLowCellAdmissible n rho z (dyadicRouteBLowCell N i))
    (hx : x ∈ Set.Icc (routeBEqualPartitionPoint 0 prawitzSplit N i)
      (routeBEqualPartitionPoint 0 prawitzSplit N (i + 1))) :
    routeBNormalizedLowIntegrand n rhoR zR x ≤
      (dyadicLowCellValue n rho z (dyadicRouteBLowCell N i)).upper := by
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
  have hx1 : x < 1 :=
    lt_of_le_of_lt (hx.2.trans hpRight.2) (by norm_num [prawitzSplit])
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
  have hhqRaw := dyadicPrawitzCellAt_hq_lower_le htRaw hx0 hx1.le
  have hhq : (dyadicRouteBLowCell N i).hq.lower ≤ routeBCellV x ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV x) := by
    simpa [dyadicRouteBLowCell] using hhqRaw
  exact routeBNormalizedLowIntegrand_le_dyadicLowCellValue_upper_of_admissible
    hrho hz ht hv hhq hk0 hkd2 hbox hcell hx0 hx1

theorem routeBNormalizedHighIntegrand_le_dyadicRouteBHighCell_upper
    {n N i : ℕ} {rho z : DyadicInterval} {rhoR zR x : ℝ}
    (hN : 0 < N) (hi : i < N)
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (hcell : DyadicHighCellAdmissible n rho z (dyadicRouteBHighCell N i))
    (hx : x ∈ Set.Icc (routeBEqualPartitionPoint prawitzSplit 1 N i)
      (routeBEqualPartitionPoint prawitzSplit 1 N (i + 1))) :
    routeBNormalizedHighIntegrand n rhoR zR x ≤
      (dyadicHighCellValue n rho z (dyadicRouteBHighCell N i)).upper := by
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
  exact routeBNormalizedHighIntegrand_le_dyadicHighCellValue_upper_of_admissible
    hrho hz ht hhq hkh2 hbox hcell hx0 hx1

theorem intervalIntegrable_equalPartitionCell
    {f : ℝ → ℝ} {a b : ℝ} {N i : ℕ}
    (hint : IntervalIntegrable f volume a b) (hab : a ≤ b)
    (hN : 0 < N) (hi : i < N) :
    IntervalIntegrable f volume
      (routeBEqualPartitionPoint a b N i)
      (routeBEqualPartitionPoint a b N (i + 1)) := by
  have hleftBounds := routeBEqualPartitionPoint_mem_Icc hab hN (Nat.le_of_lt hi)
  have hrightBounds := routeBEqualPartitionPoint_mem_Icc
    hab hN (Nat.succ_le_iff.mpr hi)
  have hmono := routeBEqualPartitionPoint_mono hab hN (Nat.le_succ i)
  have hleft : routeBEqualPartitionPoint a b N i ∈ Set.uIcc a b :=
    Set.mem_uIcc_of_le hleftBounds.1 (hmono.trans hrightBounds.2)
  have hright : routeBEqualPartitionPoint a b N (i + 1) ∈ Set.uIcc a b :=
    Set.mem_uIcc_of_le (hleftBounds.1.trans hmono) hrightBounds.2
  exact IntervalIntegrable.mono hint
    (Set.uIcc_subset_uIcc hleft hright) le_rfl

theorem intervalIntegrable_routeBNormalizedLowerDifferenceIntegrand
    (n : ℕ) {rho z : ℝ} (hrho : 0 < rho) (hz0 : 0 ≤ z) :
    IntervalIntegrable
      (routeBNormalizedLowerDifferenceIntegrand n rho z)
      volume 0 prawitzSplit := by
  have hr : 0 < routeBDboundR rho z := by
    unfold routeBDboundR routeBDboundW
    positivity
  have hbase := routeB_prawitz_difference_envelope_intervalIntegrable
    routeB_exactMinorantCertificate n hrho hr
  have hscaled := hbase.const_mul (2 * Real.sqrt (n : ℝ) / rho)
  change IntervalIntegrable
    (fun t => 2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖ *
      routeBPowerDifferenceEnvelope routeBKappa routeBTheta n rho
        (routeBDboundR rho z) t) volume 0 prawitzSplit
  simpa only [mul_assoc] using hscaled

theorem intervalIntegrable_routeBNormalizedCorrectionIntegrand
    {n : ℕ} (hn : 0 < n) {rho z : ℝ} (hrho : 0 < rho) (hz0 : 0 ≤ z) :
    IntervalIntegrable
      (routeBNormalizedCorrectionIntegrand n rho z)
      volume 0 prawitzSplit := by
  have hr : 0 < routeBDboundR rho z := by
    unfold routeBDboundR routeBDboundW
    positivity
  have hbase := intervalIntegrable_prawitzCorrectionGaussian
    (t0 := prawitzSplit)
    (routeBSmoothingT n rho (routeBDboundR rho z))
    (by norm_num [prawitzSplit]) (by norm_num [prawitzSplit])
  have hbase' : IntervalIntegrable
      (fun t => ‖prawitzKernelCorrection t‖ *
        routeBPowerGaussianEnvelope n rho (routeBDboundR rho z) t)
      volume 0 prawitzSplit := by
    simpa only [routeBPowerGaussianEnvelope_eq_smoothing_gaussian hn hrho hr] using hbase
  have hscaled := hbase'.const_mul (2 * Real.sqrt (n : ℝ) / rho)
  change IntervalIntegrable
    (fun t => 2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernelCorrection t‖ *
      routeBPowerGaussianEnvelope n rho (routeBDboundR rho z) t)
      volume 0 prawitzSplit
  simpa only [mul_assoc] using hscaled

theorem intervalIntegrable_routeBNormalizedLowIntegrand
    {n : ℕ} (hn : 0 < n) {rho z : ℝ} (hrho : 0 < rho) (hz0 : 0 ≤ z) :
    IntervalIntegrable (routeBNormalizedLowIntegrand n rho z)
      volume 0 prawitzSplit := by
  exact (intervalIntegrable_routeBNormalizedLowerDifferenceIntegrand n hrho hz0).add
    (intervalIntegrable_routeBNormalizedCorrectionIntegrand hn hrho hz0)

theorem intervalIntegrable_routeBNormalizedHighIntegrand
    (n : ℕ) {rho z : ℝ} (hrho : 0 < rho) (hz0 : 0 ≤ z) :
    IntervalIntegrable (routeBNormalizedHighIntegrand n rho z)
      volume prawitzSplit 1 := by
  have hr : 0 < routeBDboundR rho z := by
    unfold routeBDboundR routeBDboundW
    positivity
  have hbase := routeB_prawitz_modulus_envelope_intervalIntegrable
    routeB_exactMinorantCertificate n rho (routeBDboundR rho z)
  have hscaled := hbase.const_mul (2 * Real.sqrt (n : ℝ) / rho)
  change IntervalIntegrable
    (fun t => 2 * Real.sqrt (n : ℝ) / rho * ‖prawitzKernel t‖ *
      routeBPowerModulusEnvelope routeBKappa routeBTheta n rho
        (routeBDboundR rho z) t) volume prawitzSplit 1
  simpa only [mul_assoc] using hscaled

theorem routeBNormalizedLowIntegral_le_dyadicRouteBLowSum_upper
    {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    {rho z : DyadicInterval} {rhoR zR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (hadmissible : ∀ i < N,
      DyadicLowCellAdmissible n rho z (dyadicRouteBLowCell N i)) :
    (∫ t in (0 : ℝ)..prawitzSplit,
      routeBNormalizedLowIntegrand n rhoR zR t) ≤
      (dyadicRouteBLowSum n rho z N).upper := by
  let p := routeBEqualPartitionPoint (0 : ℝ) prawitzSplit N
  have hrhoR := hbox.real_rho_pos hrho
  have hz0 := hbox.real_z_nonnegative hz
  have hint := intervalIntegrable_routeBNormalizedLowIntegrand hn hrhoR hz0
  have hbound := intervalIntegral_le_intervalNatSum_upper
    (f := routeBNormalizedLowIntegrand n rhoR zR) (p := p) (N := N)
    (fun i hi => routeBEqualPartitionPoint_mono
      (by norm_num [prawitzSplit]) hN (Nat.le_succ i))
    (fun i hi => intervalIntegrable_equalPartitionCell hint
      (by norm_num [prawitzSplit]) hN hi)
    (fun i => dyadicLowCellValue n rho z (dyadicRouteBLowCell N i))
    (fun i => (dyadicRouteBLowCell N i).wid)
    (fun i hi => (hadmissible i hi).valueOrdered)
    (fun i hi x hx =>
      routeBNormalizedLowIntegrand_le_dyadicRouteBLowCell_upper
        hN hi hrho hz hbox (hadmissible i hi) hx)
    (fun i hi => dyadicRouteBLowCell_wid_contains hN hi)
  simpa [p, dyadicRouteBLowSum, routeBEqualPartitionPoint_zero,
    routeBEqualPartitionPoint_at_N hN] using hbound

theorem routeBNormalizedHighIntegral_le_dyadicRouteBHighSum_upper
    {n N : ℕ} (hN : 0 < N)
    {rho z : DyadicInterval} {rhoR zR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (hadmissible : ∀ i < N,
      DyadicHighCellAdmissible n rho z (dyadicRouteBHighCell N i)) :
    (∫ t in prawitzSplit..(1 : ℝ),
      routeBNormalizedHighIntegrand n rhoR zR t) ≤
      (dyadicRouteBHighSum n rho z N).upper := by
  let p := routeBEqualPartitionPoint prawitzSplit (1 : ℝ) N
  have hrhoR := hbox.real_rho_pos hrho
  have hz0 := hbox.real_z_nonnegative hz
  have hint := intervalIntegrable_routeBNormalizedHighIntegrand n hrhoR hz0
  have hbound := intervalIntegral_le_intervalNatSum_upper
    (f := routeBNormalizedHighIntegrand n rhoR zR) (p := p) (N := N)
    (fun i hi => routeBEqualPartitionPoint_mono
      (by norm_num [prawitzSplit]) hN (Nat.le_succ i))
    (fun i hi => intervalIntegrable_equalPartitionCell hint
      (by norm_num [prawitzSplit]) hN hi)
    (fun i => dyadicHighCellValue n rho z (dyadicRouteBHighCell N i))
    (fun i => (dyadicRouteBHighCell N i).wid)
    (fun i hi => (hadmissible i hi).valueOrdered)
    (fun i hi x hx =>
      routeBNormalizedHighIntegrand_le_dyadicRouteBHighCell_upper
        hN hi hrho hz hbox (hadmissible i hi) hx)
    (fun i hi => dyadicRouteBHighCell_wid_contains hN hi)
  simpa [p, dyadicRouteBHighSum, routeBEqualPartitionPoint_zero,
    routeBEqualPartitionPoint_at_N hN] using hbound

theorem routeBNormalizedFiniteIntegrals_le_dyadicRouteBFiniteBound_upper
    {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    {rho z : DyadicInterval} {rhoR zR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (hlow : ∀ i < N,
      DyadicLowCellAdmissible n rho z (dyadicRouteBLowCell N i))
    (hhigh : ∀ i < N,
      DyadicHighCellAdmissible n rho z (dyadicRouteBHighCell N i)) :
    (∫ t in (0 : ℝ)..prawitzSplit,
        routeBNormalizedLowIntegrand n rhoR zR t) +
      (∫ t in prawitzSplit..(1 : ℝ),
        routeBNormalizedHighIntegrand n rhoR zR t) ≤
      (dyadicRouteBFiniteBound n rho z N).upper := by
  have hlo := routeBNormalizedLowIntegral_le_dyadicRouteBLowSum_upper
    hn hN hrho hz hbox hlow
  have hhi := routeBNormalizedHighIntegral_le_dyadicRouteBHighSum_upper
    hN hrho hz hbox hhigh
  have hsum := add_le_add hlo hhi
  simpa [dyadicRouteBFiniteBound, DyadicInterval.add, DyadicInterval.upper,
    Int.cast_add, add_div] using hsum

end

end BerryEsseen
