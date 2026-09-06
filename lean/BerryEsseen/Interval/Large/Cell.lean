import BerryEsseen.Smoothing.LargeSampleComparison
import BerryEsseen.CharacteristicFunctions.GaussianCorrection
import BerryEsseen.DyadicPrawitzLargeNCell

/-!
# Interval / Large / Cell
-/

namespace BerryEsseen

open DyadicInterval
open MeasureTheory ProbabilityTheory

noncomputable section

def certifiedLargeMax
    (I J : DyadicInterval) : DyadicInterval :=
  ⟨max I.lo J.lo, max I.hi J.hi⟩

def certifiedLargeRate : DyadicInterval :=
  DyadicInterval.ofRat 39 100

def certifiedLargeDirectRateQ
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  DyadicInterval.maxZero <|
    DyadicInterval.div
      (DyadicInterval.mul certifiedLargeRate
        (DyadicInterval.sqr c.v))
      (dyadicLargeDen L r)

def certifiedLargeDirectStrongQ
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  if c.t.hi ≤ (DyadicInterval.ofRat 1 4).lo then
    certifiedLargeMax (dyadicLargeQ L r c)
      (certifiedLargeDirectRateQ L r c)
  else
    dyadicLargeQ L r c

def certifiedLargeDirectCellStrongQReal
    (L r t hq : ℝ) (cellHi : ℤ) : ℝ :=
  if cellHi ≤ (DyadicInterval.ofRat 1 4).lo then
    max (routeBLargeCellQLower L r hq)
      (largeDirectRateQReal L r t)
  else
    routeBLargeCellQLower L r hq

def certifiedLargeDirectStrongAlphaExp
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  dyadicExpNeg <|
    DyadicInterval.mul dyadicRouteBLargeAlpha
      (certifiedLargeDirectStrongQ L r c)

def certifiedLargeDirectTelescoping
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  let kernelFrequency := DyadicInterval.mul c.k0
    (DyadicInterval.mul (DyadicInterval.point 2)
      (DyadicInterval.mul (DyadicInterval.sqr c.t) dyadicCellTwoPiCubed))
  let diskScale := DyadicInterval.div
    (dyadicPrawitzDstarFeasible r c.v)
    (DyadicInterval.mul (powi r 3) (powi L 3))
  let withDisk := DyadicInterval.mul kernelFrequency diskScale
  let withExp := DyadicInterval.mul withDisk
    (certifiedLargeDirectStrongAlphaExp L r c)
  DyadicInterval.mul withExp (DyadicInterval.point 1)

def certifiedLargeDirectF1
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  ⟨0, min (certifiedLargeDirectTelescoping L r c).hi
    (dyadicLargeTrivial L r c).hi⟩

def certifiedLargeDirectLowCellValue
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  DyadicInterval.add (certifiedLargeDirectF1 L r c)
    (dyadicLargeF3 L r c)

structure CertifiedLargeBoxAdmissible
    (L r : DyadicInterval) : Prop extends DyadicLargeBoxAdmissible L r where
  nineteenTenthsLeR : (DyadicInterval.ofRat 19 10).hi ≤ r.lo

structure CertifiedLargeLowCellAdmissible
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : Prop where
  base : DyadicLargeLowCellAdmissible L r c
  strongAlphaArgNonnegative :
    0 ≤ (DyadicInterval.mul dyadicRouteBLargeAlpha
      (certifiedLargeDirectStrongQ L r c)).lo
  hugeFallback : ¬ 0 < c.t.lo →
    (certifiedLargeDirectTelescoping L r c).hi ≤ dyadicCellHuge.hi
  valueOrdered : (certifiedLargeDirectLowCellValue L r c).Ordered

instance (L r : DyadicInterval) :
    Decidable (CertifiedLargeBoxAdmissible L r) :=
  decidable_of_iff
    (DyadicLargeBoxAdmissible L r ∧
      (DyadicInterval.ofRat 19 10).hi ≤ r.lo) <| by
    constructor
    · rintro ⟨hbase, hr⟩
      exact ⟨hbase, hr⟩
    · intro h
      exact ⟨h.toDyadicLargeBoxAdmissible, h.nineteenTenthsLeR⟩

instance (L r : DyadicInterval) (c : DyadicPrawitzCell) :
    Decidable (CertifiedLargeLowCellAdmissible L r c) :=
  decidable_of_iff
    (DyadicLargeLowCellAdmissible L r c ∧
      0 ≤ (DyadicInterval.mul dyadicRouteBLargeAlpha
        (certifiedLargeDirectStrongQ L r c)).lo ∧
      (¬ 0 < c.t.lo →
        (certifiedLargeDirectTelescoping L r c).hi ≤ dyadicCellHuge.hi) ∧
      (certifiedLargeDirectLowCellValue L r c).lo ≤
        (certifiedLargeDirectLowCellValue L r c).hi) <| by
    constructor
    · rintro ⟨hbase, harg, hhuge, hordered⟩
      exact ⟨hbase, harg, hhuge, hordered⟩
    · intro h
      exact ⟨h.base, h.strongAlphaArgNonnegative,
        h.hugeFallback, h.valueOrdered⟩

theorem certifiedLargeMax_contains
    {I J : DyadicInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (certifiedLargeMax I J).Contains (max x y) := by
  have hscale : (0 : ℝ) ≤ (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos.le
  constructor
  · change ((max I.lo J.lo : ℤ) : ℝ) / (dyadicScale : ℝ) ≤ max x y
    rw [Int.cast_max, ← max_div_div_right hscale]
    exact max_le
      (hx.1.trans (le_max_left _ _))
      (hy.1.trans (le_max_right _ _))
  · change max x y ≤ ((max I.hi J.hi : ℤ) : ℝ) / (dyadicScale : ℝ)
    rw [Int.cast_max, ← max_div_div_right hscale]
    exact max_le_max hx.2 hy.2

theorem certifiedLargeRate_sound :
    certifiedLargeRate.Contains (39 / 100 : ℝ) := by
  simpa [certifiedLargeRate] using
    DyadicInterval.contains_ofRat 39 (b := 100) (by norm_num)

theorem certifiedLargeDirectRateQ_sound
    {L r : DyadicInterval} {c : DyadicPrawitzCell}
    {LR rR tR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR)
    (hv : c.v.Contains (routeBCellV tR))
    (hden : 0 < (dyadicLargeDen L r).lo) :
    (certifiedLargeDirectRateQ L r c).Contains
      (largeDirectRateQReal LR rR tR) := by
  have hv2 := hv.sqr hv.ordered
  have hnum := certifiedLargeRate_sound.mul hv2
  have hdenSound := dyadicLargeDen_sound hL hr
  have hquot := hnum.div hdenSound hdenSound.ordered hden
  have hmax := hquot.maxZero
  have hnonneg : 0 ≤
      (39 / 100 : ℝ) * (2 * Real.pi * tR) ^ 2 /
        (rR ^ 2 * LR ^ 2) := by
    positivity
  simpa [certifiedLargeDirectRateQ, largeDirectRateQReal,
    routeBCellV, max_eq_right hnonneg] using hmax

theorem certifiedLargeDirectStrongQ_sound
    {L r : DyadicInterval} {c : DyadicPrawitzCell}
    {LR rR tR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR)
    (hv : c.v.Contains (routeBCellV tR))
    (hden : 0 < (dyadicLargeDen L r).lo) :
    (certifiedLargeDirectStrongQ L r c).Contains
      (certifiedLargeDirectCellStrongQReal
        LR rR tR c.hq.lower c.t.hi) := by
  have hold := dyadicLargeQ_sound (c := c) hL hr hden
  by_cases hquarter : c.t.hi ≤ (DyadicInterval.ofRat 1 4).lo
  · have hrate := certifiedLargeDirectRateQ_sound hL hr hv hden
    simp only [certifiedLargeDirectStrongQ,
      certifiedLargeDirectCellStrongQReal, if_pos hquarter]
    exact certifiedLargeMax_contains hold hrate
  · simp only [certifiedLargeDirectStrongQ,
      certifiedLargeDirectCellStrongQReal, if_neg hquarter]
    exact hold

lemma feasible_disk_lower_y_le_three
    {r t : ℝ} (hr1 : 1 < r) (hr2 : r ≤ 2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ prawitzSplit) :
    (((2 * Real.pi * t) / r) * (r - 1)) ^ 2 / 2 ≤ 3 := by
  have hbase := routeBLargeDstar_y_le_three hr1.le ht0 ht1
  have hc0 : 0 ≤ (2 * Real.pi * t) / r := by positivity
  have hrm0 : 0 ≤ r - 1 := by linarith
  have hrm1 : r - 1 ≤ 1 := by linarith
  have hprod0 : 0 ≤ ((2 * Real.pi * t) / r) * (r - 1) :=
    mul_nonneg hc0 hrm0
  have hprod : ((2 * Real.pi * t) / r) * (r - 1) ≤
      (2 * Real.pi * t) / r := by
    simpa using mul_le_of_le_one_right hc0 hrm1
  nlinarith

theorem CertifiedLargeBoxAdmissible.real_nineteenTenths_le_r
    {L r : DyadicInterval} (hbox : CertifiedLargeBoxAdmissible L r)
    {rR : ℝ} (hr : r.Contains rR) : (19 / 10 : ℝ) ≤ rR := by
  have hmiddle := dyadic_upper_le_lower_of_hi_le_lo hbox.nineteenTenthsLeR
  have hrat := DyadicInterval.contains_ofRat 19 (b := 10) (by norm_num)
  exact hrat.2.trans (hmiddle.trans hr.1)

theorem certifiedLargeDirectCellStrongQ_le_actual
    {c : DyadicPrawitzCell}
    {LR rR tR : ℝ}
    (ht : c.t.Contains tR)
    (hLPos : 0 < LR) (hrPos : 0 < rR) (ht0 : 0 ≤ tR)
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR)) :
    certifiedLargeDirectCellStrongQReal
        LR rR tR c.hq.lower c.t.hi ≤
      largeDirectStrongQReal LR rR tR := by
  have hold := routeBLargeCellQLower_le hLPos hrPos ht0 <| by
    simpa only [routeBCellV] using hhq
  by_cases hquarter : c.t.hi ≤ (DyadicInterval.ofRat 1 4).lo
  · have hquarterContains :=
      DyadicInterval.contains_ofRat 1 (b := 4) (by norm_num)
    have hmiddle := dyadic_upper_le_lower_of_hi_le_lo hquarter
    have hquarterLower : (DyadicInterval.ofRat 1 4).lower ≤
        (1 / 4 : ℝ) := by
      simpa using hquarterContains.1
    have htQuarter : tR ≤ (1 / 4 : ℝ) :=
      ht.2.trans (hmiddle.trans hquarterLower)
    simp only [certifiedLargeDirectCellStrongQReal,
      largeDirectStrongQReal, if_pos hquarter, if_pos htQuarter]
    exact max_le_max hold le_rfl
  · simp only [certifiedLargeDirectCellStrongQReal, if_neg hquarter]
    unfold largeDirectStrongQReal
    split_ifs
    · exact hold.trans (le_max_left _ _)
    · exact hold

theorem certifiedLargeDirectStrongAlphaExp_sound
    {L r : DyadicInterval} {c : DyadicPrawitzCell}
    {LR rR tR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR)
    (hv : c.v.Contains (routeBCellV tR))
    (hden : 0 < (dyadicLargeDen L r).lo)
    (harg : 0 ≤ (DyadicInterval.mul dyadicRouteBLargeAlpha
      (certifiedLargeDirectStrongQ L r c)).lo) :
    (certifiedLargeDirectStrongAlphaExp L r c).Contains
      (Real.exp (-routeBLargeNAlpha *
        certifiedLargeDirectCellStrongQReal
          LR rR tR c.hq.lower c.t.hi)) := by
  have hq := certifiedLargeDirectStrongQ_sound hL hr hv hden
  have hproduct := dyadicRouteBLargeAlpha_sound.mul hq
  simpa [certifiedLargeDirectStrongAlphaExp] using
    dyadicExpNeg_sound hproduct harg

def certifiedLargeDirectCellTelescopingReal
    (L r t k0 hq : ℝ) (cellHi : ℤ) : ℝ :=
  k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
    (refinedRouteBDiskStar r (2 * Real.pi * t / r) /
      (r ^ 3 * L ^ 3)) *
    Real.exp (-routeBLargeNAlpha *
      certifiedLargeDirectCellStrongQReal
        L r t hq cellHi)

theorem largeDirectTelescopingReal_le_cell
    {L r t k0 hq : ℝ} {cellHi : ℤ}
    (hL : 0 < L) (hr : 0 < r) (ht0 : 0 ≤ t) (hk00 : 0 ≤ k0)
    (hQ : certifiedLargeDirectCellStrongQReal L r t hq cellHi ≤
      largeDirectStrongQReal L r t) :
    largeDirectTelescopingReal L r t k0 ≤
      certifiedLargeDirectCellTelescopingReal
        L r t k0 hq cellHi := by
  have halpha0 : 0 ≤ routeBLargeNAlpha := routeBLargeNAlpha_nonneg
  have hexp :
      Real.exp (-routeBLargeNAlpha * largeDirectStrongQReal L r t) ≤
        Real.exp (-routeBLargeNAlpha *
          certifiedLargeDirectCellStrongQReal L r t hq cellHi) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hfrequency0 : 0 ≤ 2 * (t ^ 2 * (2 * Real.pi) ^ 3) := by
    positivity
  have hden0 : 0 ≤ r ^ 3 * L ^ 3 := by positivity
  have hdisk0 : 0 ≤
      refinedRouteBDiskStar r (2 * Real.pi * t / r) /
        (r ^ 3 * L ^ 3) := by
    exact div_nonneg (Real.sqrt_nonneg _) hden0
  unfold largeDirectTelescopingReal
    certifiedLargeDirectCellTelescopingReal
  exact mul_le_mul_of_nonneg_left hexp
    (mul_nonneg (mul_nonneg hk00 hfrequency0) hdisk0)

theorem certifiedLargeDirectTelescoping_sound
    {L r : DyadicInterval} {c : DyadicPrawitzCell}
    {LR rR tR k0R : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR)
    (ht : c.t.Contains tR) (hk0 : c.k0.Contains k0R)
    (hv : c.v.Contains (routeBCellV tR))
    (hbox : CertifiedLargeBoxAdmissible L r)
    (hcell : CertifiedLargeLowCellAdmissible L r c)
    (ht0 : 0 ≤ tR) (ht1 : tR ≤ prawitzSplit) :
    (certifiedLargeDirectTelescoping L r c).Contains
      (certifiedLargeDirectCellTelescopingReal
        LR rR tR k0R c.hq.lower c.t.hi) := by
  have hbase := hbox.toDyadicLargeBoxAdmissible
  have hLR := hbase.real_L_pos hL
  have hrR := hbase.real_r_pos hr
  have hr19 := hbox.real_nineteenTenths_le_r hr
  have hrStrict : 1 < rR := by norm_num at hr19 ⊢; linarith
  have hr2 := hbase.real_r_le_two hr
  have hv0 : 0 ≤ routeBCellV tR := by
    unfold routeBCellV
    positivity
  have hyLower := feasible_disk_lower_y_le_three
    hrStrict hr2 ht0 ht1
  have hyUpper := routeBLargeDstar_y_le_three hrStrict.le ht0 ht1
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have ht2 := ht.sqr ht.ordered
  have hfrequency := ht2.mul dyadicCellTwoPiCubed_sound
  have hkernelFrequency := hk0.mul (htwo.mul hfrequency)
  have hD := dyadicPrawitzDstarFeasible_sound
    hr hv hbase.rPos hrStrict hr2 hv0 hyLower hyUpper
  have hr3 := powi_sound hr 3
  have hL3 := powi_sound hL 3
  have hdiskDenSound := hr3.mul hL3
  have hdiskScale := hD.div hdiskDenSound hdiskDenSound.ordered
    hbase.diskDenPos
  have hwithDisk := hkernelFrequency.mul hdiskScale
  have hexp := certifiedLargeDirectStrongAlphaExp_sound
    hL hr hv hbase.denPos hcell.strongAlphaArgNonnegative
  have hwithExp := hwithDisk.mul hexp
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have hresult := hwithExp.mul hone
  unfold certifiedLargeDirectTelescoping
    certifiedLargeDirectCellTelescopingReal
  dsimp only
  convert hresult using 1 <;> simp only [routeBCellV] <;> ring

theorem lawNormalizedDifferenceIntegrand_le_directF1_upper
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 100 ≤ n)
    {L r : DyadicInterval} {c : DyadicPrawitzCell} {tR : ℝ}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (ht : c.t.Contains tR)
    (hv : c.v.Contains (routeBCellV tR))
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hk0 : c.k0.Contains (prawitzK0Envelope tR))
    (hbox : CertifiedLargeBoxAdmissible L r)
    (hcell : CertifiedLargeLowCellAdmissible L r c)
    (ht0 : 0 ≤ tR) (ht1 : tR ≤ prawitzSplit) :
    lawNormalizedDifferenceIntegrand n mu tR ≤
      (certifiedLargeDirectF1 L r c).upper := by
  let LR := routeBSmoothingScale n (thirdAbsoluteMoment mu)
  let rR := symmetrizationRatio mu
  let k0R := prawitzK0Envelope tR
  have hbase := hbox.toDyadicLargeBoxAdmissible
  have hLR : 0 < LR := hbase.real_L_pos hL
  have hrR : 0 < rR := hbase.real_r_pos hr
  have hr19 : (19 / 10 : ℝ) ≤ rR :=
    hbox.real_nineteenTenths_le_r hr
  have hk0Real : tR * ‖prawitzKernel tR‖ ≤ k0R := by
    dsimp only [k0R]
    exact t_mul_norm_prawitzKernel_le_K0Envelope ht0
      (ht1.trans_lt (by norm_num [prawitzSplit]))
  have hk0Nonnegative : 0 ≤ k0R :=
    (mul_nonneg ht0 (norm_nonneg _)).trans hk0Real
  have hLawTel :=
    lawNormalizedDifferenceIntegrand_le_large_telescoping
      mu hX hmean hsecond hn hr19 ht0 hk0Real
  have hQ := certifiedLargeDirectCellStrongQ_le_actual
    ht hLR hrR ht0 hhq
  have hTelCell := largeDirectTelescopingReal_le_cell
    hLR hrR ht0 hk0Nonnegative hQ
  have hTelContains := certifiedLargeDirectTelescoping_sound
    hL hr ht hk0 hv hbox hcell ht0 ht1
  have hTelUpper : lawNormalizedDifferenceIntegrand n mu tR ≤
      (certifiedLargeDirectTelescoping L r c).upper :=
    hLawTel.trans (hTelCell.trans hTelContains.2)
  have hTrivUpper : lawNormalizedDifferenceIntegrand n mu tR ≤
      (dyadicLargeTrivial L r c).upper := by
    by_cases htLo : 0 < c.t.lo
    · have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
        exact_mod_cast dyadicScale_pos
      have hcLowerPos : 0 < c.t.lower := by
        unfold DyadicInterval.lower
        exact div_pos (by exact_mod_cast htLo) hscale
      have htRPos : 0 < tR := hcLowerPos.trans_le ht.1
      have hLawOld := lawNormalizedDifferenceIntegrand_le_large_old
        mu hX hmean hsecond hn ht0
      have hRouteTriv := routeBLargeLowerDifference_le_cellTrivial
        hLR hrR htRPos hhq hk0Real
      have hTrivContains := dyadicLargeTrivial_sound
        (LR := LR) (rR := rR) (tR := tR) (k0R := k0R)
        (vR := routeBCellV tR) hL hr ht hk0 hv hbase.denPos
          hbase.normalDenPos hcell.base.normalArgNonnegative htLo
          (hcell.base.trivialDen htLo)
      exact hLawOld.trans (hRouteTriv.trans hTrivContains.2)
    · rw [dyadicLargeTrivial, if_neg htLo]
      have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
        exact_mod_cast dyadicScale_pos
      exact hTelUpper.trans
        (div_le_div_of_nonneg_right
          (by exact_mod_cast hcell.hugeFallback htLo) hscale.le)
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  change lawNormalizedDifferenceIntegrand n mu tR ≤
    ((min (certifiedLargeDirectTelescoping L r c).hi
      (dyadicLargeTrivial L r c).hi : ℤ) : ℝ) / (dyadicScale : ℝ)
  rw [Int.cast_min, ← min_div_div_right hscale.le]
  exact le_min hTelUpper hTrivUpper

theorem lawNormalizedLowIntegrand_le_directCell_upper
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 100 ≤ n)
    {L r : DyadicInterval} {c : DyadicPrawitzCell} {tR : ℝ}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (ht : c.t.Contains tR)
    (hv : c.v.Contains (routeBCellV tR))
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hk0 : c.k0.Contains (prawitzK0Envelope tR))
    (hkd2 : c.kd2.Contains (prawitzKD2Envelope tR))
    (hbox : CertifiedLargeBoxAdmissible L r)
    (hcell : CertifiedLargeLowCellAdmissible L r c)
    (ht0 : 0 ≤ tR) (ht1 : tR ≤ prawitzSplit) :
    lawNormalizedLowIntegrand n mu tR ≤
      (certifiedLargeDirectLowCellValue L r c).upper := by
  have hdiff := lawNormalizedDifferenceIntegrand_le_directF1_upper
    mu hX hmean hsecond hn hL hr ht hv hhq hk0 hbox hcell ht0 ht1
  have hcorrLarge := lawNormalizedCorrectionIntegrand_le_large
    mu hX hmean hsecond (t := tR) hn
  have hcorrCell := routeBLargeCorrection_le_dyadicLargeF3_upper
    hL hr hv hkd2 hbox.toDyadicLargeBoxAdmissible hcell.base ht0
      (ht1.trans_lt (by norm_num [prawitzSplit]))
  have hsum := add_le_add hdiff (hcorrLarge.trans hcorrCell)
  simpa [lawNormalizedLowIntegrand,
    certifiedLargeDirectLowCellValue, DyadicInterval.add,
    DyadicInterval.upper, Int.cast_add, add_div] using hsum

theorem lawNormalizedHighIntegrand_le_directCell_upper
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 100 ≤ n)
    {L r : DyadicInterval} {c : DyadicPrawitzCell} {tR : ℝ}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hkh2 : c.kh2.Contains (prawitzKH2Envelope tR))
    (hbox : CertifiedLargeBoxAdmissible L r)
    (hcell : DyadicLargeHighCellAdmissible L r c)
    (ht0 : 0 < tR) (ht1 : tR ≤ 1) :
    lawNormalizedHighIntegrand n mu tR ≤
      (dyadicLargeHighCellValue L r c).upper := by
  have hlaw := lawNormalizedHighIntegrand_le_large
    mu hX hmean hsecond hn ht0.le
  have hcellUpper := routeBLargeHighIntegrand_le_dyadicLargeHighCellValue_upper
    hL hr hhq hkh2 hbox.toDyadicLargeBoxAdmissible hcell ht0 ht1
  exact hlaw.trans hcellUpper

end

end BerryEsseen
