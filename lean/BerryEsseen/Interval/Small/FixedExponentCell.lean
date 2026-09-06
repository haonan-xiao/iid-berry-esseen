import BerryEsseen.Interval.Large.Cell
import BerryEsseen.DyadicPrawitzLargeNSmallCell

/-!
# Interval / Small / Fixed Exponent Cell
-/

namespace BerryEsseen

open DyadicInterval
open MeasureTheory ProbabilityTheory intervalIntegral

noncomputable section

def certifiedLargeSmallRateQ
    (r y : DyadicInterval) : DyadicInterval :=
  DyadicInterval.maxZero <|
    DyadicInterval.div
      (DyadicInterval.mul certifiedLargeRate
        (DyadicInterval.sqr (dyadicRouteBLargeSmallYV y)))
      (DyadicInterval.sqr r)

def certifiedLargeSmallRateQReal (r y : ℝ) : ℝ :=
  (39 / 100 : ℝ) * (2 * Real.pi * y) ^ 2 / r ^ 2

def certifiedLargeSmallStrongQ
    (L r y : DyadicInterval) : DyadicInterval :=
  certifiedLargeMax
    (dyadicRouteBLargeSmallLowQ L r y)
    (certifiedLargeSmallRateQ r y)

def certifiedLargeSmallCellStrongQReal
    (r y ql : ℝ) : ℝ :=
  max (routeBLargeSmallLowCellQ r y ql)
    (certifiedLargeSmallRateQReal r y)

def certifiedLargeSmallStrongAlphaExp
    (L r y : DyadicInterval) : DyadicInterval :=
  dyadicExpNeg <|
    DyadicInterval.mul dyadicRouteBLargeAlpha
      (certifiedLargeSmallStrongQ L r y)

def certifiedLargeSmallF1
    (L r y : DyadicInterval) : DyadicInterval :=
  let scale := DyadicInterval.div
    (DyadicInterval.mul (DyadicInterval.point 8)
      (DyadicInterval.sqr checkerPi))
    (powi r 3)
  let withY := DyadicInterval.mul scale (DyadicInterval.sqr y)
  let withP0 := DyadicInterval.mul withY
    (dyadicRouteBLargeSmallP0 L y)
  DyadicInterval.mul withP0
    (DyadicInterval.mul
      (dyadicPrawitzDstarFeasible r
        (dyadicRouteBLargeSmallV L y))
      (certifiedLargeSmallStrongAlphaExp L r y))

def certifiedLargeSmallCellValue
    (L r y : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add
    (DyadicInterval.add (certifiedLargeSmallF1 L r y)
      (dyadicRouteBLargeSmallF3 L r y))
    (dyadicRouteBLargeSmallF2 L r y)

structure CertifiedLargeSmallBoxAdmissible
    (L r : DyadicInterval) : Prop extends DyadicLargeSmallBoxAdmissible L r where
  nineteenTenthsLeR : (DyadicInterval.ofRat 19 10).hi ≤ r.lo

structure CertifiedLargeSmallCellAdmissible
    (L r y : DyadicInterval) : Prop where
  base : DyadicLargeSmallCellAdmissible L r y
  strongAlphaArgNonnegative :
    0 ≤ (DyadicInterval.mul dyadicRouteBLargeAlpha
      (certifiedLargeSmallStrongQ L r y)).lo
  valueOrdered : (certifiedLargeSmallCellValue L r y).Ordered

instance (L r : DyadicInterval) :
    Decidable (CertifiedLargeSmallBoxAdmissible L r) :=
  decidable_of_iff
    (DyadicLargeSmallBoxAdmissible L r ∧
      (DyadicInterval.ofRat 19 10).hi ≤ r.lo) <| by
    constructor
    · rintro ⟨hbase, hr⟩
      exact ⟨hbase, hr⟩
    · intro h
      exact ⟨h.toDyadicLargeSmallBoxAdmissible, h.nineteenTenthsLeR⟩

instance (L r y : DyadicInterval) :
    Decidable (CertifiedLargeSmallCellAdmissible L r y) :=
  decidable_of_iff
    (DyadicLargeSmallCellAdmissible L r y ∧
      0 ≤ (DyadicInterval.mul dyadicRouteBLargeAlpha
        (certifiedLargeSmallStrongQ L r y)).lo ∧
      (certifiedLargeSmallCellValue L r y).lo ≤
        (certifiedLargeSmallCellValue L r y).hi) <| by
    constructor
    · rintro ⟨hbase, harg, hordered⟩
      exact ⟨hbase, harg, hordered⟩
    · intro h
      exact ⟨h.base, h.strongAlphaArgNonnegative, h.valueOrdered⟩

theorem CertifiedLargeSmallBoxAdmissible.real_nineteenTenths_le_r
    {L r : DyadicInterval}
    (hbox : CertifiedLargeSmallBoxAdmissible L r)
    {rR : ℝ} (hr : r.Contains rR) : (19 / 10 : ℝ) ≤ rR := by
  have hmiddle := dyadic_upper_le_lower_of_hi_le_lo hbox.nineteenTenthsLeR
  have hrat := DyadicInterval.contains_ofRat 19 (b := 10) (by norm_num)
  exact hrat.2.trans (hmiddle.trans hr.1)

theorem certifiedLargeSmallRateQ_sound
    {r y : DyadicInterval} {rR yR : ℝ}
    (hr : r.Contains rR) (hy : y.Contains yR)
    (hr2Lo : 0 < (DyadicInterval.sqr r).lo) :
    (certifiedLargeSmallRateQ r y).Contains
      (certifiedLargeSmallRateQReal rR yR) := by
  have hyv := dyadicRouteBLargeSmallYV_sound hy
  have hyv2 := hyv.sqr hyv.ordered
  have hnum := certifiedLargeRate_sound.mul hyv2
  have hr2 := hr.sqr hr.ordered
  have hquot := hnum.div hr2 hr2.ordered hr2Lo
  have hmax := hquot.maxZero
  have hnonneg : 0 ≤ certifiedLargeSmallRateQReal rR yR := by
    unfold certifiedLargeSmallRateQReal
    positivity
  have hmax' : (certifiedLargeSmallRateQ r y).Contains
      (max 0 (certifiedLargeSmallRateQReal rR yR)) := by
    simpa [certifiedLargeSmallRateQ,
      certifiedLargeSmallRateQReal] using hmax
  simpa [max_eq_right hnonneg] using hmax'

theorem certifiedLargeSmallStrongQ_sound
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hr2Lo : 0 < (DyadicInterval.sqr r).lo) :
    (certifiedLargeSmallStrongQ L r y).Contains
      (certifiedLargeSmallCellStrongQReal rR yR
        (dyadicRouteBLargeSmallLowLine L y).lower) := by
  have hold := dyadicRouteBLargeSmallLowQ_sound hL hr hy hr2Lo
  have hrate := certifiedLargeSmallRateQ_sound hr hy hr2Lo
  simpa [certifiedLargeSmallStrongQ,
    certifiedLargeSmallCellStrongQReal] using
      certifiedLargeMax_contains hold hrate

lemma certifiedLargeSmallRateQReal_eq_direct
    {L r y : ℝ} (hL : 0 < L) (hr : 0 < r) :
    certifiedLargeSmallRateQReal r y =
      largeDirectRateQReal L r (L * y) := by
  unfold certifiedLargeSmallRateQReal largeDirectRateQReal
  field_simp [hL.ne', hr.ne']

theorem certifiedLargeSmallCellStrongQ_le_actual
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hLR : 0 < LR) (hLupper : LR ≤ 1 / 16)
    (hrR : 0 < rR) (hy0 : 0 ≤ yR) (hy4 : yR ≤ 4) :
    certifiedLargeSmallCellStrongQReal rR yR
        (dyadicRouteBLargeSmallLowLine L y).lower ≤
      largeDirectStrongQReal LR rR (LR * yR) := by
  have holdCell := routeBLargeSmallLowCellQ_le hL hr hy hrR
  have hold := holdCell.trans
    (routeBLargeSmallLowQ_le hLR hLupper hrR hy0 hy4)
  have hquarter : LR * yR ≤ 1 / 4 := by
    nlinarith [mul_le_mul hLupper hy4 hy0
      (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have hrate := certifiedLargeSmallRateQReal_eq_direct
    (L := LR) (r := rR) (y := yR) hLR hrR
  unfold certifiedLargeSmallCellStrongQReal
    largeDirectStrongQReal
  rw [if_pos hquarter, hrate]
  exact max_le_max hold le_rfl

theorem certifiedLargeSmallStrongAlphaExp_sound
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hr2Lo : 0 < (DyadicInterval.sqr r).lo)
    (harg : 0 ≤ (DyadicInterval.mul dyadicRouteBLargeAlpha
      (certifiedLargeSmallStrongQ L r y)).lo) :
    (certifiedLargeSmallStrongAlphaExp L r y).Contains
      (Real.exp (-routeBLargeNAlpha *
        certifiedLargeSmallCellStrongQReal rR yR
          (dyadicRouteBLargeSmallLowLine L y).lower)) := by
  have hq := certifiedLargeSmallStrongQ_sound hL hr hy hr2Lo
  have hproduct := dyadicRouteBLargeAlpha_sound.mul hq
  simpa [certifiedLargeSmallStrongAlphaExp] using
    dyadicExpNeg_sound hproduct harg

theorem certifiedLargeSmallF1_sound
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hbox : CertifiedLargeSmallBoxAdmissible L r)
    (hcell : CertifiedLargeSmallCellAdmissible L r y)
    (hy0 : 0 ≤ yR) (hy4 : yR ≤ 4) :
    (certifiedLargeSmallF1 L r y).Contains
      (routeBLargeSmallCellF1 rR yR
        (prawitzK0Envelope (LR * yR))
        (certifiedLargeSmallCellStrongQReal rR yR
          (dyadicRouteBLargeSmallLowLine L y).lower)
        (refinedRouteBDiskStar rR
          (2 * Real.pi * LR * yR / rR))) := by
  have hbase := hbox.toDyadicLargeSmallBoxAdmissible
  have hLR0 := hbase.real_L_nonnegative hL
  have hLR16 := hbase.real_L_le_sixteenth hL
  have hrR := hbase.real_r_pos hr
  have hr19 := hbox.real_nineteenTenths_le_r hr
  have hrStrict : 1 < rR := by norm_num at hr19 ⊢; linarith
  have hr2 := hbase.real_r_le_two hr
  have ht0 : 0 ≤ LR * yR := mul_nonneg hLR0 hy0
  have htSplit : LR * yR ≤ prawitzSplit := by
    have hquarter : LR * yR ≤ 1 / 4 := by
      nlinarith [mul_le_mul hLR16 hy4 hy0
        (by norm_num : (0 : ℝ) ≤ 1 / 16)]
    norm_num [prawitzSplit] at hquarter ⊢
    linarith
  have hv := dyadicRouteBLargeSmallV_sound hL hy
  have hv0 : 0 ≤ 2 * Real.pi * LR * yR := by positivity
  have hyLower := feasible_disk_lower_y_le_three
    hrStrict hr2 ht0 htSplit
  have hyLower' :
      ((2 * Real.pi * LR * yR / rR) * (rR - 1)) ^ 2 / 2 ≤ 3 := by
    simpa [mul_assoc] using hyLower
  have hyUpper := routeBLargeDstar_y_le_three
    hrStrict.le ht0 htSplit
  have hyUpper' :
      (2 * Real.pi * LR * yR / rR) ^ 2 / 2 ≤ 3 := by
    simpa [mul_assoc] using hyUpper
  have height : (DyadicInterval.point 8).Contains (8 : ℝ) := by
    simpa using DyadicInterval.contains_point (8 : ℤ)
  have hpi2 := checkerPi_contains_pi.sqr checkerPi_contains_pi.ordered
  have hnum := height.mul hpi2
  have hr3 := powi_sound hr 3
  have hscale := hnum.div hr3 hr3.ordered hbase.rCubePos
  have hy2 := hy.sqr hy.ordered
  have hwithY := hscale.mul hy2
  have hP0 := dyadicRouteBLargeSmallP0_sound hL hy hcell.base.lowCotDenom
  have hwithP0 := hwithY.mul hP0
  have hD := dyadicPrawitzDstarFeasible_sound
    hr hv hbase.rPos hrStrict hr2 hv0 hyLower' hyUpper'
  have hExp := certifiedLargeSmallStrongAlphaExp_sound
    hL hr hy hbase.rSqPos hcell.strongAlphaArgNonnegative
  have hresult := hwithP0.mul (hD.mul hExp)
  unfold certifiedLargeSmallF1 routeBLargeSmallCellF1
  dsimp only
  convert hresult using 1 <;> ring

lemma routeBLargeSmallCellF1_mono_q
    {r y k0 q Q D : ℝ}
    (hr : 0 < r) (hy0 : 0 ≤ y) (hk00 : 0 ≤ k0)
    (hD0 : 0 ≤ D) (hq : q ≤ Q) :
    routeBLargeSmallCellF1 r y k0 Q D ≤
      routeBLargeSmallCellF1 r y k0 q D := by
  have hexp : Real.exp (-routeBLargeNAlpha * Q) ≤
      Real.exp (-routeBLargeNAlpha * q) := by
    apply Real.exp_le_exp.mpr
    have halpha0 := routeBLargeNAlpha_nonneg
    nlinarith
  have hprefix0 : 0 ≤
      (8 * Real.pi ^ 2 / r ^ 3) * y ^ 2 *
        (2 * Real.pi * k0) * D := by
    positivity
  unfold routeBLargeSmallCellF1
  exact mul_le_mul_of_nonneg_left hexp hprefix0

lemma largeDirectTelescoping_mul_scale_eq_smallCellF1
    {L r y k0 : ℝ} (hL : 0 < L) (hr : 0 < r) :
    L * largeDirectTelescopingReal L r (L * y) k0 =
      routeBLargeSmallCellF1 r y k0
        (largeDirectStrongQReal L r (L * y))
        (refinedRouteBDiskStar r (2 * Real.pi * L * y / r)) := by
  unfold largeDirectTelescopingReal routeBLargeSmallCellF1
  field_simp [hL.ne', hr.ne'] <;> ring

theorem lawNormalizedDifference_mul_scale_le_smallCellF1
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 100 ≤ n) {y q k0 : ℝ}
    (hr19 : 19 / 10 ≤ symmetrizationRatio mu)
    (hy0 : 0 ≤ y)
    (hk0 : routeBSmoothingScale n (thirdAbsoluteMoment mu) * y *
        ‖prawitzKernel
          (routeBSmoothingScale n (thirdAbsoluteMoment mu) * y)‖ ≤ k0)
    (hq : q ≤ largeDirectStrongQReal
      (routeBSmoothingScale n (thirdAbsoluteMoment mu))
      (symmetrizationRatio mu)
      (routeBSmoothingScale n (thirdAbsoluteMoment mu) * y)) :
    routeBSmoothingScale n (thirdAbsoluteMoment mu) *
        lawNormalizedDifferenceIntegrand n mu
          (routeBSmoothingScale n (thirdAbsoluteMoment mu) * y) ≤
      routeBLargeSmallCellF1 (symmetrizationRatio mu) y k0 q
        (refinedRouteBDiskStar (symmetrizationRatio mu)
          (2 * Real.pi * routeBSmoothingScale n (thirdAbsoluteMoment mu) * y /
            symmetrizationRatio mu)) := by
  let L := routeBSmoothingScale n (thirdAbsoluteMoment mu)
  let r := symmetrizationRatio mu
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrho : 1 ≤ thirdAbsoluteMoment mu :=
    thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < thirdAbsoluteMoment mu := zero_lt_one.trans_le hrho
  have hL : 0 < L := by
    dsimp only [L]
    exact routeBSmoothingScale_pos hnPos hrhoPos
  have hr : 0 < r := by
    dsimp only [r]
    norm_num at hr19 ⊢
    linarith
  have ht0 : 0 ≤ L * y := mul_nonneg hL.le hy0
  have hk00 : 0 ≤ k0 := by
    exact (mul_nonneg ht0 (norm_nonneg _)).trans
      (by simpa only [L] using hk0)
  have hD0 : 0 ≤ refinedRouteBDiskStar r (2 * Real.pi * L * y / r) := by
    unfold refinedRouteBDiskStar
    positivity
  have hlaw := lawNormalizedDifferenceIntegrand_le_large_telescoping
    mu hX hmean hsecond hn hr19 ht0 (by simpa only [L] using hk0)
  have hscaled := mul_le_mul_of_nonneg_left hlaw hL.le
  calc
    routeBSmoothingScale n (thirdAbsoluteMoment mu) *
        lawNormalizedDifferenceIntegrand n mu
          (routeBSmoothingScale n (thirdAbsoluteMoment mu) * y) =
      L * lawNormalizedDifferenceIntegrand n mu (L * y) := by rfl
    _ ≤ L * largeDirectTelescopingReal L r (L * y) k0 := by
      simpa only [L, r] using hscaled
    _ = routeBLargeSmallCellF1 r y k0
        (largeDirectStrongQReal L r (L * y))
        (refinedRouteBDiskStar r (2 * Real.pi * L * y / r)) :=
      largeDirectTelescoping_mul_scale_eq_smallCellF1 hL hr
    _ ≤ routeBLargeSmallCellF1 r y k0 q
        (refinedRouteBDiskStar r (2 * Real.pi * L * y / r)) :=
      routeBLargeSmallCellF1_mono_q hr hy0 hk00 hD0 hq
    _ = routeBLargeSmallCellF1 (symmetrizationRatio mu) y k0 q
        (refinedRouteBDiskStar (symmetrizationRatio mu)
          (2 * Real.pi * routeBSmoothingScale n (thirdAbsoluteMoment mu) * y /
            symmetrizationRatio mu)) := by rfl

theorem lawNormalizedDifference_mul_scale_le_smallF1_upper
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 100 ≤ n)
    {L r y : DyadicInterval} {yR : ℝ}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (hy : y.Contains yR)
    (hbox : CertifiedLargeSmallBoxAdmissible L r)
    (hcell : CertifiedLargeSmallCellAdmissible L r y)
    (hy0 : 0 ≤ yR) (hy4 : yR ≤ 4) :
    routeBSmoothingScale n (thirdAbsoluteMoment mu) *
        lawNormalizedDifferenceIntegrand n mu
          (routeBSmoothingScale n (thirdAbsoluteMoment mu) * yR) ≤
      (certifiedLargeSmallF1 L r y).upper := by
  let LR := routeBSmoothingScale n (thirdAbsoluteMoment mu)
  let rR := symmetrizationRatio mu
  let q := certifiedLargeSmallCellStrongQReal rR yR
    (dyadicRouteBLargeSmallLowLine L y).lower
  let k0 := prawitzK0Envelope (LR * yR)
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrho : 1 ≤ thirdAbsoluteMoment mu :=
    thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < thirdAbsoluteMoment mu := zero_lt_one.trans_le hrho
  have hLR : 0 < LR := by
    dsimp only [LR]
    exact routeBSmoothingScale_pos hnPos hrhoPos
  have hLRupper : LR ≤ 1 / 16 :=
    hbox.toDyadicLargeSmallBoxAdmissible.real_L_le_sixteenth hL
  have hrR : 0 < rR :=
    hbox.toDyadicLargeSmallBoxAdmissible.real_r_pos hr
  have hr19 : 19 / 10 ≤ rR := hbox.real_nineteenTenths_le_r hr
  have ht0 : 0 ≤ LR * yR := mul_nonneg hLR.le hy0
  have hquarter : LR * yR ≤ 1 / 4 := by
    nlinarith [mul_le_mul hLRupper hy4 hy0
      (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have ht1 : LR * yR < 1 := hquarter.trans_lt (by norm_num)
  have hk0 : LR * yR * ‖prawitzKernel (LR * yR)‖ ≤ k0 := by
    dsimp only [k0]
    exact t_mul_norm_prawitzKernel_le_K0Envelope ht0 ht1
  have hq : q ≤ largeDirectStrongQReal LR rR (LR * yR) := by
    dsimp only [q]
    exact certifiedLargeSmallCellStrongQ_le_actual
      hL hr hy hLR hLRupper hrR hy0 hy4
  have hreal := lawNormalizedDifference_mul_scale_le_smallCellF1
    mu hX hmean hsecond hn hr19 hy0
      (by simpa only [LR, k0] using hk0)
      (by simpa only [LR, rR, q] using hq)
  have hcontains := certifiedLargeSmallF1_sound
    hL hr hy hbox hcell hy0 hy4
  exact hreal.trans <| by
    simpa only [LR, rR, q, k0] using hcontains.2

theorem lawNormalizedCorrection_mul_scale_le_smallF3_upper
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 100 ≤ n)
    {L r y : DyadicInterval} {yR : ℝ}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (hy : y.Contains yR)
    (hbox : CertifiedLargeSmallBoxAdmissible L r)
    (hcell : CertifiedLargeSmallCellAdmissible L r y)
    (hy0 : 0 ≤ yR) (hy4 : yR ≤ 4) :
    routeBSmoothingScale n (thirdAbsoluteMoment mu) *
        lawNormalizedCorrectionIntegrand n mu
          (routeBSmoothingScale n (thirdAbsoluteMoment mu) * yR) ≤
      (dyadicRouteBLargeSmallF3 L r y).upper := by
  let LR := routeBSmoothingScale n (thirdAbsoluteMoment mu)
  let rR := symmetrizationRatio mu
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrho : 1 ≤ thirdAbsoluteMoment mu :=
    thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < thirdAbsoluteMoment mu := zero_lt_one.trans_le hrho
  have hLR : 0 < LR := by
    dsimp only [LR]
    exact routeBSmoothingScale_pos hnPos hrhoPos
  have hLRupper : LR ≤ 1 / 16 :=
    hbox.toDyadicLargeSmallBoxAdmissible.real_L_le_sixteenth hL
  have hrR : 0 < rR :=
    hbox.toDyadicLargeSmallBoxAdmissible.real_r_pos hr
  have ht0 : 0 ≤ LR * yR := mul_nonneg hLR.le hy0
  have hquarter : LR * yR ≤ 1 / 4 := by
    nlinarith [mul_le_mul hLRupper hy4 hy0
      (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have ht1 : LR * yR < 1 := hquarter.trans_lt (by norm_num)
  have hlaw := lawNormalizedCorrectionIntegrand_le_large
    mu hX hmean hsecond (t := LR * yR) hn
  have hscaled := mul_le_mul_of_nonneg_left hlaw hLR.le
  have hsmall := routeBLargeCorrection_mul_scale_le_smallF3
    hLR hLRupper hrR hy0 hy4
  have hF3Real := routeBLargeSmallF3_le_cell
    (L := LR) (r := rR) (y := yR)
    (kd2 := prawitzKD2Envelope (LR * yR)) ht0 ht1 le_rfl
  have hF3Contains := dyadicRouteBLargeSmallF3_sound
    hL hr hy hbox.toDyadicLargeSmallBoxAdmissible hcell.base
  calc
    routeBSmoothingScale n (thirdAbsoluteMoment mu) *
        lawNormalizedCorrectionIntegrand n mu
          (routeBSmoothingScale n (thirdAbsoluteMoment mu) * yR) =
      LR * lawNormalizedCorrectionIntegrand n mu (LR * yR) := by rfl
    _ ≤ LR * routeBLargeCorrectionIntegrand LR rR (LR * yR) := by
      simpa only [LR, rR] using hscaled
    _ ≤ routeBLargeSmallF3 LR rR yR := hsmall
    _ ≤ routeBLargeSmallCellF3 rR yR
        (prawitzKD2Envelope (LR * yR)) := hF3Real
    _ ≤ (dyadicRouteBLargeSmallF3 L r y).upper := hF3Contains.2

theorem lawNormalizedHigh_mul_scale_le_smallF2_upper
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 100 ≤ n)
    {L r y : DyadicInterval} {yR : ℝ}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (hy : y.Contains yR)
    (hbox : CertifiedLargeSmallBoxAdmissible L r)
    (hcell : CertifiedLargeSmallCellAdmissible L r y)
    (hy0 : 0 ≤ yR) (hy4 : yR ≤ 4) :
    routeBSmoothingScale n (thirdAbsoluteMoment mu) *
        lawNormalizedHighIntegrand n mu
          (1 - routeBSmoothingScale n (thirdAbsoluteMoment mu) * yR) ≤
      (dyadicRouteBLargeSmallF2 L r y).upper := by
  let LR := routeBSmoothingScale n (thirdAbsoluteMoment mu)
  let rR := symmetrizationRatio mu
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrho : 1 ≤ thirdAbsoluteMoment mu :=
    thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < thirdAbsoluteMoment mu := zero_lt_one.trans_le hrho
  have hLR : 0 < LR := by
    dsimp only [LR]
    exact routeBSmoothingScale_pos hnPos hrhoPos
  have hLRupper : LR ≤ 1 / 16 :=
    hbox.toDyadicLargeSmallBoxAdmissible.real_L_le_sixteenth hL
  have hrR : 0 < rR :=
    hbox.toDyadicLargeSmallBoxAdmissible.real_r_pos hr
  have hquarter : LR * yR ≤ 1 / 4 := by
    nlinarith [mul_le_mul hLRupper hy4 hy0
      (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have ht0 : 0 ≤ 1 - LR * yR := by linarith
  have hlaw := lawNormalizedHighIntegrand_le_large
    mu hX hmean hsecond (t := 1 - LR * yR) hn ht0
  have hscaled := mul_le_mul_of_nonneg_left hlaw hLR.le
  have hsmall := routeBLargeHigh_mul_scale_le_smallF2
    hLR hLRupper hrR hy0 hy4
  have hhigh0 : 0 < 1 - LR * yR := by linarith
  have hhigh1 : 1 - LR * yR ≤ 1 := by
    have hLy0 : 0 ≤ LR * yR := mul_nonneg hLR.le hy0
    linarith
  have hqHigh0 : 0 ≤ routeBLargeSmallHighQ LR rR yR :=
    routeBLargeSmallHighQ_nonneg _ _ _
  have hF2Real := routeBLargeSmallF2_le_cell
    (L := LR) (r := rR) (y := yR)
    (kh2 := prawitzKH2Envelope (1 - LR * yR))
    (q := routeBLargeSmallHighQ LR rR yR)
    hhigh0 hhigh1 le_rfl hqHigh0 le_rfl
  have hF2Contains := dyadicRouteBLargeSmallF2_sound
    hL hr hy hbox.toDyadicLargeSmallBoxAdmissible hcell.base
  calc
    routeBSmoothingScale n (thirdAbsoluteMoment mu) *
        lawNormalizedHighIntegrand n mu
          (1 - routeBSmoothingScale n (thirdAbsoluteMoment mu) * yR) =
      LR * lawNormalizedHighIntegrand n mu (1 - LR * yR) := by rfl
    _ ≤ LR * routeBLargeHighIntegrand LR rR (1 - LR * yR) := by
      simpa only [LR, rR] using hscaled
    _ ≤ routeBLargeSmallF2 LR rR yR := hsmall
    _ ≤ routeBLargeSmallCellF2
        (prawitzKH2Envelope (1 - LR * yR))
        (routeBLargeSmallHighQ LR rR yR) := hF2Real
    _ ≤ (dyadicRouteBLargeSmallF2 L r y).upper := hF2Contains.2

def lawNormalizedLargeSmallIntegrand
    (n : ℕ) (mu : Measure ℝ) (y : ℝ) : ℝ :=
  let L := routeBSmoothingScale n (thirdAbsoluteMoment mu)
  L * lawNormalizedLowIntegrand n mu (L * y) +
    L * lawNormalizedHighIntegrand n mu (1 - L * y)

theorem lawNormalizedLargeSmallIntegrand_le_cell_upper
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 100 ≤ n)
    {L r y : DyadicInterval} {yR : ℝ}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (hy : y.Contains yR)
    (hbox : CertifiedLargeSmallBoxAdmissible L r)
    (hcell : CertifiedLargeSmallCellAdmissible L r y)
    (hy0 : 0 ≤ yR) (hy4 : yR ≤ 4) :
    lawNormalizedLargeSmallIntegrand n mu yR ≤
      (certifiedLargeSmallCellValue L r y).upper := by
  have hdiff := lawNormalizedDifference_mul_scale_le_smallF1_upper
    mu hX hmean hsecond hn hL hr hy hbox hcell hy0 hy4
  have hcorr := lawNormalizedCorrection_mul_scale_le_smallF3_upper
    mu hX hmean hsecond hn hL hr hy hbox hcell hy0 hy4
  have hhigh := lawNormalizedHigh_mul_scale_le_smallF2_upper
    mu hX hmean hsecond hn hL hr hy hbox hcell hy0 hy4
  have hsum := add_le_add (add_le_add hdiff hcorr) hhigh
  simpa [lawNormalizedLargeSmallIntegrand,
    lawNormalizedLowIntegrand,
    certifiedLargeSmallCellValue, DyadicInterval.add,
    DyadicInterval.upper, Int.cast_add, add_div,
    mul_add, add_assoc] using hsum

end

end BerryEsseen
