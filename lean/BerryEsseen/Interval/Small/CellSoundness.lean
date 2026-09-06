import BerryEsseen.Smoothing.VariableExponentComparison
import BerryEsseen.Interval.VariableExponent

/-!
# Interval / Small / Cell Soundness
-/

namespace BerryEsseen

open DyadicInterval
open MeasureTheory ProbabilityTheory intervalIntegral

noncomputable section

def largeDirectVariableTelescopingReal
    (L r t k0 : ℝ) : ℝ :=
  k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
    (refinedRouteBDiskStar r (2 * Real.pi * t / r) /
      (r ^ 3 * L ^ 3)) *
    Real.exp (-largeVariableAlphaReal L *
      largeDirectStrongQReal L r t)

theorem scalar_normalizedDifference_le_large_variable_telescoping
    {n : ℕ} (hn : 100 ≤ n) {rho r t k0 : ℝ}
    (hrho : 1 ≤ rho) (hr : 19 / 10 ≤ r)
    (hfeasible : rho * (r - 1) ≤ 1)
    (ht0 : 0 ≤ t) (hk0 : t * ‖prawitzKernel t‖ ≤ k0) :
    (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ *
        scalarPowerDifference n rho (rho * (r - 1)) t ≤
      largeDirectVariableTelescopingReal
        (routeBSmoothingScale n rho) r t k0 := by
  let L := routeBSmoothingScale n rho
  let F := scalarModulus rho (rho * (r - 1)) t
  let B := scalarNormalOne rho (rho * (r - 1)) t
  let H := max F B ^ (n - 1)
  let D := routeBDiskBound routeBKappa rho r (2 * Real.pi * t / r)
  let Dstar := refinedRouteBDiskStar r (2 * Real.pi * t / r)
  let E := Real.exp (-largeVariableAlphaReal L *
    largeDirectStrongQReal L r t)
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hrPos : 0 < r := by norm_num at hr ⊢; linarith
  have hrStrict : 1 < r := by norm_num at hr ⊢; linarith
  have hLPos : 0 < L := by
    dsimp only [L, routeBSmoothingScale]
    positivity
  have hrouteR : routeBDboundR rho (rho * (r - 1)) = r := by
    simpa using routeBDboundR_mul_excess hrhoPos.ne'
  have hpower : H ≤ E := by
    simpa only [F, B, H, E, L] using
      scalarMaxPower_le_large_strong_variable_exp
        hn hrho hr hfeasible ht0
  have hc0 : 0 ≤ 2 * Real.pi * t / r := by positivity
  have hD : D ≤ Dstar := by
    simpa only [D, Dstar] using
      refinedRouteBDiskBound_le_diskStar hrho hrStrict hfeasible hc0
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact routeBDiskBound_nonneg _ _ _ _
  have hDstar0 : 0 ≤ Dstar := by
    dsimp only [Dstar, refinedRouteBDiskStar]
    positivity
  have hk00 : 0 ≤ k0 :=
    (mul_nonneg ht0 (norm_nonneg _)).trans hk0
  have hfrequency0 : 0 ≤ 2 * (t ^ 2 * (2 * Real.pi) ^ 3) := by
    positivity
  have hdenPos : 0 < r ^ 3 * L ^ 3 :=
    mul_pos (pow_pos hrPos 3) (pow_pos hLPos 3)
  have hDquot0 : 0 ≤ D / (r ^ 3 * L ^ 3) :=
    div_nonneg hD0 hdenPos.le
  have hDstarQuot0 : 0 ≤ Dstar / (r ^ 3 * L ^ 3) :=
    div_nonneg hDstar0 hdenPos.le
  have hH0 : 0 ≤ H := by
    dsimp only [H]
    exact pow_nonneg
      ((scalarModulus_nonneg rho (rho * (r - 1)) t).trans
        (le_max_left _ _)) _
  have hscalar : scalarPowerDifference n rho (rho * (r - 1)) t ≤
      scalarDiskDifference n rho (rho * (r - 1)) t := by
    unfold scalarPowerDifference
    exact min_le_left _ _
  have hscale0 : 0 ≤
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ := by
    positivity
  have hscaleIdentity :
      Real.sqrt (n : ℝ) * (n : ℝ) / rho ^ 3 = 1 / L ^ 3 := by
    let s := Real.sqrt (n : ℝ)
    have hsSq : s ^ 2 = (n : ℝ) := by
      dsimp only [s]
      exact Real.sq_sqrt hnReal.le
    have hsNe : s ≠ 0 := by
      dsimp only [s]
      exact hsqrt.ne'
    change s * (n : ℝ) / rho ^ 3 = 1 / (rho / s) ^ 3
    rw [← hsSq]
    field_simp [hrhoPos.ne', hsNe]
  have hrewrite :
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ *
          scalarDiskDifference n rho (rho * (r - 1)) t =
        (t * ‖prawitzKernel t‖) *
          (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (D / (r ^ 3 * L ^ 3)) * H := by
    calc
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ *
          scalarDiskDifference n rho (rho * (r - 1)) t =
        (t * ‖prawitzKernel t‖) *
          (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (D / r ^ 3) *
          (Real.sqrt (n : ℝ) * (n : ℝ) / rho ^ 3) * H := by
            dsimp only [D, H, F, B]
            unfold scalarDiskDifference scalarU routeBUFrequency
            rw [hrouteR]
            field_simp [hrhoPos.ne', hrPos.ne']
      _ = (t * ‖prawitzKernel t‖) *
          (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (D / r ^ 3) * (1 / L ^ 3) * H := by
            rw [hscaleIdentity]
      _ = (t * ‖prawitzKernel t‖) *
          (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (D / (r ^ 3 * L ^ 3)) * H := by
            field_simp [hrPos.ne', hLPos.ne']
  calc
    (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ *
        scalarPowerDifference n rho (rho * (r - 1)) t ≤
      (2 * Real.sqrt (n : ℝ) / rho) * ‖prawitzKernel t‖ *
        scalarDiskDifference n rho (rho * (r - 1)) t :=
          mul_le_mul_of_nonneg_left hscalar hscale0
    _ = (t * ‖prawitzKernel t‖) *
          (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (D / (r ^ 3 * L ^ 3)) * H := hrewrite
    _ ≤ k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (D / (r ^ 3 * L ^ 3)) * H := by
      have h1 := mul_le_mul_of_nonneg_right hk0 hfrequency0
      have h2 := mul_le_mul_of_nonneg_right h1 hDquot0
      exact mul_le_mul_of_nonneg_right h2 hH0
    _ ≤ k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (Dstar / (r ^ 3 * L ^ 3)) * H := by
      have hquot := div_le_div_of_nonneg_right hD hdenPos.le
      have hpref0 : 0 ≤ k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) :=
        mul_nonneg hk00 hfrequency0
      have h1 := mul_le_mul_of_nonneg_left hquot hpref0
      exact mul_le_mul_of_nonneg_right h1 hH0
    _ ≤ k0 * (2 * (t ^ 2 * (2 * Real.pi) ^ 3)) *
          (Dstar / (r ^ 3 * L ^ 3)) * E := by
      exact mul_le_mul_of_nonneg_left hpower
        (mul_nonneg (mul_nonneg hk00 hfrequency0) hDstarQuot0)
    _ = largeDirectVariableTelescopingReal L r t k0 := by rfl

theorem lawNormalizedDifferenceIntegrand_le_large_variable_telescoping
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n : ℕ} (hn : 100 ≤ n) {t k0 : ℝ}
    (hr : 19 / 10 ≤ symmetrizationRatio mu)
    (ht0 : 0 ≤ t) (hk0 : t * ‖prawitzKernel t‖ ≤ k0) :
    lawNormalizedDifferenceIntegrand n mu t ≤
      largeDirectVariableTelescopingReal
        (routeBSmoothingScale n (thirdAbsoluteMoment mu))
        (symmetrizationRatio mu) t k0 := by
  let rho := thirdAbsoluteMoment mu
  let r := symmetrizationRatio mu
  have hnOne : 1 ≤ n := by omega
  have hrho : 1 ≤ rho := by
    dsimp only [rho]
    exact thirdAbsoluteMoment_ge_one mu hX hsecond
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hrUpper : r ≤ 1 + 1 / rho := by
    simpa only [rho, r] using symmetrizationRatio_upper mu hX hmean hsecond
  have hdiff : r - 1 ≤ 1 / rho := by linarith
  have hmul : rho * (r - 1) ≤ rho * (1 / rho) :=
    mul_le_mul_of_nonneg_left hdiff (zero_le_one.trans hrho)
  have hfeasible : rho * (r - 1) ≤ 1 := by
    have hcancel : rho * (1 / rho) = 1 := by field_simp
    linarith
  have henvelope := lawNormalizedDifferenceIntegrand_le_envelope
    mu hX hmean hsecond hnOne ht0
  have htel := scalar_normalizedDifference_le_large_variable_telescoping
    hn hrho (by simpa only [r] using hr) hfeasible ht0 hk0
  exact henvelope.trans (by simpa only [rho, r] using htel)

def largeSmallVariableCellF1
    (L r y k0 q D : ℝ) : ℝ :=
  (8 * Real.pi ^ 2 / r ^ 3) * y ^ 2 * (2 * Real.pi * k0) * D *
    Real.exp (-largeVariableAlphaReal L * q)

lemma largeSmallVariableCellF1_mono_q
    {L r y k0 q Q D : ℝ}
    (hr : 0 < r) (hy0 : 0 ≤ y) (hk00 : 0 ≤ k0)
    (hD0 : 0 ≤ D) (hq : q ≤ Q) :
    largeSmallVariableCellF1 L r y k0 Q D ≤
      largeSmallVariableCellF1 L r y k0 q D := by
  have hexp :
      Real.exp (-largeVariableAlphaReal L * Q) ≤
        Real.exp (-largeVariableAlphaReal L * q) := by
    apply Real.exp_le_exp.mpr
    have halpha0 := largeVariableAlphaReal_nonneg L
    nlinarith
  have hprefix0 : 0 ≤
      (8 * Real.pi ^ 2 / r ^ 3) * y ^ 2 *
        (2 * Real.pi * k0) * D := by
    positivity
  unfold largeSmallVariableCellF1
  exact mul_le_mul_of_nonneg_left hexp hprefix0

lemma largeDirectVariableTelescoping_mul_scale_eq_smallCellF1
    {L r y k0 : ℝ} (hL : 0 < L) (hr : 0 < r) :
    L * largeDirectVariableTelescopingReal L r (L * y) k0 =
      largeSmallVariableCellF1 L r y k0
        (largeDirectStrongQReal L r (L * y))
        (refinedRouteBDiskStar r (2 * Real.pi * L * y / r)) := by
  unfold largeDirectVariableTelescopingReal
    largeSmallVariableCellF1
  field_simp [hL.ne', hr.ne'] <;> ring

theorem lawNormalizedDifference_mul_scale_le_smallVariableCellF1
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
      largeSmallVariableCellF1
        (routeBSmoothingScale n (thirdAbsoluteMoment mu))
        (symmetrizationRatio mu) y k0 q
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
  have hlaw :=
    lawNormalizedDifferenceIntegrand_le_large_variable_telescoping
      mu hX hmean hsecond hn hr19 ht0 (by simpa only [L] using hk0)
  have hscaled := mul_le_mul_of_nonneg_left hlaw hL.le
  calc
    routeBSmoothingScale n (thirdAbsoluteMoment mu) *
        lawNormalizedDifferenceIntegrand n mu
          (routeBSmoothingScale n (thirdAbsoluteMoment mu) * y) =
      L * lawNormalizedDifferenceIntegrand n mu (L * y) := by rfl
    _ ≤ L * largeDirectVariableTelescopingReal L r (L * y) k0 := by
      simpa only [L, r] using hscaled
    _ = largeSmallVariableCellF1 L r y k0
        (largeDirectStrongQReal L r (L * y))
        (refinedRouteBDiskStar r (2 * Real.pi * L * y / r)) :=
      largeDirectVariableTelescoping_mul_scale_eq_smallCellF1 hL hr
    _ ≤ largeSmallVariableCellF1 L r y k0 q
        (refinedRouteBDiskStar r (2 * Real.pi * L * y / r)) :=
      largeSmallVariableCellF1_mono_q hr hy0 hk00 hD0 hq
    _ = largeSmallVariableCellF1
        (routeBSmoothingScale n (thirdAbsoluteMoment mu))
        (symmetrizationRatio mu) y k0 q
        (refinedRouteBDiskStar (symmetrizationRatio mu)
          (2 * Real.pi * routeBSmoothingScale n (thirdAbsoluteMoment mu) * y /
            symmetrizationRatio mu)) := by rfl

theorem largeVariableAlpha_sound
    {L : DyadicInterval} {LR : ℝ} (hL : L.Contains LR) :
    (largeVariableAlpha L).Contains
      (largeVariableAlphaReal LR) := by
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have hL2 := hL.sqr hL.ordered
  have hsub := hone.sub hL2
  simpa [largeVariableAlpha, largeVariableAlphaReal] using
    certifiedLargeMax_contains dyadicRouteBLargeAlpha_sound hsub

theorem certifiedLargeSmallVariableAlphaExp_sound
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hr2Lo : 0 < (DyadicInterval.sqr r).lo)
    (harg : 0 ≤ (DyadicInterval.mul (largeVariableAlpha L)
      (certifiedLargeSmallStrongQ L r y)).lo) :
    (certifiedLargeSmallVariableAlphaExp L r y).Contains
      (Real.exp (-largeVariableAlphaReal LR *
        certifiedLargeSmallCellStrongQReal rR yR
          (dyadicRouteBLargeSmallLowLine L y).lower)) := by
  have halpha := largeVariableAlpha_sound hL
  have hq := certifiedLargeSmallStrongQ_sound hL hr hy hr2Lo
  have hproduct := halpha.mul hq
  simpa [certifiedLargeSmallVariableAlphaExp] using
    dyadicExpNeg_sound hproduct harg

theorem certifiedLargeSmallVariableAlphaF1_sound
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hbox : CertifiedLargeSmallBoxAdmissible L r)
    (hcell : CertifiedLargeSmallVariableAlphaCellAdmissible L r y)
    (hy0 : 0 ≤ yR) (hy4 : yR ≤ 4) :
    (certifiedLargeSmallVariableAlphaF1 L r y).Contains
      (largeSmallVariableCellF1 LR rR yR
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
  have hP0 := dyadicRouteBLargeSmallP0_sound hL hy hcell.base.base.lowCotDenom
  have hwithP0 := hwithY.mul hP0
  have hD := dyadicPrawitzDstarFeasible_sound
    hr hv hbase.rPos hrStrict hr2 hv0 hyLower' hyUpper'
  have hExp := certifiedLargeSmallVariableAlphaExp_sound
    hL hr hy hbase.rSqPos hcell.alphaArgNonnegative
  have hresult := hwithP0.mul (hD.mul hExp)
  unfold certifiedLargeSmallVariableAlphaF1
    largeSmallVariableCellF1
  dsimp only
  convert hresult using 1 <;> ring

theorem lawNormalizedDifference_mul_scale_le_smallVariableF1_upper
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
    (hcell : CertifiedLargeSmallVariableAlphaCellAdmissible L r y)
    (hy0 : 0 ≤ yR) (hy4 : yR ≤ 4) :
    routeBSmoothingScale n (thirdAbsoluteMoment mu) *
        lawNormalizedDifferenceIntegrand n mu
          (routeBSmoothingScale n (thirdAbsoluteMoment mu) * yR) ≤
      (certifiedLargeSmallVariableAlphaF1 L r y).upper := by
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
  have hreal := lawNormalizedDifference_mul_scale_le_smallVariableCellF1
    mu hX hmean hsecond hn hr19 hy0
      (by simpa only [LR, k0] using hk0)
      (by simpa only [LR, rR, q] using hq)
  have hcontains := certifiedLargeSmallVariableAlphaF1_sound
    hL hr hy hbox hcell hy0 hy4
  exact hreal.trans <| by
    simpa only [LR, rR, q, k0] using hcontains.2

theorem lawNormalizedLargeSmallIntegrand_le_variable_cell_upper
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
    (hcell : CertifiedLargeSmallVariableAlphaCellAdmissible L r y)
    (hy0 : 0 ≤ yR) (hy4 : yR ≤ 4) :
    lawNormalizedLargeSmallIntegrand n mu yR ≤
      (certifiedLargeSmallVariableAlphaCellValue L r y).upper := by
  have hdiff :=
    lawNormalizedDifference_mul_scale_le_smallVariableF1_upper
      mu hX hmean hsecond hn hL hr hy hbox hcell hy0 hy4
  have hcorr := lawNormalizedCorrection_mul_scale_le_smallF3_upper
    mu hX hmean hsecond hn hL hr hy hbox hcell.base hy0 hy4
  have hhigh := lawNormalizedHigh_mul_scale_le_smallF2_upper
    mu hX hmean hsecond hn hL hr hy hbox hcell.base hy0 hy4
  have hsum := add_le_add (add_le_add hdiff hcorr) hhigh
  simpa [lawNormalizedLargeSmallIntegrand,
    lawNormalizedLowIntegrand,
    certifiedLargeSmallVariableAlphaCellValue, DyadicInterval.add,
    DyadicInterval.upper, Int.cast_add, add_div,
    mul_add, add_assoc] using hsum

end

end BerryEsseen
