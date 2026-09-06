import BerryEsseen.DyadicPrawitzLargeNDisk

/-!
# Characteristic Functions / Gaussian Correction
-/

namespace BerryEsseen

noncomputable section

open DyadicInterval

/-- The Route B offset is antitone in the moment parameter `rho`. -/
theorem routeBEpsilon_antitone_rho
    {rho₁ rho₂ c : ℝ} (hrho₁ : 0 < rho₁) (hrhos : rho₁ ≤ rho₂)
    (hc : 0 ≤ c) :
    routeBEpsilon rho₂ c ≤ routeBEpsilon rho₁ c := by
  by_cases hcZero : c = 0
  · simp [routeBEpsilon, hcZero]
  · have hcPos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcZero)
    have hrho₂ : 0 < rho₂ := hrho₁.trans_le hrhos
    let x : ℝ := c ^ 2 / (2 * rho₂ ^ 2)
    let y : ℝ := c ^ 2 / (2 * rho₁ ^ 2)
    have hx : 0 < x := by
      dsimp only [x]
      positivity
    have hxy : x ≤ y := by
      dsimp only [x, y]
      have hrhoSq : rho₁ ^ 2 ≤ rho₂ ^ 2 := by nlinarith
      have hcSq : 0 ≤ c ^ 2 := sq_nonneg c
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * rho₂ ^ 2)
        (by positivity : (0 : ℝ) < 2 * rho₁ ^ 2)).2
      nlinarith
    have hquotient :
        routeBEpsilonQuotient x ≤ routeBEpsilonQuotient y :=
      routeBEpsilonQuotient_mono hx hxy
    have hprefactor : 0 ≤ 1 / (2 * c) := by positivity
    rw [routeBEpsilon_eq_quotient hrho₂ hcPos,
      routeBEpsilon_eq_quotient hrho₁ hcPos]
    simpa only [x, y] using
      mul_le_mul_of_nonneg_left hquotient hprefactor

/-- General `H` representation of the offset, used by the new exact checker. -/
lemma routeBEpsilon_eq_c_mul_H
    {rho c : ℝ} (hrho : rho ≠ 0) :
    routeBEpsilon rho c =
      c / (4 * rho ^ 2) * routeBH (c ^ 2 / (2 * rho ^ 2)) := by
  by_cases hc : c = 0
  · simp [routeBEpsilon, routeBH, hc]
  · have hy : c ^ 2 / (2 * rho ^ 2) ≠ 0 := by
      positivity
    unfold routeBEpsilon routeBH
    rw [if_neg hc, if_neg hy]
    field_simp [hc, hrho]
    ring

/-- Checker-facing formula at `rho=1/(r-1)`. -/
lemma routeBEpsilon_at_feasible_upper
    {r c : ℝ} (hr : 1 < r) :
    routeBEpsilon (1 / (r - 1)) c =
      c * (r - 1) ^ 2 / 4 *
        routeBH ((c * (r - 1)) ^ 2 / 2) := by
  have hrm : r - 1 ≠ 0 := sub_ne_zero.mpr hr.ne'
  rw [routeBEpsilon_eq_c_mul_H (one_div_ne_zero hrm)]
  field_simp [hrm]

/-- Squared distance from a fixed point is maximized at an endpoint of any
closed interval; unlike the the baseline bound version, the left endpoint need not be 0. -/
lemma sq_sub_le_interval_endpoints
    {lower epsilon upper x : ℝ}
    (hlower : lower ≤ epsilon) (hupper : epsilon ≤ upper) :
    (x - epsilon) ^ 2 ≤
      max ((x - lower) ^ 2) ((x - upper) ^ 2) := by
  by_cases he : epsilon ≤ x
  · have hfactor : 0 ≤ (epsilon - lower) * (2 * x - epsilon - lower) :=
      mul_nonneg (sub_nonneg.mpr hlower) (by linarith)
    exact (show (x - epsilon) ^ 2 ≤ (x - lower) ^ 2 by nlinarith).trans
      (le_max_left _ _)
  · have hxe : x ≤ epsilon := le_of_not_ge he
    have hfactor : 0 ≤ (upper - epsilon) * (upper + epsilon - 2 * x) :=
      mul_nonneg (sub_nonneg.mpr hupper) (by linarith)
    exact (show (x - epsilon) ^ 2 ≤ (x - upper) ^ 2 by nlinarith).trans
      (le_max_right _ _)

lemma refinedRouteBDiskScore_le_epsilon_endpoints
    {beta d lower epsilon upper x : ℝ}
    (hlower : lower ≤ epsilon) (hupper : epsilon ≤ upper) :
    routeBDiskScore beta d epsilon x ≤
      max (routeBDiskScore beta d lower x)
        (routeBDiskScore beta d upper x) := by
  have hsq := sq_sub_le_interval_endpoints
    (x := x) hlower hupper
  unfold routeBDiskScore
  let m := min (beta ^ 2) (d ^ 2 - x ^ 2)
  calc
    (x - epsilon) ^ 2 + m ≤
        max ((x - lower) ^ 2) ((x - upper) ^ 2) + m :=
      by simpa [add_comm] using add_le_add_right hsq m
    _ = max ((x - lower) ^ 2 + m) ((x - upper) ^ 2 + m) := by
      rw [max_add_add_right]

/-- The finite disk maximum is convex in its offset, so it is bounded by the
larger value at the two feasible offset endpoints. -/
theorem refinedRouteBDiskBoundSqAtEpsilon_le_endpoints
    {kappa r lower epsilon upper : ℝ}
    (hlower : lower ≤ epsilon) (hupper : epsilon ≤ upper) :
    routeBDiskBoundSqAtEpsilon kappa r epsilon ≤
      max (routeBDiskBoundSqAtEpsilon kappa r lower)
        (routeBDiskBoundSqAtEpsilon kappa r upper) := by
  have hcandidate (x : ℝ)
      (hleft : routeBDiskScore (routeBBeta r) routeBD0 lower x ≤
        routeBDiskBoundSqAtEpsilon kappa r lower)
      (hright : routeBDiskScore (routeBBeta r) routeBD0 upper x ≤
        routeBDiskBoundSqAtEpsilon kappa r upper) :
      routeBDiskScore (routeBBeta r) routeBD0 epsilon x ≤
        max (routeBDiskBoundSqAtEpsilon kappa r lower)
          (routeBDiskBoundSqAtEpsilon kappa r upper) :=
    (refinedRouteBDiskScore_le_epsilon_endpoints hlower hupper).trans
      (max_le_max hleft hright)
  by_cases hcondition :
      0 ≤ routeBTransition r ∧ routeBTransition r ≤ kappa
  · simp only [routeBDiskBoundSqAtEpsilon, if_pos hcondition]
    refine max_le ?_ (max_le ?_ ?_)
    · simpa only [routeBDiskBoundSqAtEpsilon, if_pos hcondition] using
        hcandidate 0
          (routeBDiskScore_zero_le_boundSqAtEpsilon kappa r lower)
          (routeBDiskScore_zero_le_boundSqAtEpsilon kappa r upper)
    · simpa only [routeBDiskBoundSqAtEpsilon, if_pos hcondition] using
        hcandidate kappa
          (routeBDiskScore_kappa_le_boundSqAtEpsilon kappa r lower)
          (routeBDiskScore_kappa_le_boundSqAtEpsilon kappa r upper)
    · simpa only [routeBDiskBoundSqAtEpsilon, if_pos hcondition] using
        hcandidate (routeBTransition r)
          (routeBDiskScore_transition_le_boundSqAtEpsilon hcondition)
          (routeBDiskScore_transition_le_boundSqAtEpsilon hcondition)
  · simp only [routeBDiskBoundSqAtEpsilon, if_neg hcondition]
    refine max_le ?_ (max_le ?_ ?_)
    · simpa only [routeBDiskBoundSqAtEpsilon, if_neg hcondition] using
        hcandidate 0
          (routeBDiskScore_zero_le_boundSqAtEpsilon kappa r lower)
          (routeBDiskScore_zero_le_boundSqAtEpsilon kappa r upper)
    · simpa only [routeBDiskBoundSqAtEpsilon, if_neg hcondition] using
        hcandidate kappa
          (routeBDiskScore_kappa_le_boundSqAtEpsilon kappa r lower)
          (routeBDiskScore_kappa_le_boundSqAtEpsilon kappa r upper)
    · simpa only [routeBDiskBoundSqAtEpsilon, if_neg hcondition] using
        hcandidate 0
          (routeBDiskScore_zero_le_boundSqAtEpsilon kappa r lower)
          (routeBDiskScore_zero_le_boundSqAtEpsilon kappa r upper)

def refinedRouteBDiskStarSq (r c : ℝ) : ℝ :=
  max
    (routeBDiskBoundSqAtEpsilon routeBKappa r
      (routeBEpsilon (1 / (r - 1)) c))
    (routeBDiskBoundSqAtEpsilon routeBKappa r (routeBEpsilon 1 c))

def refinedRouteBDiskStar (r c : ℝ) : ℝ :=
  Real.sqrt (refinedRouteBDiskStarSq r c)

/-- Feasible two-endpoint replacement for the baseline bound's `[0,epsilon(1,c)]` disk. -/
theorem refinedRouteBDiskBound_le_diskStar
    {rho r c : ℝ} (hrho : 1 ≤ rho) (hr : 1 < r)
    (hfeasible : rho * (r - 1) ≤ 1) (hc : 0 ≤ c) :
    routeBDiskBound routeBKappa rho r c ≤
      refinedRouteBDiskStar r c := by
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hrmPos : 0 < r - 1 := sub_pos.mpr hr
  have hrhoUpper : rho ≤ 1 / (r - 1) := by
    exact (le_div_iff₀ hrmPos).2 (by simpa [mul_comm] using hfeasible)
  have hlower :
      routeBEpsilon (1 / (r - 1)) c ≤ routeBEpsilon rho c :=
    routeBEpsilon_antitone_rho hrhoPos hrhoUpper hc
  have hupper : routeBEpsilon rho c ≤ routeBEpsilon 1 c :=
    routeBEpsilon_le_one hrho hc
  have hsq := refinedRouteBDiskBoundSqAtEpsilon_le_endpoints
    (kappa := routeBKappa) (r := r) hlower hupper
  unfold routeBDiskBound refinedRouteBDiskStar refinedRouteBDiskStarSq
  rw [routeBDiskBoundSq_eq_atEpsilon]
  exact Real.sqrt_le_sqrt hsq

/-! ## Exact dyadic realization -/

def dyadicDstarFeasibleEpsilon
    (r v : DyadicInterval) : DyadicInterval :=
  let delta := DyadicInterval.sub r (DyadicInterval.point 1)
  let c := dyadicDstarC r v
  let cDelta := DyadicInterval.mul c delta
  let y := DyadicInterval.divPoint (DyadicInterval.sqr cDelta) 2
  let prefactor := DyadicInterval.divPoint
    (DyadicInterval.mul c (DyadicInterval.sqr delta)) 4
  DyadicInterval.mul prefactor (hfunInterval y)

def dyadicPrawitzDstarFeasible
    (r v : DyadicInterval) : DyadicInterval :=
  let a := dyadicDstarA r
  let epsilonLower := dyadicDstarFeasibleEpsilon r v
  let epsilonUpper := dyadicDstarEpsilon r v
  let hiLower := dyadicDstarEndpointHi a epsilonLower
  let hiUpper := dyadicDstarEndpointHi a epsilonUpper
  DyadicInterval.sqrt (dyadicUpperHull (max hiLower hiUpper))

lemma dyadicDstarFeasibleEpsilon_sound
    {r v : DyadicInterval} {rR vR : ℝ}
    (hr : r.Contains rR) (hv : v.Contains vR) (hrLo : 0 < r.lo)
    (hr1 : 1 < rR)
    (hy3 : ((vR / rR) * (rR - 1)) ^ 2 / 2 ≤ 3) :
    (dyadicDstarFeasibleEpsilon r v).Contains
      (routeBEpsilon (1 / (rR - 1)) (vR / rR)) := by
  let delta := DyadicInterval.sub r (DyadicInterval.point 1)
  let c := dyadicDstarC r v
  let cDelta := DyadicInterval.mul c delta
  let y := DyadicInterval.divPoint (DyadicInterval.sqr cDelta) 2
  let prefactor := DyadicInterval.divPoint
    (DyadicInterval.mul c (DyadicInterval.sqr delta)) 4
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have hdelta : delta.Contains (rR - 1) := by
    simpa only [delta] using hr.sub hone
  have hc : c.Contains (vR / rR) := by
    simpa only [c] using dyadicDstarC_sound hr hv hrLo
  have hcDelta : cDelta.Contains ((vR / rR) * (rR - 1)) := by
    simpa only [cDelta] using hc.mul hdelta
  have hy : y.Contains (((vR / rR) * (rR - 1)) ^ 2 / 2) := by
    have hsquared := hcDelta.sqr hcDelta.ordered
    simpa only [y, DyadicInterval.divPoint_eq_div] using
      dyadicContains_div_point hsquared 2 (by norm_num)
  have hprefactor :
      prefactor.Contains ((vR / rR) * (rR - 1) ^ 2 / 4) := by
    have hdeltaSq := hdelta.sqr hdelta.ordered
    have hproduct := hc.mul hdeltaSq
    simpa only [prefactor, DyadicInterval.divPoint_eq_div] using
      dyadicContains_div_point hproduct 4 (by norm_num)
  have hH := hfunInterval_sound hy (by positivity) hy3
  have hresult := hprefactor.mul hH
  rw [routeBEpsilon_at_feasible_upper hr1]
  simpa only [dyadicDstarFeasibleEpsilon, delta, c, cDelta, y,
    prefactor] using hresult

theorem dyadicPrawitzDstarFeasible_sound
    {r v : DyadicInterval} {rR vR : ℝ}
    (hr : r.Contains rR) (hv : v.Contains vR) (hrLo : 0 < r.lo)
    (hr1 : 1 < rR) (hr2 : rR ≤ 2) (hv0 : 0 ≤ vR)
    (hy3 : ((vR / rR) * (rR - 1)) ^ 2 / 2 ≤ 3)
    (hyUpper3 : (vR / rR) ^ 2 / 2 ≤ 3) :
    (dyadicPrawitzDstarFeasible r v).Contains
      (refinedRouteBDiskStar rR (vR / rR)) := by
  let a := dyadicDstarA r
  let epsilonLower := dyadicDstarFeasibleEpsilon r v
  let epsilonUpper := dyadicDstarEpsilon r v
  let hiLower := dyadicDstarEndpointHi a epsilonLower
  let hiUpper := dyadicDstarEndpointHi a epsilonUpper
  let SLower := routeBDiskBoundSqAtEpsilon routeBKappa rR
    (routeBEpsilon (1 / (rR - 1)) (vR / rR))
  let SUpper := routeBDiskBoundSqAtEpsilon routeBKappa rR
    (routeBEpsilon 1 (vR / rR))
  let S := max SLower SUpper
  have hrPos : 0 < rR := zero_lt_one.trans hr1
  have hc0 : 0 ≤ vR / rR := div_nonneg hv0 hrPos.le
  have ha : a.Contains (routeBTransition rR) := dyadicDstarA_sound hr
  have hepsilonLower : epsilonLower.Contains
      (routeBEpsilon (1 / (rR - 1)) (vR / rR)) := by
    simpa only [epsilonLower] using
      dyadicDstarFeasibleEpsilon_sound hr hv hrLo hr1 hy3
  have hepsilonUpper : epsilonUpper.Contains
      (routeBEpsilon 1 (vR / rR)) := by
    simpa only [epsilonUpper] using
      dyadicDstarEpsilon_sound hr hv hrLo hyUpper3
  have hrhoUpperPos : 0 < 1 / (rR - 1) :=
    one_div_pos.mpr (sub_pos.mpr hr1)
  have hepsilonLower0 :
      0 ≤ routeBEpsilon (1 / (rR - 1)) (vR / rR) :=
    routeBEpsilon_nonneg hrhoUpperPos hc0
  have hepsilonUpper0 : 0 ≤ routeBEpsilon 1 (vR / rR) :=
    routeBEpsilon_nonneg (by norm_num) hc0
  have hSLower : SLower ≤ (hiLower : ℝ) / (dyadicScale : ℝ) := by
    simpa only [SLower, hiLower] using
      dyadicDstarEndpointSq_le_upper
        ha hepsilonLower hr1.le hr2 hepsilonLower0
  have hSUpper : SUpper ≤ (hiUpper : ℝ) / (dyadicScale : ℝ) := by
    simpa only [SUpper, hiUpper] using
      dyadicDstarEndpointSq_le_upper
        ha hepsilonUpper hr1.le hr2 hepsilonUpper0
  have hscale : (0 : ℝ) ≤ (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos.le
  have hS : S ≤ ((max hiLower hiUpper : ℤ) : ℝ) /
      (dyadicScale : ℝ) := by
    have hmax : S ≤
        max ((hiLower : ℝ) / (dyadicScale : ℝ))
          ((hiUpper : ℝ) / (dyadicScale : ℝ)) := by
      dsimp only [S]
      exact max_le
        (hSLower.trans (le_max_left _ _))
        (hSUpper.trans (le_max_right _ _))
    simpa [Int.cast_max, max_div_div_right hscale] using hmax
  have hSNonneg : 0 ≤ S := by
    dsimp only [S, SLower, SUpper]
    exact (routeBDiskBoundSqAtEpsilon_nonneg routeBKappa rR
      (routeBEpsilon (1 / (rR - 1)) (vR / rR))).trans
        (le_max_left _ _)
  have hHull := dyadicUpperHull_contains hSNonneg hS
  have hSqrt := hHull.sqrt hHull.ordered (by
    simp [dyadicUpperHull])
  simpa [dyadicPrawitzDstarFeasible, refinedRouteBDiskStar,
    refinedRouteBDiskStarSq, a, epsilonLower, epsilonUpper, hiLower, hiUpper,
    SLower, SUpper, S] using hSqrt

theorem routeBDiskStar_le_dyadic_upper
    {r v : DyadicInterval} {rR vR : ℝ}
    (hr : r.Contains rR) (hv : v.Contains vR) (hrLo : 0 < r.lo)
    (hr1 : 1 < rR) (hr2 : rR ≤ 2) (hv0 : 0 ≤ vR)
    (hy3 : ((vR / rR) * (rR - 1)) ^ 2 / 2 ≤ 3)
    (hyUpper3 : (vR / rR) ^ 2 / 2 ≤ 3) :
    refinedRouteBDiskStar rR (vR / rR) ≤
      (dyadicPrawitzDstarFeasible r v).upper :=
  (dyadicPrawitzDstarFeasible_sound hr hv hrLo hr1 hr2 hv0
    hy3 hyUpper3).2

end

end BerryEsseen
