import BerryEsseen.Smoothing.PrawitzLargeNDisk
import BerryEsseen.Certificate.Dyadic.Dbound
/-!
# Verifier-matching dyadic large-`n` disk bound

This module implements and verifies the exact checker's `Dstar_bound`.  The
external C++ routine is used only to discover certificates; this Lean
implementation recomputes every interval and proves that its result contains
the analytic envelope `routeBDiskStar`.
-/

namespace BerryEsseen

open DyadicInterval

def dyadicDstarC (r v : DyadicInterval) : DyadicInterval :=
  DyadicInterval.div v r

def dyadicDstarY (r v : DyadicInterval) : DyadicInterval :=
  DyadicInterval.divPoint (DyadicInterval.sqr (dyadicDstarC r v)) 2

def dyadicDstarEpsilon (r v : DyadicInterval) : DyadicInterval :=
  let c := dyadicDstarC r v
  let y := dyadicDstarY r v
  DyadicInterval.mul (DyadicInterval.divPoint c 4) (hfunInterval y)

def dyadicDstarA (r : DyadicInterval) : DyadicInterval :=
  DyadicInterval.divPoint
    (DyadicInterval.sub r (DyadicInterval.point 1)) 6

def dyadicDstarBetaSq (a : DyadicInterval) : DyadicInterval :=
  DyadicInterval.sub (DyadicInterval.ofRat 1 36) (DyadicInterval.sqr a)

def dyadicDstarV0 (a epsilon : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add (DyadicInterval.sqr epsilon) (dyadicDstarBetaSq a)

def dyadicDstarVa (a epsilon : DyadicInterval) : DyadicInterval :=
  DyadicInterval.sub
    (DyadicInterval.add (DyadicInterval.ofRat 1 36)
      (DyadicInterval.sqr epsilon))
    (DyadicInterval.mulPoint 2 (DyadicInterval.mul a epsilon))

def dyadicDstarVk (a epsilon : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add
    (DyadicInterval.add (DyadicInterval.sqr checkerKappaUpper)
      (DyadicInterval.sqr epsilon))
    (DyadicInterval.sub (dyadicDstarBetaSq a)
      (DyadicInterval.mulPoint 2
        (DyadicInterval.mul checkerKappaLower epsilon)))

def dyadicDstarEndpointHi (a epsilon : DyadicInterval) : ℤ :=
  let V0 := dyadicDstarV0 a epsilon
  let Va := dyadicDstarVa a epsilon
  let Vk := dyadicDstarVk a epsilon
  if a.hi ≤ checkerKappaLower.lo then max V0.hi Va.hi
  else if checkerKappaUpper.hi ≤ a.lo then max V0.hi Vk.hi
  else max (max V0.hi Va.hi) Vk.hi

/-- The exact fixed-point implementation of `Dstar_bound`. -/
def dyadicPrawitzDstar (r v : DyadicInterval) : DyadicInterval :=
  let a := dyadicDstarA r
  let epsilon := dyadicDstarEpsilon r v
  let hi0 := dyadicDstarEndpointHi a (DyadicInterval.point 0)
  let hi1 := dyadicDstarEndpointHi a epsilon
  DyadicInterval.sqrt (dyadicUpperHull (max hi0 hi1))

noncomputable section

lemma dyadicDstarC_sound
    {r v : DyadicInterval} {rR vR : ℝ}
    (hr : r.Contains rR) (hv : v.Contains vR) (hrLo : 0 < r.lo) :
    (dyadicDstarC r v).Contains (vR / rR) := by
  have hdiv := hv.div hr hr.ordered hrLo
  simpa [dyadicDstarC] using hdiv

lemma dyadicDstarY_sound
    {r v : DyadicInterval} {rR vR : ℝ}
    (hr : r.Contains rR) (hv : v.Contains vR) (hrLo : 0 < r.lo) :
    (dyadicDstarY r v).Contains ((vR / rR) ^ 2 / 2) := by
  have hc := dyadicDstarC_sound hr hv hrLo
  have hc2 := hc.sqr hc.ordered
  have hy := dyadicContains_div_point hc2 2 (by norm_num)
  simpa [dyadicDstarY] using hy

lemma dyadicDstarEpsilon_sound
    {r v : DyadicInterval} {rR vR : ℝ}
    (hr : r.Contains rR) (hv : v.Contains vR) (hrLo : 0 < r.lo)
    (hy3 : (vR / rR) ^ 2 / 2 ≤ 3) :
    (dyadicDstarEpsilon r v).Contains (routeBEpsilon 1 (vR / rR)) := by
  have hc := dyadicDstarC_sound hr hv hrLo
  have hy := dyadicDstarY_sound hr hv hrLo
  have hc4 := dyadicContains_div_point hc 4 (by norm_num)
  have hH := hfunInterval_sound hy (by positivity) hy3
  have hresult := hc4.mul hH
  rw [routeBEpsilon_one_eq_c_mul_H]
  simpa [dyadicDstarEpsilon, div_eq_mul_inv] using hresult

lemma dyadicDstarA_sound
    {r : DyadicInterval} {rR : ℝ} (hr : r.Contains rR) :
    (dyadicDstarA r).Contains (routeBTransition rR) := by
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have hraw := dyadicContains_div_point (hr.sub hone) 6 (by norm_num)
  simpa [dyadicDstarA, routeBTransition] using hraw

lemma dyadicDstarBetaSq_sound
    {a : DyadicInterval} {aR : ℝ} (ha : a.Contains aR) :
    (dyadicDstarBetaSq a).Contains (routeBD0 ^ 2 - aR ^ 2) := by
  have hone36 :
      (DyadicInterval.ofRat 1 36).Contains ((1 : ℝ) / 36) := by
    simpa only [Int.cast_one, Int.cast_ofNat] using
      DyadicInterval.contains_ofRat 1 (b := 36) (by norm_num)
  have hresult := hone36.sub (ha.sqr ha.ordered)
  norm_num [routeBD0] at hresult ⊢
  exact hresult

lemma dyadicDstarV0_sound
    {a epsilon : DyadicInterval} {aR epsilonR : ℝ}
    (ha : a.Contains aR) (hepsilon : epsilon.Contains epsilonR) :
    (dyadicDstarV0 a epsilon).Contains
      (routeBDiskV0 routeBD0 aR epsilonR) := by
  have hresult := (hepsilon.sqr hepsilon.ordered).add
    (dyadicDstarBetaSq_sound ha)
  simp only [dyadicDstarV0]
  convert hresult using 1 <;> unfold routeBDiskV0 <;> ring

lemma dyadicDstarVa_sound
    {a epsilon : DyadicInterval} {aR epsilonR : ℝ}
    (ha : a.Contains aR) (hepsilon : epsilon.Contains epsilonR) :
    (dyadicDstarVa a epsilon).Contains
      (routeBDiskVa routeBD0 aR epsilonR) := by
  have hone36 :
      (DyadicInterval.ofRat 1 36).Contains ((1 : ℝ) / 36) := by
    simpa only [Int.cast_one, Int.cast_ofNat] using
      DyadicInterval.contains_ofRat 1 (b := 36) (by norm_num)
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hresult := (hone36.add (hepsilon.sqr hepsilon.ordered)).sub
    (htwo.mul (ha.mul hepsilon))
  have hresult' :
      (dyadicDstarVa a epsilon).Contains
        ((1 : ℝ) / 36 + epsilonR ^ 2 - 2 * (aR * epsilonR)) := by
    simpa only [dyadicDstarVa, DyadicInterval.mulPoint_eq_mul] using hresult
  convert hresult' using 1
  unfold routeBDiskVa
  norm_num [routeBD0]
  ring

lemma dyadicDstarVk_sound
    {a epsilon : DyadicInterval} {aR epsilonR : ℝ}
    (ha : a.Contains aR) (hepsilon : epsilon.Contains epsilonR) :
    (dyadicDstarVk a epsilon).Contains
      (routeBDiskVkUpper (6 * aR + 1) epsilonR) := by
  have hkU2 := checkerKappaUpper_contains.sqr
    checkerKappaUpper_contains.ordered
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hcross := htwo.mul (checkerKappaLower_contains.mul hepsilon)
  have hresult := (hkU2.add (hepsilon.sqr hepsilon.ordered)).add
    ((dyadicDstarBetaSq_sound ha).sub hcross)
  simp only [dyadicDstarVk, DyadicInterval.mulPoint_eq_mul]
  unfold routeBDiskVkUpper routeBTransition
  norm_num [routeBD0] at hresult ⊢
  convert hresult using 1 <;> ring

lemma dyadicDstarVk_sound_for_transition
    {a epsilon : DyadicInterval} {rR epsilonR : ℝ}
    (ha : a.Contains (routeBTransition rR))
    (hepsilon : epsilon.Contains epsilonR) :
    (dyadicDstarVk a epsilon).Contains
      (routeBDiskVkUpper rR epsilonR) := by
  have h := dyadicDstarVk_sound ha hepsilon
  convert h using 1
  unfold routeBTransition
  ring

/-- Soundness of one `epsilon` endpoint of `Dstar_bound`, including all
three interval branches around `a = kappa`. -/
theorem dyadicDstarEndpointSq_le_upper
    {a epsilon : DyadicInterval} {rR epsilonR : ℝ}
    (ha : a.Contains (routeBTransition rR))
    (hepsilon : epsilon.Contains epsilonR)
    (hr1 : 1 ≤ rR) (hr2 : rR ≤ 2) (hepsilon0 : 0 ≤ epsilonR) :
    routeBDiskBoundSqAtEpsilon routeBKappa rR epsilonR ≤
      ((dyadicDstarEndpointHi a epsilon : ℤ) : ℝ) /
        (dyadicScale : ℝ) := by
  let V0 := dyadicDstarV0 a epsilon
  let Va := dyadicDstarVa a epsilon
  let Vk := dyadicDstarVk a epsilon
  have hV0 : V0.Contains
      (routeBDiskV0 routeBD0 (routeBTransition rR) epsilonR) :=
    dyadicDstarV0_sound ha hepsilon
  have hVa : Va.Contains
      (routeBDiskVa routeBD0 (routeBTransition rR) epsilonR) :=
    dyadicDstarVa_sound ha hepsilon
  have hVk : Vk.Contains (routeBDiskVkUpper rR epsilonR) :=
    dyadicDstarVk_sound_for_transition ha hepsilon
  have hVkActual :
      routeBDiskVk routeBKappa routeBD0
          (routeBTransition rR) epsilonR ≤ Vk.upper :=
    (routeBDiskVk_le_upper hepsilon0).trans hVk.2
  by_cases hLow : a.hi ≤ checkerKappaLower.lo
  · have haUpperLe : a.upper ≤ checkerKappaLower.lower :=
      dyadic_upper_le_lower_of_hi_le_lo hLow
    have haKappa : routeBTransition rR ≤ routeBKappa := by
      calc
        routeBTransition rR ≤ a.upper := ha.2
        _ ≤ checkerKappaLower.lower := haUpperLe
        _ ≤ routeBKappaLower := checkerKappaLower_contains.1
        _ ≤ routeBKappa := routeBKappa_gt_lower.le
    have hSq :=
      routeBDiskBoundSqAtEpsilon_le_candidates_of_transition_le_kappa
        hr1 hr2 haKappa hepsilon0
    have hUpper :
        routeBDiskBoundSqAtEpsilon routeBKappa rR epsilonR ≤
          max V0.upper Va.upper := hSq.trans <| max_le
      (hV0.2.trans (le_max_left _ _))
      (hVa.2.trans (le_max_right _ _))
    rw [dyadic_max_upper_eq] at hUpper
    simpa [dyadicDstarEndpointHi, V0, Va, Vk, hLow] using hUpper
  · by_cases hHigh : checkerKappaUpper.hi ≤ a.lo
    · have hUpperLeA : checkerKappaUpper.upper ≤ a.lower :=
        dyadic_upper_le_lower_of_hi_le_lo hHigh
      have hKappaA : routeBKappa ≤ routeBTransition rR := by
        calc
          routeBKappa ≤ routeBKappaUpper := routeBKappa_lt_upper.le
          _ ≤ checkerKappaUpper.upper := checkerKappaUpper_contains.2
          _ ≤ a.lower := hUpperLeA
          _ ≤ routeBTransition rR := ha.1
      have hSq :=
        routeBDiskBoundSqAtEpsilon_le_candidates_of_kappa_le_transition
          (epsilon := epsilonR) hr1 hr2 hKappaA
      have hUpper :
          routeBDiskBoundSqAtEpsilon routeBKappa rR epsilonR ≤
            max V0.upper Vk.upper := hSq.trans <| max_le
        (hV0.2.trans (le_max_left _ _))
        (hVkActual.trans (le_max_right _ _))
      rw [dyadic_max_upper_eq] at hUpper
      simpa [dyadicDstarEndpointHi, V0, Va, Vk, hLow, hHigh] using hUpper
    · have hSq := routeBDiskBoundSqAtEpsilon_le_all_candidates
          hr1 hr2 hepsilon0
      have hUpper :
          routeBDiskBoundSqAtEpsilon routeBKappa rR epsilonR ≤
            max V0.upper (max Va.upper Vk.upper) := hSq.trans <| max_le
        (hV0.2.trans (le_max_left _ _))
        (max_le
          (hVa.2.trans ((le_max_left _ _).trans (le_max_right _ _)))
          (hVkActual.trans ((le_max_right _ _).trans (le_max_right _ _))))
      have hscale : (0 : ℝ) ≤ (dyadicScale : ℝ) := by
        exact_mod_cast dyadicScale_pos.le
      have hUpper' :
          routeBDiskBoundSqAtEpsilon routeBKappa rR epsilonR ≤
            ((max (max V0.hi Va.hi) Vk.hi : ℤ) : ℝ) /
              (dyadicScale : ℝ) := by
        simpa [DyadicInterval.upper, Int.cast_max,
          max_div_div_right hscale, max_assoc] using hUpper
      simpa [dyadicDstarEndpointHi, V0, Va, Vk, hLow, hHigh] using hUpper'

/-- The Lean implementation of `Dstar_bound` contains the analytic `D_*`
for every admissible large-`n` parameter. -/
theorem dyadicPrawitzDstar_sound
    {r v : DyadicInterval} {rR vR : ℝ}
    (hr : r.Contains rR) (hv : v.Contains vR) (hrLo : 0 < r.lo)
    (hr1 : 1 ≤ rR) (hr2 : rR ≤ 2) (hv0 : 0 ≤ vR)
    (hy3 : (vR / rR) ^ 2 / 2 ≤ 3) :
    (dyadicPrawitzDstar r v).Contains
      (routeBDiskStar rR (vR / rR)) := by
  let a := dyadicDstarA r
  let epsilon := dyadicDstarEpsilon r v
  let epsilon0 := DyadicInterval.point 0
  let hi0 := dyadicDstarEndpointHi a epsilon0
  let hi1 := dyadicDstarEndpointHi a epsilon
  let S0 := routeBDiskBoundSqAtEpsilon routeBKappa rR 0
  let S1 := routeBDiskBoundSqAtEpsilon routeBKappa rR
    (routeBEpsilon 1 (vR / rR))
  let S := max S0 S1
  have hrPos : 0 < rR := zero_lt_one.trans_le hr1
  have hc0 : 0 ≤ vR / rR := div_nonneg hv0 hrPos.le
  have ha : a.Contains (routeBTransition rR) := dyadicDstarA_sound hr
  have hepsilon : epsilon.Contains (routeBEpsilon 1 (vR / rR)) :=
    dyadicDstarEpsilon_sound hr hv hrLo hy3
  have hepsilon0 : epsilon0.Contains (0 : ℝ) := by
    simpa [epsilon0] using DyadicInterval.contains_point (0 : ℤ)
  have hrealEpsilon0 : 0 ≤ routeBEpsilon 1 (vR / rR) :=
    routeBEpsilon_nonneg (by norm_num) hc0
  have hS0 : S0 ≤ (hi0 : ℝ) / (dyadicScale : ℝ) := by
    simpa only [S0, hi0, epsilon0] using
      dyadicDstarEndpointSq_le_upper ha hepsilon0 hr1 hr2 (by norm_num)
  have hS1 : S1 ≤ (hi1 : ℝ) / (dyadicScale : ℝ) := by
    simpa only [S1, hi1] using
      dyadicDstarEndpointSq_le_upper
        ha hepsilon hr1 hr2 hrealEpsilon0
  have hscale : (0 : ℝ) ≤ (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos.le
  have hS : S ≤ ((max hi0 hi1 : ℤ) : ℝ) / (dyadicScale : ℝ) := by
    have hmax : S ≤
        max ((hi0 : ℝ) / (dyadicScale : ℝ))
          ((hi1 : ℝ) / (dyadicScale : ℝ)) := by
      dsimp only [S]
      exact max_le
        (hS0.trans (le_max_left _ _))
        (hS1.trans (le_max_right _ _))
    simpa [Int.cast_max, max_div_div_right hscale] using hmax
  have hSNonneg : 0 ≤ S := by
    dsimp only [S, S0, S1]
    exact (routeBDiskBoundSqAtEpsilon_nonneg routeBKappa rR 0).trans
      (le_max_left _ _)
  have hHull := dyadicUpperHull_contains hSNonneg hS
  have hSqrt := hHull.sqrt hHull.ordered (by
    simp [dyadicUpperHull])
  simpa [dyadicPrawitzDstar, routeBDiskStar, routeBDiskStarSq,
    a, epsilon, epsilon0, hi0, hi1, S0, S1, S] using hSqrt

theorem routeBDiskStar_le_dyadicPrawitzDstar_upper
    {r v : DyadicInterval} {rR vR : ℝ}
    (hr : r.Contains rR) (hv : v.Contains vR) (hrLo : 0 < r.lo)
    (hr1 : 1 ≤ rR) (hr2 : rR ≤ 2) (hv0 : 0 ≤ vR)
    (hy3 : (vR / rR) ^ 2 / 2 ≤ 3) :
    routeBDiskStar rR (vR / rR) ≤ (dyadicPrawitzDstar r v).upper :=
  (dyadicPrawitzDstar_sound hr hv hrLo hr1 hr2 hv0 hy3).2

end

end BerryEsseen
