import BerryEsseen.Smoothing.PrawitzDiskCandidates
import BerryEsseen.Certificate.Dyadic.Elementary
/-!
# Correlation-preserving formulas for the Route B disk bound

This module proves the reparameterization used by `Dbound`, including
`epsilon_rho(v / r) = C * p`, the three formulas `V0`, `Va`, and `Vk`, and the
soundness of the checker's conservative mixed `KU`/`KL` endpoints.
-/

namespace BerryEsseen

noncomputable section

def routeBDboundW (rho z : ℝ) : ℝ := rho + z

def routeBDboundP (rho : ℝ) : ℝ := 1 / rho

def routeBDboundY (rho z v : ℝ) : ℝ :=
  v ^ 2 / (2 * routeBDboundW rho z ^ 2)

def routeBDboundC (rho z v : ℝ) : ℝ :=
  v / (4 * routeBDboundW rho z) * routeBH (routeBDboundY rho z v)

def routeBDboundR (rho z : ℝ) : ℝ :=
  routeBDboundW rho z / rho

def routeBDboundFrequency (rho z v : ℝ) : ℝ :=
  v / routeBDboundR rho z

lemma routeBH_nonneg (y : ℝ) : 0 ≤ routeBH y := by
  by_cases hy : y = 0
  · simp [routeBH, hy]
  · have hrem : 0 ≤ Real.exp (-y) - 1 + y := by
      linarith [Real.add_one_le_exp (-y)]
    unfold routeBH
    rw [if_neg hy]
    exact div_nonneg hrem (sq_nonneg y)

lemma routeBDboundR_eq_one_add {rho z : ℝ} (hrho : rho ≠ 0) :
    routeBDboundR rho z = 1 + z / rho := by
  unfold routeBDboundR routeBDboundW
  field_simp [hrho]

lemma routeBTransition_DboundR {rho z : ℝ} (hrho : rho ≠ 0) :
    routeBTransition (routeBDboundR rho z) =
      (routeBDboundW rho z * routeBDboundP rho - 1) / 6 := by
  unfold routeBTransition routeBDboundR routeBDboundW routeBDboundP
  field_simp [hrho]

theorem routeBEpsilon_Dbound_identity {rho z v : ℝ}
    (hrho : 0 < rho) (hz : 0 ≤ z) :
    routeBEpsilon rho (routeBDboundFrequency rho z v) =
      routeBDboundC rho z v * routeBDboundP rho := by
  let w := routeBDboundW rho z
  let r := routeBDboundR rho z
  let c := routeBDboundFrequency rho z v
  let y := routeBDboundY rho z v
  have hw : 0 < w := by dsimp only [w, routeBDboundW]; linarith
  have hr : 0 < r := by dsimp only [r, routeBDboundR]; positivity
  by_cases hv : v = 0
  · subst v
    simp [routeBDboundFrequency, routeBDboundC, routeBDboundY,
      routeBEpsilon, routeBDboundP]
  · have hc : c ≠ 0 := by dsimp only [c, routeBDboundFrequency]; positivity
    have hy : y ≠ 0 := by
      dsimp only [y, routeBDboundY]
      positivity
    have hyEq : c ^ 2 / (2 * rho ^ 2) = y := by
      change (v / ((rho + z) / rho)) ^ 2 / (2 * rho ^ 2) =
        v ^ 2 / (2 * (rho + z) ^ 2)
      field_simp [hrho.ne', hw.ne', hv]
    unfold routeBEpsilon
    rw [if_neg hc]
    unfold routeBDboundC routeBH
    rw [if_neg hy]
    rw [hyEq]
    dsimp only [routeBDboundY, routeBDboundFrequency, routeBDboundR,
      routeBDboundW, routeBDboundP, w, r, c, y]
    field_simp [hrho.ne', hw.ne', hv]
    ring

def routeBDboundV0 (rho z v : ℝ) : ℝ :=
  let w := routeBDboundW rho z
  let p := routeBDboundP rho
  let C := routeBDboundC rho z v
  (C ^ 2 - w ^ 2 / 36) * p ^ 2 + (w / 18) * p

def routeBDboundVa (rho z v : ℝ) : ℝ :=
  let w := routeBDboundW rho z
  let p := routeBDboundP rho
  let C := routeBDboundC rho z v
  (1 : ℝ) / 36 + (C ^ 2 - C * w / 3) * p ^ 2 + (C / 3) * p

def routeBDboundVk (rho z v : ℝ) : ℝ :=
  let w := routeBDboundW rho z
  let p := routeBDboundP rho
  let C := routeBDboundC rho z v
  routeBKappa ^ 2 + (C ^ 2 - w ^ 2 / 36) * p ^ 2 +
    (w / 18 - 2 * routeBKappa * C) * p

/-- The mixed-endpoint expression intentionally used by the checker. -/
def routeBDboundVkChecker (rho z v : ℝ) : ℝ :=
  let w := routeBDboundW rho z
  let p := routeBDboundP rho
  let C := routeBDboundC rho z v
  routeBKappaUpper ^ 2 + (C ^ 2 - w ^ 2 / 36) * p ^ 2 +
    (w / 18 - 2 * routeBKappaLower * C) * p

lemma routeBDboundC_nonneg {rho z v : ℝ}
    (hrho : 0 < rho) (hz0 : 0 ≤ z) (hv0 : 0 ≤ v) :
    0 ≤ routeBDboundC rho z v := by
  have hw : 0 < routeBDboundW rho z := by unfold routeBDboundW; linarith
  unfold routeBDboundC
  exact mul_nonneg (div_nonneg hv0 (by positivity)) (routeBH_nonneg _)

lemma routeBDboundVk_le_checker {rho z v : ℝ}
    (hrho : 0 < rho) (hz0 : 0 ≤ z) (hv0 : 0 ≤ v) :
    routeBDboundVk rho z v ≤ routeBDboundVkChecker rho z v := by
  let C := routeBDboundC rho z v
  let p := routeBDboundP rho
  have hC : 0 ≤ C := routeBDboundC_nonneg hrho hz0 hv0
  have hp : 0 ≤ p := by unfold p routeBDboundP; positivity
  have hk0 : 0 ≤ routeBKappa := routeBKappa_pos.le
  have hkU0 : 0 ≤ routeBKappaUpper := by norm_num [routeBKappaUpper]
  have hkUpper : routeBKappa ≤ routeBKappaUpper := routeBKappa_lt_upper.le
  have hkLower : routeBKappaLower ≤ routeBKappa := routeBKappa_gt_lower.le
  have hkSq : routeBKappa ^ 2 ≤ routeBKappaUpper ^ 2 :=
    pow_le_pow_left₀ hk0 hkUpper 2
  have hcross :
      (2 * routeBKappa * C) * p ≥ (2 * routeBKappaLower * C) * p := by
    gcongr
  unfold routeBDboundVk routeBDboundVkChecker
  dsimp only
  nlinarith

lemma routeBDiskV0_Dbound_identity {rho z v : ℝ} (hrho : rho ≠ 0) :
    routeBDiskV0 routeBD0 (routeBTransition (routeBDboundR rho z))
        (routeBDboundC rho z v * routeBDboundP rho) =
      routeBDboundV0 rho z v := by
  rw [routeBTransition_DboundR hrho]
  unfold routeBDiskV0 routeBD0 routeBDboundV0
  dsimp only
  ring

lemma routeBDiskVa_Dbound_identity {rho z v : ℝ} (hrho : rho ≠ 0) :
    routeBDiskVa routeBD0 (routeBTransition (routeBDboundR rho z))
        (routeBDboundC rho z v * routeBDboundP rho) =
      routeBDboundVa rho z v := by
  rw [routeBTransition_DboundR hrho]
  unfold routeBDiskVa routeBD0 routeBDboundVa
  dsimp only
  ring

lemma routeBDiskVk_Dbound_identity {rho z v : ℝ} (hrho : rho ≠ 0) :
    routeBDiskVk routeBKappa routeBD0 (routeBTransition (routeBDboundR rho z))
        (routeBDboundC rho z v * routeBDboundP rho) =
      routeBDboundVk rho z v := by
  rw [routeBTransition_DboundR hrho]
  unfold routeBDiskVk routeBD0 routeBDboundVk
  dsimp only
  ring

theorem routeBDiskBoundSq_le_Dbound_V0_Va {rho z v : ℝ}
    (hrho : 0 < rho) (hz0 : 0 ≤ z) (hz1 : z ≤ rho) (hv0 : 0 ≤ v)
    (haKappa : routeBTransition (routeBDboundR rho z) ≤ routeBKappa) :
    routeBDiskBoundSq routeBKappa rho (routeBDboundR rho z)
        (routeBDboundFrequency rho z v) ≤
      max (routeBDboundV0 rho z v) (routeBDboundVa rho z v) := by
  have hr1 : 1 ≤ routeBDboundR rho z := by
    rw [routeBDboundR_eq_one_add hrho.ne']
    have hzdiv : 0 ≤ z / rho := div_nonneg hz0 hrho.le
    linarith
  have hr2 : routeBDboundR rho z ≤ 2 := by
    rw [routeBDboundR_eq_one_add hrho.ne']
    have hzdiv : z / rho ≤ 1 := (div_le_one hrho).2 hz1
    linarith
  have hepsilon : 0 ≤ routeBEpsilon rho (routeBDboundFrequency rho z v) := by
    apply routeBEpsilon_nonneg hrho
    unfold routeBDboundFrequency
    exact div_nonneg hv0 (zero_le_one.trans hr1)
  have h := routeBDiskBoundSq_le_candidates_of_transition_le_kappa
    hr1 hr2 haKappa hepsilon
  rwa [routeBEpsilon_Dbound_identity hrho hz0,
    routeBDiskV0_Dbound_identity hrho.ne',
    routeBDiskVa_Dbound_identity hrho.ne'] at h

theorem routeBDiskBoundSq_le_Dbound_V0_Vk {rho z v : ℝ}
    (hrho : 0 < rho) (hz0 : 0 ≤ z) (hz1 : z ≤ rho)
    (hKappaA : routeBKappa ≤ routeBTransition (routeBDboundR rho z)) :
    routeBDiskBoundSq routeBKappa rho (routeBDboundR rho z)
        (routeBDboundFrequency rho z v) ≤
      max (routeBDboundV0 rho z v) (routeBDboundVk rho z v) := by
  have hr1 : 1 ≤ routeBDboundR rho z := by
    rw [routeBDboundR_eq_one_add hrho.ne']
    have hzdiv : 0 ≤ z / rho := div_nonneg hz0 hrho.le
    linarith
  have hr2 : routeBDboundR rho z ≤ 2 := by
    rw [routeBDboundR_eq_one_add hrho.ne']
    have hzdiv : z / rho ≤ 1 := (div_le_one hrho).2 hz1
    linarith
  have h := routeBDiskBoundSq_le_candidates_of_kappa_le_transition
    (rho := rho) (c := routeBDboundFrequency rho z v) hr1 hr2 hKappaA
  rwa [routeBEpsilon_Dbound_identity hrho hz0,
    routeBDiskV0_Dbound_identity hrho.ne',
    routeBDiskVk_Dbound_identity hrho.ne'] at h

theorem routeBDiskBoundSq_le_Dbound_candidates {rho z v : ℝ}
    (hrho : 0 < rho) (hz0 : 0 ≤ z) (hz1 : z ≤ rho) (hv0 : 0 ≤ v) :
    routeBDiskBoundSq routeBKappa rho (routeBDboundR rho z)
        (routeBDboundFrequency rho z v) ≤
      if routeBTransition (routeBDboundR rho z) ≤ routeBKappa then
        max (routeBDboundV0 rho z v) (routeBDboundVa rho z v)
      else
        max (routeBDboundV0 rho z v) (routeBDboundVk rho z v) := by
  have hr1 : 1 ≤ routeBDboundR rho z := by
    rw [routeBDboundR_eq_one_add hrho.ne']
    have hzdiv : 0 ≤ z / rho := div_nonneg hz0 hrho.le
    linarith
  have hr2 : routeBDboundR rho z ≤ 2 := by
    rw [routeBDboundR_eq_one_add hrho.ne']
    have hzdiv : z / rho ≤ 1 := (div_le_one hrho).2 hz1
    linarith
  have hepsilon : 0 ≤ routeBEpsilon rho (routeBDboundFrequency rho z v) := by
    apply routeBEpsilon_nonneg hrho
    unfold routeBDboundFrequency
    exact div_nonneg hv0 (zero_le_one.trans hr1)
  split_ifs with ha
  · have h := routeBDiskBoundSq_le_candidates_of_transition_le_kappa
      hr1 hr2 ha hepsilon
    rwa [routeBEpsilon_Dbound_identity hrho hz0,
      routeBDiskV0_Dbound_identity hrho.ne',
      routeBDiskVa_Dbound_identity hrho.ne'] at h
  · have hKappaA : routeBKappa ≤ routeBTransition (routeBDboundR rho z) :=
      le_of_not_ge ha
    have h := routeBDiskBoundSq_le_candidates_of_kappa_le_transition
      (rho := rho) (c := routeBDboundFrequency rho z v) hr1 hr2 hKappaA
    rwa [routeBEpsilon_Dbound_identity hrho hz0,
      routeBDiskV0_Dbound_identity hrho.ne',
      routeBDiskVk_Dbound_identity hrho.ne'] at h

theorem routeBDiskBoundSq_le_Dbound_all_candidates {rho z v : ℝ}
    (hrho : 0 < rho) (hz0 : 0 ≤ z) (hz1 : z ≤ rho) (hv0 : 0 ≤ v) :
    routeBDiskBoundSq routeBKappa rho (routeBDboundR rho z)
        (routeBDboundFrequency rho z v) ≤
      max (routeBDboundV0 rho z v)
        (max (routeBDboundVa rho z v) (routeBDboundVkChecker rho z v)) := by
  have hbase := routeBDiskBoundSq_le_Dbound_candidates hrho hz0 hz1 hv0
  by_cases ha : routeBTransition (routeBDboundR rho z) ≤ routeBKappa
  · rw [if_pos ha] at hbase
    exact hbase.trans (max_le
      (le_max_left _ _)
      ((le_max_left _ _).trans (le_max_right _ _)))
  · rw [if_neg ha] at hbase
    apply hbase.trans
    apply max_le
    · exact le_max_left _ _
    · exact (routeBDboundVk_le_checker hrho hz0 hv0).trans
        ((le_max_right _ _).trans (le_max_right _ _))

end

end BerryEsseen
