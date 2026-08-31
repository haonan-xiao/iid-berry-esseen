import BerryEsseen.CharacteristicFunction.BreakpointNumerics
import BerryEsseen.CharacteristicFunction.OneStepDisk
/-!
# Exact reduction of the Route B disk candidates

This module proves formula (10): according to the position of the strip/circle transition
relative to the certified slope, the squared disk bound is controlled by two of its three
algebraic candidates.  These are the branch semantics required by the exact `Dbound` checker.
-/

namespace BerryEsseen

noncomputable section

def routeBDiskV0 (d a epsilon : ℝ) : ℝ :=
  epsilon ^ 2 + d ^ 2 - a ^ 2

def routeBDiskVa (d a epsilon : ℝ) : ℝ :=
  d ^ 2 + epsilon ^ 2 - 2 * a * epsilon

def routeBDiskVk (kappa d a epsilon : ℝ) : ℝ :=
  (kappa - epsilon) ^ 2 + d ^ 2 - a ^ 2

lemma routeBKappa_le_routeBD0 : routeBKappa ≤ routeBD0 := by
  have hk := routeBKappa_lt_upper
  norm_num [routeBKappaUpper, routeBD0] at hk ⊢
  linarith

lemma routeBDiskScore_zero_eq_V0 {r epsilon : ℝ}
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
    routeBDiskScore (routeBBeta r) routeBD0 epsilon 0 =
      routeBDiskV0 routeBD0 (routeBTransition r) epsilon := by
  have htrans := routeBTransition_sq_eq hr1 hr2
  have hbetaLe : routeBBeta r ^ 2 ≤ routeBD0 ^ 2 := by
    nlinarith [sq_nonneg (routeBTransition r)]
  unfold routeBDiskScore routeBDiskV0
  rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
  rw [min_eq_left hbetaLe]
  nlinarith

lemma routeBDiskScore_transition_eq_Va {r epsilon : ℝ}
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
    routeBDiskScore (routeBBeta r) routeBD0 epsilon (routeBTransition r) =
      routeBDiskVa routeBD0 (routeBTransition r) epsilon := by
  have htrans := routeBTransition_sq_eq hr1 hr2
  have hbetaEq : routeBBeta r ^ 2 =
      routeBD0 ^ 2 - routeBTransition r ^ 2 := by linarith
  unfold routeBDiskScore routeBDiskVa
  rw [hbetaEq, min_self]
  ring

lemma routeBDiskScore_kappa_le_Va {r epsilon : ℝ}
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hepsilon : 0 ≤ epsilon)
    (haKappa : routeBTransition r ≤ routeBKappa) :
    routeBDiskScore (routeBBeta r) routeBD0 epsilon routeBKappa ≤
      routeBDiskVa routeBD0 (routeBTransition r) epsilon := by
  have htrans := routeBTransition_sq_eq hr1 hr2
  have hk0 : 0 ≤ routeBKappa := routeBKappa_pos.le
  have hkD : routeBKappa ≤ routeBD0 := routeBKappa_le_routeBD0
  have hcircle : routeBD0 ^ 2 - routeBKappa ^ 2 ≤ routeBBeta r ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haKappa)
      (add_nonneg (routeBTransition_nonneg hr1) hk0)]
  unfold routeBDiskScore routeBDiskVa
  rw [min_eq_right hcircle]
  nlinarith [mul_nonneg (sub_nonneg.mpr haKappa) hepsilon]

lemma routeBDiskScore_kappa_eq_Vk {r epsilon : ℝ}
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hKappaA : routeBKappa ≤ routeBTransition r) :
    routeBDiskScore (routeBBeta r) routeBD0 epsilon routeBKappa =
      routeBDiskVk routeBKappa routeBD0 (routeBTransition r) epsilon := by
  have htrans := routeBTransition_sq_eq hr1 hr2
  have hk0 : 0 ≤ routeBKappa := routeBKappa_pos.le
  have ha0 : 0 ≤ routeBTransition r := routeBTransition_nonneg hr1
  have hstrip : routeBBeta r ^ 2 ≤ routeBD0 ^ 2 - routeBKappa ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hKappaA) (add_nonneg hk0 ha0)]
  unfold routeBDiskScore routeBDiskVk
  rw [min_eq_left hstrip]
  nlinarith

theorem routeBDiskBoundSq_le_candidates_of_transition_le_kappa
    {rho r c : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (haKappa : routeBTransition r ≤ routeBKappa)
    (hepsilon : 0 ≤ routeBEpsilon rho c) :
    routeBDiskBoundSq routeBKappa rho r c ≤
      max
        (routeBDiskV0 routeBD0 (routeBTransition r) (routeBEpsilon rho c))
        (routeBDiskVa routeBD0 (routeBTransition r) (routeBEpsilon rho c)) := by
  have ha0 : 0 ≤ routeBTransition r := routeBTransition_nonneg hr1
  have hcondition : 0 ≤ routeBTransition r ∧ routeBTransition r ≤ routeBKappa :=
    ⟨ha0, haKappa⟩
  unfold routeBDiskBoundSq
  dsimp only
  rw [if_pos hcondition]
  apply max_le
  · rw [routeBDiskScore_zero_eq_V0 hr1 hr2]
    exact le_max_left _ _
  · apply max_le
    · exact (routeBDiskScore_kappa_le_Va hr1 hr2 hepsilon haKappa).trans
        (le_max_right _ _)
    · rw [routeBDiskScore_transition_eq_Va hr1 hr2]
      exact le_max_right _ _

theorem routeBDiskBoundSq_le_candidates_of_kappa_le_transition
    {rho r c : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hKappaA : routeBKappa ≤ routeBTransition r) :
    routeBDiskBoundSq routeBKappa rho r c ≤
      max
        (routeBDiskV0 routeBD0 (routeBTransition r) (routeBEpsilon rho c))
        (routeBDiskVk routeBKappa routeBD0 (routeBTransition r) (routeBEpsilon rho c)) := by
  have ha0 : 0 ≤ routeBTransition r := routeBTransition_nonneg hr1
  unfold routeBDiskBoundSq
  dsimp only
  by_cases heq : routeBTransition r = routeBKappa
  · have hcondition : 0 ≤ routeBTransition r ∧ routeBTransition r ≤ routeBKappa :=
      ⟨ha0, heq.le⟩
    rw [if_pos hcondition]
    apply max_le
    · rw [routeBDiskScore_zero_eq_V0 hr1 hr2]
      exact le_max_left _ _
    · apply max_le
      · rw [routeBDiskScore_kappa_eq_Vk hr1 hr2 hKappaA]
        exact le_max_right _ _
      · rw [routeBDiskScore_transition_eq_Va hr1 hr2]
        have hVaVk :
            routeBDiskVa routeBD0 (routeBTransition r) (routeBEpsilon rho c) =
              routeBDiskVk routeBKappa routeBD0 (routeBTransition r)
                (routeBEpsilon rho c) := by
          rw [heq]
          unfold routeBDiskVa routeBDiskVk
          ring
        rw [hVaVk]
        exact le_max_right _ _
  · have hnot : ¬(0 ≤ routeBTransition r ∧ routeBTransition r ≤ routeBKappa) := by
      rintro ⟨_, hle⟩
      exact heq (le_antisymm hle hKappaA)
    rw [if_neg hnot]
    apply max_le
    · rw [routeBDiskScore_zero_eq_V0 hr1 hr2]
      exact le_max_left _ _
    · apply max_le
      · rw [routeBDiskScore_kappa_eq_Vk hr1 hr2 hKappaA]
        exact le_max_right _ _
      · rw [routeBDiskScore_zero_eq_V0 hr1 hr2]
        exact le_max_left _ _

end

end BerryEsseen
