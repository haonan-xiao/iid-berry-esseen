import BerryEsseen.Smoothing.PrawitzLargeN
/-!
# Uniform large-`n` Route B disk bound

This module formalizes equations (11)--(11a) from the numerical-lemma
supplement.  It proves that the one-step disk radius for every `rho ≥ 1` is
controlled by the two offset endpoints `epsilon = 0` and
`epsilon = routeBEpsilon 1 c`.  This is the analytic justification for the
checker-facing quantity `Dstar_bound`.
-/

open Set

namespace BerryEsseen

noncomputable section

/-- The scalar quotient whose monotonicity controls `routeBEpsilon` as `rho`
varies.  Only positive arguments are used below. -/
def routeBEpsilonQuotient (y : ℝ) : ℝ :=
  (Real.exp (-y) - 1 + y) / y

lemma hasDerivAt_routeBEpsilonQuotient {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt routeBEpsilonQuotient
      ((1 - (1 + y) * Real.exp (-y)) / y ^ 2) y := by
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x))
      (-Real.exp (-y)) y := by
    convert (Real.hasDerivAt_exp (-y)).comp y ((hasDerivAt_id y).neg) using 1
    ring
  have hnum : HasDerivAt (fun x : ℝ => Real.exp (-x) - 1 + x)
      (-Real.exp (-y) + 1) y := by
    convert (hexp.sub_const 1).add (hasDerivAt_id y) using 1
  unfold routeBEpsilonQuotient
  convert hnum.div (hasDerivAt_id y) hy using 1 <;>
    simp only [id_eq] <;> field_simp [hy] <;> ring

lemma routeBEpsilonQuotient_deriv_nonneg (y : ℝ) :
    0 ≤ (1 - (1 + y) * Real.exp (-y)) / y ^ 2 := by
  have hlinear : 1 + y ≤ Real.exp y := by
    simpa [add_comm] using Real.add_one_le_exp y
  have hmul :=
    mul_le_mul_of_nonneg_right hlinear (Real.exp_nonneg (-y))
  have hproduct : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hproduct] at hmul
  exact div_nonneg (sub_nonneg.mpr hmul) (sq_nonneg y)

lemma routeBEpsilonQuotient_mono
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    routeBEpsilonQuotient x ≤ routeBEpsilonQuotient y := by
  have hcontinuous : ContinuousOn routeBEpsilonQuotient (Icc x y) := by
    intro z hz
    exact (hasDerivAt_routeBEpsilonQuotient
      (ne_of_gt (hx.trans_le hz.1))).continuousAt.continuousWithinAt
  have hdifferentiable :
      DifferentiableOn ℝ routeBEpsilonQuotient (interior (Icc x y)) := by
    intro z hz
    rw [interior_Icc] at hz
    exact (hasDerivAt_routeBEpsilonQuotient
      (ne_of_gt (hx.trans hz.1))).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn routeBEpsilonQuotient (Icc x y) :=
    monotoneOn_of_deriv_nonneg (convex_Icc x y) hcontinuous
      hdifferentiable (by
        intro z hz
        rw [interior_Icc] at hz
        rw [(hasDerivAt_routeBEpsilonQuotient
          (ne_of_gt (hx.trans hz.1))).deriv]
        exact routeBEpsilonQuotient_deriv_nonneg z)
  exact hmono (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy

lemma routeBEpsilon_eq_quotient
    {rho c : ℝ} (hrho : 0 < rho) (hc : 0 < c) :
    routeBEpsilon rho c =
      1 / (2 * c) *
        routeBEpsilonQuotient (c ^ 2 / (2 * rho ^ 2)) := by
  have hrhoNe : rho ≠ 0 := hrho.ne'
  have hcNe : c ≠ 0 := hc.ne'
  unfold routeBEpsilon routeBEpsilonQuotient
  rw [if_neg hcNe]
  field_simp [hrhoNe, hcNe]

/-- The source supplement's monotonicity fact
`epsilon_rho(c) ≤ epsilon_1(c)` for `rho ≥ 1`. -/
theorem routeBEpsilon_le_one
    {rho c : ℝ} (hrho : 1 ≤ rho) (hc : 0 ≤ c) :
    routeBEpsilon rho c ≤ routeBEpsilon 1 c := by
  by_cases hcZero : c = 0
  · simp [routeBEpsilon, hcZero]
  · have hcPos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcZero)
    have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
    let x : ℝ := c ^ 2 / (2 * rho ^ 2)
    let y : ℝ := c ^ 2 / 2
    have hx : 0 < x := by
      dsimp only [x]
      positivity
    have hxy : x ≤ y := by
      dsimp only [x, y]
      have hrhoSq : 1 ≤ rho ^ 2 := by nlinarith
      have hcSq : 0 ≤ c ^ 2 := sq_nonneg c
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * rho ^ 2)
        (by norm_num : (0 : ℝ) < 2)).2
      nlinarith
    have hquotient :
        routeBEpsilonQuotient x ≤ routeBEpsilonQuotient y :=
      routeBEpsilonQuotient_mono hx hxy
    have hprefactor : 0 ≤ 1 / (2 * c) := by positivity
    rw [routeBEpsilon_eq_quotient hrhoPos hcPos,
      routeBEpsilon_eq_quotient (by norm_num) hcPos]
    simpa only [x, y, one_pow, mul_one] using
      mul_le_mul_of_nonneg_left hquotient hprefactor

/-- The `rho = 1` offset in the exact checker's `H` representation. -/
lemma routeBEpsilon_one_eq_c_mul_H (c : ℝ) :
    routeBEpsilon 1 c = c / 4 * routeBH (c ^ 2 / 2) := by
  by_cases hc : c = 0
  · simp [routeBEpsilon, routeBH, hc]
  · have hy : c ^ 2 / 2 ≠ 0 := by positivity
    unfold routeBEpsilon routeBH
    rw [if_neg hc, if_neg hy]
    field_simp [hc]
    ring

/-- The finite disk maximum with its Gaussian offset supplied explicitly. -/
def routeBDiskBoundSqAtEpsilon (kappa r epsilon : ℝ) : ℝ :=
  let beta := routeBBeta r
  let d := routeBD0
  let transition := routeBTransition r
  max (routeBDiskScore beta d epsilon 0)
    (max (routeBDiskScore beta d epsilon kappa)
      (if 0 ≤ transition ∧ transition ≤ kappa then
        routeBDiskScore beta d epsilon transition
      else routeBDiskScore beta d epsilon 0))

lemma routeBDiskBoundSq_eq_atEpsilon (kappa rho r c : ℝ) :
    routeBDiskBoundSq kappa rho r c =
      routeBDiskBoundSqAtEpsilon kappa r (routeBEpsilon rho c) := by
  rfl

lemma routeBDiskScore_le_epsilon_endpoints
    {beta d epsilon epsilonUpper x : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilonUpper : epsilon ≤ epsilonUpper)
    (hx : 0 ≤ x) :
    routeBDiskScore beta d epsilon x ≤
      max (routeBDiskScore beta d 0 x)
        (routeBDiskScore beta d epsilonUpper x) := by
  have hsq := sq_sub_le_max_endpoints hepsilon hepsilonUpper hx
  unfold routeBDiskScore
  let m := min (beta ^ 2) (d ^ 2 - x ^ 2)
  calc
    (x - epsilon) ^ 2 + m = (epsilon - x) ^ 2 + m := by ring
    _ ≤ max (((0 : ℝ) - x) ^ 2) ((epsilonUpper - x) ^ 2) + m :=
      by simpa [add_comm] using add_le_add_right hsq m
    _ = max ((x - 0) ^ 2 + m) ((x - epsilonUpper) ^ 2 + m) := by
      rw [max_add_add_right]
      congr 2 <;> ring

lemma routeBDiskScore_zero_le_boundSqAtEpsilon
    (kappa r epsilon : ℝ) :
    routeBDiskScore (routeBBeta r) routeBD0 epsilon 0 ≤
      routeBDiskBoundSqAtEpsilon kappa r epsilon := by
  unfold routeBDiskBoundSqAtEpsilon
  exact le_max_left _ _

lemma routeBDiskScore_kappa_le_boundSqAtEpsilon
    (kappa r epsilon : ℝ) :
    routeBDiskScore (routeBBeta r) routeBD0 epsilon kappa ≤
      routeBDiskBoundSqAtEpsilon kappa r epsilon := by
  unfold routeBDiskBoundSqAtEpsilon
  exact (le_max_left _ _).trans (le_max_right _ _)

lemma routeBDiskScore_transition_le_boundSqAtEpsilon
    {kappa r epsilon : ℝ}
    (htransition :
      0 ≤ routeBTransition r ∧ routeBTransition r ≤ kappa) :
    routeBDiskScore (routeBBeta r) routeBD0 epsilon
        (routeBTransition r) ≤
      routeBDiskBoundSqAtEpsilon kappa r epsilon := by
  unfold routeBDiskBoundSqAtEpsilon
  dsimp only
  rw [if_pos htransition]
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem routeBDiskBoundSqAtEpsilon_le_candidates_of_transition_le_kappa
    {r epsilon : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (haKappa : routeBTransition r ≤ routeBKappa)
    (hepsilon : 0 ≤ epsilon) :
    routeBDiskBoundSqAtEpsilon routeBKappa r epsilon ≤
      max (routeBDiskV0 routeBD0 (routeBTransition r) epsilon)
        (routeBDiskVa routeBD0 (routeBTransition r) epsilon) := by
  have ha0 : 0 ≤ routeBTransition r := routeBTransition_nonneg hr1
  have hcondition :
      0 ≤ routeBTransition r ∧ routeBTransition r ≤ routeBKappa :=
    ⟨ha0, haKappa⟩
  unfold routeBDiskBoundSqAtEpsilon
  dsimp only
  rw [if_pos hcondition]
  apply max_le
  · rw [routeBDiskScore_zero_eq_V0 hr1 hr2]
    exact le_max_left _ _
  · apply max_le
    · exact (routeBDiskScore_kappa_le_Va
        hr1 hr2 hepsilon haKappa).trans (le_max_right _ _)
    · rw [routeBDiskScore_transition_eq_Va hr1 hr2]
      exact le_max_right _ _

theorem routeBDiskBoundSqAtEpsilon_le_candidates_of_kappa_le_transition
    {r epsilon : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hKappaA : routeBKappa ≤ routeBTransition r) :
    routeBDiskBoundSqAtEpsilon routeBKappa r epsilon ≤
      max (routeBDiskV0 routeBD0 (routeBTransition r) epsilon)
        (routeBDiskVk routeBKappa routeBD0
          (routeBTransition r) epsilon) := by
  have ha0 : 0 ≤ routeBTransition r := routeBTransition_nonneg hr1
  unfold routeBDiskBoundSqAtEpsilon
  dsimp only
  by_cases heq : routeBTransition r = routeBKappa
  · have hcondition :
        0 ≤ routeBTransition r ∧ routeBTransition r ≤ routeBKappa :=
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
            routeBDiskVa routeBD0 (routeBTransition r) epsilon =
              routeBDiskVk routeBKappa routeBD0
                (routeBTransition r) epsilon := by
          rw [heq]
          unfold routeBDiskVa routeBDiskVk
          ring
        rw [hVaVk]
        exact le_max_right _ _
  · have hnot :
        ¬(0 ≤ routeBTransition r ∧ routeBTransition r ≤ routeBKappa) := by
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

theorem routeBDiskBoundSqAtEpsilon_le_all_candidates
    {r epsilon : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hepsilon : 0 ≤ epsilon) :
    routeBDiskBoundSqAtEpsilon routeBKappa r epsilon ≤
      max (routeBDiskV0 routeBD0 (routeBTransition r) epsilon)
        (max (routeBDiskVa routeBD0 (routeBTransition r) epsilon)
          (routeBDiskVk routeBKappa routeBD0
            (routeBTransition r) epsilon)) := by
  rcases le_total (routeBTransition r) routeBKappa with haKappa | hKappaA
  · exact (routeBDiskBoundSqAtEpsilon_le_candidates_of_transition_le_kappa
      hr1 hr2 haKappa hepsilon).trans (max_le
        (le_max_left _ _)
        ((le_max_left _ _).trans (le_max_right _ _)))
  · exact (routeBDiskBoundSqAtEpsilon_le_candidates_of_kappa_le_transition
      hr1 hr2 hKappaA).trans (max_le
        (le_max_left _ _)
        ((le_max_right _ _).trans (le_max_right _ _)))

/-- The conservative `kappa`-endpoint formula used by the exact checker. -/
def routeBDiskVkUpper (r epsilon : ℝ) : ℝ :=
  routeBKappaUpper ^ 2 + epsilon ^ 2 +
    (routeBD0 ^ 2 - routeBTransition r ^ 2) -
      2 * routeBKappaLower * epsilon

lemma routeBDiskVk_le_upper
    {r epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    routeBDiskVk routeBKappa routeBD0 (routeBTransition r) epsilon ≤
      routeBDiskVkUpper r epsilon := by
  have hk0 : 0 ≤ routeBKappa := routeBKappa_pos.le
  have hkUpper : routeBKappa ≤ routeBKappaUpper :=
    routeBKappa_lt_upper.le
  have hkLower : routeBKappaLower ≤ routeBKappa :=
    routeBKappa_gt_lower.le
  have hkSq : routeBKappa ^ 2 ≤ routeBKappaUpper ^ 2 :=
    pow_le_pow_left₀ hk0 hkUpper 2
  have hcross :
      2 * routeBKappaLower * epsilon ≤ 2 * routeBKappa * epsilon := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hkLower (by norm_num)) hepsilon
  unfold routeBDiskVk routeBDiskVkUpper
  nlinarith

/-- A maximum of the fixed-candidate convex quadratics in `epsilon` is bounded
by the larger endpoint value. -/
theorem routeBDiskBoundSqAtEpsilon_le_endpoints
    {kappa r epsilon epsilonUpper : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilonUpper : epsilon ≤ epsilonUpper)
    (hkappa : 0 ≤ kappa) (htransition : 0 ≤ routeBTransition r) :
    routeBDiskBoundSqAtEpsilon kappa r epsilon ≤
      max (routeBDiskBoundSqAtEpsilon kappa r 0)
        (routeBDiskBoundSqAtEpsilon kappa r epsilonUpper) := by
  have hcandidate (x : ℝ) (hx : 0 ≤ x)
      (hleft : routeBDiskScore (routeBBeta r) routeBD0 0 x ≤
        routeBDiskBoundSqAtEpsilon kappa r 0)
      (hright :
        routeBDiskScore (routeBBeta r) routeBD0 epsilonUpper x ≤
          routeBDiskBoundSqAtEpsilon kappa r epsilonUpper) :
      routeBDiskScore (routeBBeta r) routeBD0 epsilon x ≤
        max (routeBDiskBoundSqAtEpsilon kappa r 0)
          (routeBDiskBoundSqAtEpsilon kappa r epsilonUpper) := by
    exact (routeBDiskScore_le_epsilon_endpoints
      hepsilon hepsilonUpper hx).trans (max_le_max hleft hright)
  by_cases hcondition :
      0 ≤ routeBTransition r ∧ routeBTransition r ≤ kappa
  · simp only [routeBDiskBoundSqAtEpsilon, if_pos hcondition]
    refine max_le ?_ (max_le ?_ ?_)
    · simpa only [routeBDiskBoundSqAtEpsilon, if_pos hcondition] using
        hcandidate 0 (by norm_num)
          (routeBDiskScore_zero_le_boundSqAtEpsilon kappa r 0)
          (routeBDiskScore_zero_le_boundSqAtEpsilon
            kappa r epsilonUpper)
    · simpa only [routeBDiskBoundSqAtEpsilon, if_pos hcondition] using
        hcandidate kappa hkappa
          (routeBDiskScore_kappa_le_boundSqAtEpsilon kappa r 0)
          (routeBDiskScore_kappa_le_boundSqAtEpsilon
            kappa r epsilonUpper)
    · simpa only [routeBDiskBoundSqAtEpsilon, if_pos hcondition] using
        hcandidate (routeBTransition r) htransition
          (routeBDiskScore_transition_le_boundSqAtEpsilon hcondition)
          (routeBDiskScore_transition_le_boundSqAtEpsilon hcondition)
  · simp only [routeBDiskBoundSqAtEpsilon, if_neg hcondition]
    refine max_le ?_ (max_le ?_ ?_)
    · simpa only [routeBDiskBoundSqAtEpsilon, if_neg hcondition] using
        hcandidate 0 (by norm_num)
          (routeBDiskScore_zero_le_boundSqAtEpsilon kappa r 0)
          (routeBDiskScore_zero_le_boundSqAtEpsilon
            kappa r epsilonUpper)
    · simpa only [routeBDiskBoundSqAtEpsilon, if_neg hcondition] using
        hcandidate kappa hkappa
          (routeBDiskScore_kappa_le_boundSqAtEpsilon kappa r 0)
          (routeBDiskScore_kappa_le_boundSqAtEpsilon
            kappa r epsilonUpper)
    · simpa only [routeBDiskBoundSqAtEpsilon, if_neg hcondition] using
        hcandidate 0 (by norm_num)
          (routeBDiskScore_zero_le_boundSqAtEpsilon kappa r 0)
          (routeBDiskScore_zero_le_boundSqAtEpsilon
            kappa r epsilonUpper)

/-- The squared large-`n` disk envelope `D_*^2`. -/
def routeBDiskStarSq (r c : ℝ) : ℝ :=
  max (routeBDiskBoundSqAtEpsilon routeBKappa r 0)
    (routeBDiskBoundSqAtEpsilon routeBKappa r (routeBEpsilon 1 c))

/-- The large-`n` disk envelope `D_*`. -/
def routeBDiskStar (r c : ℝ) : ℝ :=
  Real.sqrt (routeBDiskStarSq r c)

lemma routeBDiskBoundSqAtEpsilon_nonneg (kappa r epsilon : ℝ) :
    0 ≤ routeBDiskBoundSqAtEpsilon kappa r epsilon := by
  exact (routeBDiskScore_zero_nonneg
    (routeBBeta r) routeBD0 epsilon).trans
      (routeBDiskScore_zero_le_boundSqAtEpsilon kappa r epsilon)

lemma routeBDiskStarSq_nonneg (r c : ℝ) :
    0 ≤ routeBDiskStarSq r c := by
  unfold routeBDiskStarSq
  exact (routeBDiskBoundSqAtEpsilon_nonneg routeBKappa r 0).trans
    (le_max_left _ _)

lemma routeBDiskStar_nonneg (r c : ℝ) :
    0 ≤ routeBDiskStar r c := Real.sqrt_nonneg _

/-- Equation (11a): for every `rho ≥ 1`, the one-step disk radius is no
larger than the two-endpoint envelope used by the large-`n` checker. -/
theorem routeBDiskBound_le_diskStar
    {rho r c : ℝ} (hrho : 1 ≤ rho) (hr : 1 ≤ r) (hc : 0 ≤ c) :
    routeBDiskBound routeBKappa rho r c ≤ routeBDiskStar r c := by
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho
  have hepsilon : 0 ≤ routeBEpsilon rho c :=
    routeBEpsilon_nonneg hrhoPos hc
  have hepsilonUpper : routeBEpsilon rho c ≤ routeBEpsilon 1 c :=
    routeBEpsilon_le_one hrho hc
  have hsq :
      routeBDiskBoundSqAtEpsilon routeBKappa r (routeBEpsilon rho c) ≤
        routeBDiskStarSq r c := by
    exact routeBDiskBoundSqAtEpsilon_le_endpoints
      hepsilon hepsilonUpper routeBKappa_pos.le (routeBTransition_nonneg hr)
  unfold routeBDiskBound routeBDiskStar routeBDiskStarSq
  rw [routeBDiskBoundSq_eq_atEpsilon]
  exact Real.sqrt_le_sqrt hsq

end

end BerryEsseen
