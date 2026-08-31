import BerryEsseen.CharacteristicFunction.ConvexMinorant
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Set

namespace BerryEsseen

noncomputable section

def routeBG (v : ℝ) : ℝ := Real.cos v - 1 + v ^ 2 / 2

def routeBF (v : ℝ) : ℝ :=
  3 * (1 - Real.cos v) - v * Real.sin v - v ^ 2 / 2

def routeBA (v : ℝ) : ℝ :=
  v ^ 2 * Real.cos v - 4 * v * Real.sin v + 6 * (1 - Real.cos v)

def routeBAPrime (v : ℝ) : ℝ :=
  -2 * v * Real.cos v + (2 - v ^ 2) * Real.sin v

def routeBMaxQuotient (v : ℝ) : ℝ := routeBG v / v ^ 3

def routeBPsiPrime (v : ℝ) : ℝ :=
  (v * Real.sin v - 2 * (1 - Real.cos v)) / v ^ 3

theorem hasDerivAt_routeBF (v : ℝ) :
    HasDerivAt routeBF
      (2 * Real.sin v - v * Real.cos v - v) v := by
  unfold routeBF
  convert (((hasDerivAt_const v 1).sub (Real.hasDerivAt_cos v)).const_mul 3).sub
    ((hasDerivAt_id v).mul (Real.hasDerivAt_sin v)) |>.sub
      ((hasDerivAt_pow 2 v).div_const 2) using 1 <;> simp only [id_eq] <;> ring

theorem routeBF_derivative_factor (v : ℝ) :
    2 * Real.sin v - v * Real.cos v - v =
      4 * Real.cos (v / 2) *
        (Real.sin (v / 2) - (v / 2) * Real.cos (v / 2)) := by
  rw [show v = 2 * (v / 2) by ring, Real.sin_two_mul, Real.cos_two_mul]
  ring

theorem hasDerivAt_routeBA (v : ℝ) :
    HasDerivAt routeBA (routeBAPrime v) v := by
  unfold routeBA routeBAPrime
  convert ((hasDerivAt_pow 2 v).mul (Real.hasDerivAt_cos v)).sub
    (((hasDerivAt_id v).mul (Real.hasDerivAt_sin v)).const_mul 4) |>.add
      (((hasDerivAt_const v 1).sub (Real.hasDerivAt_cos v)).const_mul 6) using 1
  · funext x
    simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  · simp only [id_eq]
    ring

theorem hasDerivAt_routeBAPrime (v : ℝ) :
    HasDerivAt routeBAPrime (-v ^ 2 * Real.cos v) v := by
  unfold routeBAPrime
  convert ((((hasDerivAt_id v).mul (Real.hasDerivAt_cos v)).const_mul (-2))).add
    (((hasDerivAt_const v 2).sub (hasDerivAt_pow 2 v)).mul
      (Real.hasDerivAt_sin v)) using 1
  · funext x
    simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  · simp only [id_eq, Pi.sub_apply]
    ring

theorem hasDerivAt_routeBMaxQuotient {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt routeBMaxQuotient (routeBF v / v ^ 4) v := by
  unfold routeBMaxQuotient routeBG routeBF
  have hnum : HasDerivAt (fun w : ℝ => Real.cos w - 1 + w ^ 2 / 2)
      (-Real.sin v + v) v := by
    convert ((Real.hasDerivAt_cos v).sub_const 1).add
      ((hasDerivAt_pow 2 v).div_const 2) using 1 <;> ring
  convert hnum.div (hasDerivAt_pow 3 v) (pow_ne_zero 3 hv) using 1
  field_simp [hv]
  ring

theorem hasDerivAt_routeBPsi {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt routeBPsi (routeBPsiPrime v) v := by
  unfold routeBPsi routeBPsiPrime
  have hnum : HasDerivAt (fun w : ℝ => 1 - Real.cos w) (Real.sin v) v := by
    convert (hasDerivAt_const v 1).sub (Real.hasDerivAt_cos v) using 1 <;> ring
  convert hnum.div (hasDerivAt_pow 2 v) (pow_ne_zero 2 hv) using 1
  field_simp [hv]
  ring

theorem hasDerivAt_routeBPsiPrime {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt routeBPsiPrime (routeBA v / v ^ 4) v := by
  unfold routeBPsiPrime routeBA
  have hnum : HasDerivAt
      (fun w : ℝ => w * Real.sin w - 2 * (1 - Real.cos w))
      (v * Real.cos v - Real.sin v) v := by
    convert ((hasDerivAt_id v).mul (Real.hasDerivAt_sin v)).sub
      (((hasDerivAt_const v 1).sub (Real.hasDerivAt_cos v)).const_mul 2) using 1 <;>
      simp only [id_eq] <;> ring
  convert hnum.div (hasDerivAt_pow 3 v) (pow_ne_zero 3 hv) using 1
  field_simp [hv]
  ring

theorem routeBF_pi_pos : 0 < routeBF Real.pi := by
  rw [routeBF]
  simp only [Real.cos_pi, Real.sin_pi]
  nlinarith [Real.pi_pos, Real.pi_lt_d2]

theorem routeBF_three_pi_div_two_neg :
    routeBF (3 * Real.pi / 2) < 0 := by
  rw [routeBF]
  have harg : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
  rw [harg, Real.cos_add, Real.sin_add]
  simp only [Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  nlinarith [Real.pi_gt_three]

theorem sin_sub_mul_cos_pos {z : ℝ} (hz0 : 0 < z) (hzpi : z < Real.pi) :
    0 < Real.sin z - z * Real.cos z := by
  by_cases hzhalf : z < Real.pi / 2
  · have hcos : 0 < Real.cos z :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hzhalf⟩
    have htan := Real.lt_tan hz0 hzhalf
    rw [Real.tan_eq_sin_div_cos] at htan
    exact sub_pos.2 ((lt_div_iff₀ hcos).mp htan)
  · have hhalf : Real.pi / 2 ≤ z := le_of_not_gt hzhalf
    have hcos : Real.cos z ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hhalf (by linarith [Real.pi_pos])
    have hsin : 0 < Real.sin z := Real.sin_pos_of_pos_of_lt_pi hz0 hzpi
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hz0.le hcos]

theorem routeBF_deriv_pos_of_mem_Ioo_zero_pi {v : ℝ}
    (hv : v ∈ Ioo 0 Real.pi) : 0 < deriv routeBF v := by
  rw [(hasDerivAt_routeBF v).deriv, routeBF_derivative_factor]
  have hcos : 0 < Real.cos (v / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hv.1], by linarith [hv.2]⟩
  have hvhalf : v / 2 < Real.pi / 2 := by linarith [hv.2]
  have hinner : 0 < Real.sin (v / 2) - (v / 2) * Real.cos (v / 2) :=
    sin_sub_mul_cos_pos (by linarith [hv.1])
      (hvhalf.trans (half_lt_self Real.pi_pos))
  positivity

theorem routeBF_deriv_neg_of_mem_Ioo_pi_two_pi {v : ℝ}
    (hv : v ∈ Ioo Real.pi (2 * Real.pi)) : deriv routeBF v < 0 := by
  rw [(hasDerivAt_routeBF v).deriv, routeBF_derivative_factor]
  have hcos : Real.cos (v / 2) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [hv.1])
      (by linarith [Real.pi_pos, hv.2])
  have hinner : 0 < Real.sin (v / 2) - (v / 2) * Real.cos (v / 2) :=
    sin_sub_mul_cos_pos (by linarith [Real.pi_pos, hv.1]) (by linarith [hv.2])
  nlinarith [mul_neg_of_neg_of_pos hcos hinner]

theorem routeBF_strictMonoOn_zero_pi :
    StrictMonoOn routeBF (Icc 0 Real.pi) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 Real.pi)
    (by unfold routeBF; fun_prop) ?_
  intro v hv
  rw [interior_Icc] at hv
  exact routeBF_deriv_pos_of_mem_Ioo_zero_pi hv

theorem routeBF_strictAntiOn_pi_two_pi :
    StrictAntiOn routeBF (Icc Real.pi (2 * Real.pi)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc Real.pi (2 * Real.pi))
    (by unfold routeBF; fun_prop) ?_
  intro v hv
  rw [interior_Icc] at hv
  exact routeBF_deriv_neg_of_mem_Ioo_pi_two_pi hv

theorem exists_routeBTheta :
    ∃ theta ∈ Ioo Real.pi (3 * Real.pi / 2), routeBF theta = 0 := by
  have horder : Real.pi ≤ 3 * Real.pi / 2 := by linarith [Real.pi_pos]
  have hzero : (0 : ℝ) ∈ Icc (routeBF (3 * Real.pi / 2)) (routeBF Real.pi) :=
    ⟨routeBF_three_pi_div_two_neg.le, routeBF_pi_pos.le⟩
  rcases (intermediate_value_Icc' horder (by unfold routeBF; fun_prop : ContinuousOn routeBF
      (Icc Real.pi (3 * Real.pi / 2)))) hzero with ⟨theta, htheta, hF⟩
  refine ⟨theta, ⟨?_, ?_⟩, hF⟩
  · exact htheta.1.lt_of_ne (fun heq => routeBF_pi_pos.ne' (heq ▸ hF))
  · exact htheta.2.lt_of_ne (fun heq => routeBF_three_pi_div_two_neg.ne (heq ▸ hF))

noncomputable def routeBTheta : ℝ := Classical.choose exists_routeBTheta

theorem routeBTheta_mem : routeBTheta ∈ Ioo Real.pi (3 * Real.pi / 2) :=
  (Classical.choose_spec exists_routeBTheta).1

theorem routeBF_routeBTheta : routeBF routeBTheta = 0 :=
  (Classical.choose_spec exists_routeBTheta).2

noncomputable def routeBKappa : ℝ := routeBMaxQuotient routeBTheta

@[simp] theorem routeBF_zero : routeBF 0 = 0 := by simp [routeBF]

theorem routeBF_pos_of_pos_of_lt_theta {v : ℝ}
    (hv0 : 0 < v) (hvtheta : v < routeBTheta) : 0 < routeBF v := by
  rcases lt_trichotomy v Real.pi with hvpi | hvpi | hvpi
  · have hmono := routeBF_strictMonoOn_zero_pi
    have hzeroMem : (0 : ℝ) ∈ Icc 0 Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
    have hvMem : v ∈ Icc 0 Real.pi := ⟨hv0.le, hvpi.le⟩
    simpa only [routeBF_zero] using hmono hzeroMem hvMem hv0
  · simpa only [hvpi] using routeBF_pi_pos
  · have hthetaTwoPi : routeBTheta ∈ Icc Real.pi (2 * Real.pi) :=
      ⟨routeBTheta_mem.1.le, by linarith [routeBTheta_mem.2, Real.pi_pos]⟩
    have hvTwoPi : v ∈ Icc Real.pi (2 * Real.pi) :=
      ⟨hvpi.le, by linarith [hvtheta, routeBTheta_mem.2, Real.pi_pos]⟩
    have hanti := routeBF_strictAntiOn_pi_two_pi hvTwoPi hthetaTwoPi hvtheta
    simpa only [routeBF_routeBTheta] using hanti

theorem routeBF_neg_of_theta_lt {v : ℝ}
    (hvtheta : routeBTheta < v) : routeBF v < 0 := by
  by_cases hvTwoPi : v < 2 * Real.pi
  · have hthetaTwoPi : routeBTheta ∈ Icc Real.pi (2 * Real.pi) :=
      ⟨routeBTheta_mem.1.le, by linarith [routeBTheta_mem.2, Real.pi_pos]⟩
    have hvMem : v ∈ Icc Real.pi (2 * Real.pi) :=
      ⟨by linarith [routeBTheta_mem.1], hvTwoPi.le⟩
    have hanti := routeBF_strictAntiOn_pi_two_pi hthetaTwoPi hvMem hvtheta
    simpa only [routeBF_routeBTheta] using hanti
  · have hvLower : 2 * Real.pi ≤ v := le_of_not_gt hvTwoPi
    have hv0 : 0 ≤ v := by linarith [Real.pi_pos]
    have hcos := Real.neg_one_le_cos v
    have hsin := Real.neg_one_le_sin v
    unfold routeBF
    nlinarith [Real.pi_gt_three, mul_le_mul_of_nonneg_left hsin hv0]

theorem routeBMaxQuotient_monotoneOn_to_theta :
    MonotoneOn routeBMaxQuotient (Ioc 0 routeBTheta) := by
  let derivQ : ℝ → ℝ := fun v => routeBF v / v ^ 4
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := derivQ)
    (convex_Ioc 0 routeBTheta) ?_ ?_ ?_
  · intro v hv
    exact (hasDerivAt_routeBMaxQuotient (ne_of_gt hv.1)).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioc] at hv
    exact (hasDerivAt_routeBMaxQuotient (ne_of_gt hv.1)).hasDerivWithinAt
  · intro v hv
    rw [interior_Ioc] at hv
    dsimp only [derivQ]
    exact div_nonneg (routeBF_pos_of_pos_of_lt_theta hv.1 hv.2).le (by positivity)

theorem routeBMaxQuotient_antitoneOn_from_theta :
    AntitoneOn routeBMaxQuotient (Ici routeBTheta) := by
  let derivQ : ℝ → ℝ := fun v => routeBF v / v ^ 4
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := derivQ)
    (convex_Ici routeBTheta) ?_ ?_ ?_
  · intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le (lt_trans Real.pi_pos routeBTheta_mem.1) hv
    exact (hasDerivAt_routeBMaxQuotient hv0.ne').continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ici] at hv
    have hv0 : 0 < v := lt_trans (lt_trans Real.pi_pos routeBTheta_mem.1) hv
    exact (hasDerivAt_routeBMaxQuotient hv0.ne').hasDerivWithinAt
  · intro v hv
    rw [interior_Ici] at hv
    dsimp only [derivQ]
    exact div_nonpos_of_nonpos_of_nonneg (routeBF_neg_of_theta_lt hv).le (by positivity)

theorem routeBMaxQuotient_le_kappa {v : ℝ} (hv : 0 < v) :
    routeBMaxQuotient v ≤ routeBKappa := by
  unfold routeBKappa
  by_cases hvtheta : v ≤ routeBTheta
  · exact routeBMaxQuotient_monotoneOn_to_theta
      ⟨hv, hvtheta⟩ ⟨lt_trans Real.pi_pos routeBTheta_mem.1, le_rfl⟩ hvtheta
  · have htheta : routeBTheta ≤ v := le_of_not_ge hvtheta
    exact routeBMaxQuotient_antitoneOn_from_theta
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr htheta) htheta

theorem routeBKappa_pos : 0 < routeBKappa := by
  have htheta : 3 < routeBTheta := lt_trans Real.pi_gt_three routeBTheta_mem.1
  have hcos := Real.neg_one_le_cos routeBTheta
  have hg : 0 < routeBG routeBTheta := by
    unfold routeBG
    nlinarith
  unfold routeBKappa routeBMaxQuotient
  exact div_pos hg (pow_pos (by linarith) 3)

theorem routeB_line_minorant (v : ℝ) (hv : 0 < v) :
    (1 : ℝ) / 2 - routeBKappa * v ≤ routeBPsi v := by
  have hmax := routeBMaxQuotient_le_kappa hv
  have hscaled : routeBG v ≤ routeBKappa * v ^ 3 :=
    (div_le_iff₀ (pow_pos hv 3)).mp hmax
  unfold routeBPsi
  apply (le_div_iff₀ (pow_pos hv 2)).2
  unfold routeBG at hscaled
  nlinarith

theorem routeBPsi_theta_match :
    routeBPsi routeBTheta = (1 : ℝ) / 2 - routeBKappa * routeBTheta := by
  have htheta0 : routeBTheta ≠ 0 := ne_of_gt (lt_trans Real.pi_pos routeBTheta_mem.1)
  unfold routeBPsi routeBKappa routeBMaxQuotient routeBG
  field_simp [htheta0]
  ring

theorem routeBAPrime_monotoneOn_pi_three_pi_div_two :
    MonotoneOn routeBAPrime (Icc Real.pi (3 * Real.pi / 2)) := by
  let derivA' : ℝ → ℝ := fun v => -v ^ 2 * Real.cos v
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := derivA')
    (convex_Icc Real.pi (3 * Real.pi / 2)) ?_ ?_ ?_
  · intro v _
    exact (hasDerivAt_routeBAPrime v).continuousAt.continuousWithinAt
  · intro v _
    exact (hasDerivAt_routeBAPrime v).hasDerivWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    have hcos : Real.cos v ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le
        (by linarith [Real.pi_pos, hv.1]) (by linarith [hv.2])
    dsimp only [derivA']
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (sq_nonneg v)) hcos

theorem routeBAPrime_pi_pos : 0 < routeBAPrime Real.pi := by
  rw [routeBAPrime]
  simp only [Real.cos_pi, Real.sin_pi]
  nlinarith [Real.pi_pos]

theorem routeBA_monotoneOn_pi_three_pi_div_two :
    MonotoneOn routeBA (Icc Real.pi (3 * Real.pi / 2)) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := routeBAPrime)
    (convex_Icc Real.pi (3 * Real.pi / 2)) ?_ ?_ ?_
  · intro v _
    exact (hasDerivAt_routeBA v).continuousAt.continuousWithinAt
  · intro v _
    exact (hasDerivAt_routeBA v).hasDerivWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    have hpi : Real.pi ∈ Icc Real.pi (3 * Real.pi / 2) :=
      ⟨le_rfl, by linarith [Real.pi_pos]⟩
    have hvMem : v ∈ Icc Real.pi (3 * Real.pi / 2) := ⟨hv.1.le, hv.2.le⟩
    exact (routeBAPrime_pi_pos.le.trans
      (routeBAPrime_monotoneOn_pi_three_pi_div_two hpi hvMem hv.1.le))

theorem routeBA_pi_pos : 0 < routeBA Real.pi := by
  rw [routeBA]
  simp only [Real.cos_pi, Real.sin_pi]
  nlinarith [Real.pi_pos, Real.pi_lt_d2]

theorem routeBA_pos_on_pi_three_pi_div_two {v : ℝ}
    (hv : v ∈ Icc Real.pi (3 * Real.pi / 2)) : 0 < routeBA v := by
  exact routeBA_pi_pos.trans_le
    (routeBA_monotoneOn_pi_three_pi_div_two
      ⟨le_rfl, by linarith [Real.pi_pos]⟩ hv hv.1)

theorem routeBA_concaveOn_three_pi_div_two_two_pi :
    ConcaveOn ℝ (Icc (3 * Real.pi / 2) (2 * Real.pi)) routeBA := by
  let derivA' : ℝ → ℝ := fun v => -v ^ 2 * Real.cos v
  refine concaveOn_of_hasDerivWithinAt2_nonpos
    (f' := routeBAPrime) (f'' := derivA')
    (convex_Icc (3 * Real.pi / 2) (2 * Real.pi)) ?_ ?_ ?_ ?_
  · intro v _
    exact (hasDerivAt_routeBA v).continuousAt.continuousWithinAt
  · intro v _
    exact (hasDerivAt_routeBA v).hasDerivWithinAt
  · intro v _
    exact (hasDerivAt_routeBAPrime v).hasDerivWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    have hs : 2 * Real.pi - v ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos, hv.2], by linarith [hv.1]⟩
    have hcos : 0 ≤ Real.cos v := by
      rw [← Real.cos_two_pi_sub v]
      exact Real.cos_nonneg_of_mem_Icc hs
    dsimp only [derivA']
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg v)) hcos

theorem routeBA_three_pi_div_two_pos : 0 < routeBA (3 * Real.pi / 2) := by
  rw [routeBA]
  have harg : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
  rw [harg, Real.cos_add, Real.sin_add]
  simp only [Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  nlinarith [Real.pi_pos]

theorem routeBA_two_pi_pos : 0 < routeBA (2 * Real.pi) := by
  rw [routeBA, Real.cos_two_pi, Real.sin_two_pi]
  nlinarith [pow_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) 2]

theorem routeBA_nonneg_on_three_pi_div_two_two_pi {v : ℝ}
    (hv : v ∈ Icc (3 * Real.pi / 2) (2 * Real.pi)) : 0 ≤ routeBA v := by
  have hleft : 3 * Real.pi / 2 ∈ Icc (3 * Real.pi / 2) (2 * Real.pi) :=
    ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hright : 2 * Real.pi ∈ Icc (3 * Real.pi / 2) (2 * Real.pi) :=
    ⟨by linarith [Real.pi_pos], le_rfl⟩
  have hmin := routeBA_concaveOn_three_pi_div_two_two_pi.min_le_of_mem_Icc
    hleft hright hv
  exact (le_min routeBA_three_pi_div_two_pos.le routeBA_two_pi_pos.le).trans hmin

theorem routeBA_nonneg_on_theta_two_pi {v : ℝ}
    (hv : v ∈ Icc routeBTheta (2 * Real.pi)) : 0 ≤ routeBA v := by
  by_cases hvsplit : v ≤ 3 * Real.pi / 2
  · exact (routeBA_pos_on_pi_three_pi_div_two
      ⟨(routeBTheta_mem.1.trans_le hv.1).le, hvsplit⟩).le
  · exact routeBA_nonneg_on_three_pi_div_two_two_pi
      ⟨le_of_not_ge hvsplit, hv.2⟩

theorem routeBPsi_convexOn_theta_two_pi :
    ConvexOn ℝ (Icc routeBTheta (2 * Real.pi)) routeBPsi := by
  let second : ℝ → ℝ := fun v => routeBA v / v ^ 4
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := routeBPsiPrime) (f'' := second)
    (convex_Icc routeBTheta (2 * Real.pi)) ?_ ?_ ?_ ?_
  · intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le
      (lt_trans Real.pi_pos routeBTheta_mem.1) hv.1
    exact (hasDerivAt_routeBPsi hv0.ne').continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    have hv0 : 0 < v := lt_trans (lt_trans Real.pi_pos routeBTheta_mem.1) hv.1
    exact (hasDerivAt_routeBPsi hv0.ne').hasDerivWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    have hv0 : 0 < v := lt_trans (lt_trans Real.pi_pos routeBTheta_mem.1) hv.1
    exact (hasDerivAt_routeBPsiPrime hv0.ne').hasDerivWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    dsimp only [second]
    exact div_nonneg (routeBA_nonneg_on_theta_two_pi ⟨hv.1.le, hv.2.le⟩)
      (by positivity)

theorem routeBPsiPrime_monotoneOn_theta_two_pi :
    MonotoneOn routeBPsiPrime (Icc routeBTheta (2 * Real.pi)) := by
  let second : ℝ → ℝ := fun v => routeBA v / v ^ 4
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := second)
    (convex_Icc routeBTheta (2 * Real.pi)) ?_ ?_ ?_
  · intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le
      (lt_trans Real.pi_pos routeBTheta_mem.1) hv.1
    exact (hasDerivAt_routeBPsiPrime hv0.ne').continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    have hv0 : 0 < v := lt_trans (lt_trans Real.pi_pos routeBTheta_mem.1) hv.1
    exact (hasDerivAt_routeBPsiPrime hv0.ne').hasDerivWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    dsimp only [second]
    exact div_nonneg (routeBA_nonneg_on_theta_two_pi ⟨hv.1.le, hv.2.le⟩)
      (by positivity)

theorem routeBPsiPrime_nonpos_on_theta_two_pi {v : ℝ}
    (hv : v ∈ Icc routeBTheta (2 * Real.pi)) : routeBPsiPrime v ≤ 0 := by
  have hv0 : 0 < v := lt_of_lt_of_le
    (lt_trans Real.pi_pos routeBTheta_mem.1) hv.1
  have hsArg : 2 * Real.pi - v ∈ Icc 0 Real.pi :=
    ⟨by linarith [hv.2], by linarith [routeBTheta_mem.1, hv.1]⟩
  have hsinArg := Real.sin_nonneg_of_mem_Icc hsArg
  rw [Real.sin_two_pi_sub] at hsinArg
  have hsin : Real.sin v ≤ 0 := by linarith
  have hcos : Real.cos v ≤ 1 := Real.cos_le_one v
  unfold routeBPsiPrime
  exact div_nonpos_of_nonpos_of_nonneg
    (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hv0.le hsin])
    (by positivity)

theorem routeBPsi_antitoneOn_theta_two_pi :
    AntitoneOn routeBPsi (Icc routeBTheta (2 * Real.pi)) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := routeBPsiPrime)
    (convex_Icc routeBTheta (2 * Real.pi)) ?_ ?_ ?_
  · intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le
      (lt_trans Real.pi_pos routeBTheta_mem.1) hv.1
    exact (hasDerivAt_routeBPsi hv0.ne').continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    have hv0 : 0 < v := lt_trans (lt_trans Real.pi_pos routeBTheta_mem.1) hv.1
    exact (hasDerivAt_routeBPsi hv0.ne').hasDerivWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    exact routeBPsiPrime_nonpos_on_theta_two_pi ⟨hv.1.le, hv.2.le⟩

theorem routeBPsiPrime_theta : routeBPsiPrime routeBTheta = -routeBKappa := by
  have htheta0 : routeBTheta ≠ 0 := ne_of_gt (lt_trans Real.pi_pos routeBTheta_mem.1)
  have hF := routeBF_routeBTheta
  unfold routeBF at hF
  unfold routeBPsiPrime routeBKappa routeBMaxQuotient routeBG
  field_simp [htheta0]
  nlinarith

theorem hasDerivAt_routeBPsi_add_kappa_mul {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (fun w => routeBPsi w + routeBKappa * w)
      (routeBPsiPrime v + routeBKappa) v := by
  simpa only [id_eq, mul_one] using
    (hasDerivAt_routeBPsi hv).add ((hasDerivAt_id v).const_mul routeBKappa)

theorem routeBPsi_add_linear_monotoneOn_theta_two_pi :
    MonotoneOn (fun v => routeBPsi v + routeBKappa * v)
      (Icc routeBTheta (2 * Real.pi)) := by
  let first : ℝ → ℝ := fun v => routeBPsiPrime v + routeBKappa
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := first)
    (convex_Icc routeBTheta (2 * Real.pi)) ?_ ?_ ?_
  · intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le
      (lt_trans Real.pi_pos routeBTheta_mem.1) hv.1
    exact (hasDerivAt_routeBPsi_add_kappa_mul hv0.ne').continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    have hv0 : 0 < v := lt_trans (lt_trans Real.pi_pos routeBTheta_mem.1) hv.1
    exact (hasDerivAt_routeBPsi_add_kappa_mul hv0.ne').hasDerivWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    have hthetaMem : routeBTheta ∈ Icc routeBTheta (2 * Real.pi) :=
      ⟨le_rfl, by linarith [routeBTheta_mem.2, Real.pi_pos]⟩
    have hvMem : v ∈ Icc routeBTheta (2 * Real.pi) := ⟨hv.1.le, hv.2.le⟩
    have hmono := routeBPsiPrime_monotoneOn_theta_two_pi
      hthetaMem hvMem hv.1.le
    dsimp only [first]
    rw [routeBPsiPrime_theta] at hmono
    linarith

theorem routeB_exactMinorantCertificate :
    RouteBMinorantCertificate routeBKappa routeBTheta where
  theta_pos := lt_trans Real.pi_pos routeBTheta_mem.1
  theta_lt_two_pi := by linarith [routeBTheta_mem.2, Real.pi_pos]
  kappa_nonneg := routeBKappa_pos.le
  line_minorant := routeB_line_minorant
  match_theta := routeBPsi_theta_match
  psi_convex := routeBPsi_convexOn_theta_two_pi
  psi_antitone := routeBPsi_antitoneOn_theta_two_pi
  psi_add_linear_monotone := routeBPsi_add_linear_monotoneOn_theta_two_pi

end

end BerryEsseen
