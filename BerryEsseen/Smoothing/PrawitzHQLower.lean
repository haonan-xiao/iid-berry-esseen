import BerryEsseen.CharacteristicFunction.BreakpointNumerics
/-!
# The analytic lower envelope used by `hq_lower`

This module proves both branches of the Route B checker's lower envelope for
`(2 * π * t)^2 q(2 * π * t)`.  The low branch uses the certified upper bound on the
minorant slope; the high branch proves the required twelfth-order alternating cosine bound.
-/

open Finset

namespace BerryEsseen

noncomputable section

def oneSubCosMagnitude (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * (n + 1)) / (2 * (n + 1)).factorial

theorem oneSubCosMagnitude_antitone {x : ℝ}
    (hx0 : 0 ≤ x) (hxUpper : x ≤ 16 / 7) :
    Antitone (oneSubCosMagnitude x) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold oneSubCosMagnitude
  rw [show 2 * (n + 1 + 1) = (2 * (n + 1) + 1) + 1 by omega]
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [show 2 * (n + 1) + 2 = 2 * (n + 1) + 2 by rfl, pow_add]
  have hpow : x ^ 2 ≤ 12 := by
    nlinarith [sq_nonneg (x - 16 / 7)]
  have hfac : (0 : ℝ) < (2 * (n + 1)).factorial := by positivity
  have h1 : (3 : ℝ) ≤ 2 * n + 3 := by
    exact_mod_cast (by omega : 3 ≤ 2 * n + 3)
  have h2 : (4 : ℝ) ≤ 2 * n + 4 := by
    exact_mod_cast (by omega : 4 ≤ 2 * n + 4)
  have hden : x ^ 2 ≤ (2 * n + 3 : ℝ) * (2 * n + 4 : ℝ) := by
    refine hpow.trans ?_
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  have hbase : 0 ≤ x ^ (2 * (n + 1)) * ((2 * (n + 1)).factorial : ℝ) :=
    mul_nonneg (pow_nonneg hx0 _) hfac.le
  rw [div_le_div_iff₀]
  · calc
      x ^ (2 * (n + 1)) * x ^ 2 * ((2 * (n + 1)).factorial : ℝ) =
          (x ^ (2 * (n + 1)) * ((2 * (n + 1)).factorial : ℝ)) * x ^ 2 := by ring
      _ ≤ (x ^ (2 * (n + 1)) * ((2 * (n + 1)).factorial : ℝ)) *
          ((2 * n + 3 : ℝ) * (2 * n + 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hden hbase
      _ = x ^ (2 * (n + 1)) *
          ((2 * (n : ℝ) + 2 + 1 + 1) *
            ((2 * (n : ℝ) + 2 + 1) * ((2 * (n + 1)).factorial : ℝ))) := by ring
      _ = x ^ (2 * (n + 1)) *
          ((2 * ((n : ℝ) + 1) + 1 + 1) *
            ((2 * ((n : ℝ) + 1) + 1) * ((2 * (n + 1)).factorial : ℝ))) := by ring
  · positivity
  · positivity

theorem hasSum_oneSubCosMagnitude (x : ℝ) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * oneSubCosMagnitude x n)
      (1 - Real.cos x) := by
  have hfull : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * cosMagnitude x n)
      (Real.cos x) := by
    simpa only [cosMagnitude, mul_div_assoc] using Real.hasSum_cos x
  have htail := (hasSum_nat_add_iff' 1).mpr hfull
  have hneg := htail.neg
  convert hneg using 1
  · funext n
    unfold oneSubCosMagnitude cosMagnitude
    rw [pow_succ]
    ring
  · norm_num [cosMagnitude, Finset.sum_range_succ]

def prawitzCosineLossTaylor12 (x : ℝ) : ℝ :=
  x ^ 2 / 2 - x ^ 4 / 24 + x ^ 6 / 720 - x ^ 8 / 40320 +
    x ^ 10 / 3628800 - x ^ 12 / 479001600

theorem prawitzCosineLossTaylor12_le {x : ℝ}
    (hx0 : 0 ≤ x) (hxUpper : x ≤ 16 / 7) :
    prawitzCosineLossTaylor12 x ≤ 1 - Real.cos x := by
  have hbound := (oneSubCosMagnitude_antitone hx0 hxUpper).alternating_series_le_tendsto
    (hasSum_oneSubCosMagnitude x).tendsto_sum_nat 3
  convert hbound using 1
  norm_num [prawitzCosineLossTaylor12, alternatingPartial, oneSubCosMagnitude,
    Finset.sum_range_succ, Nat.factorial]
  ring

theorem checkerKappaUpper_line_le_routeBMinorant {v : ℝ}
    (hv0 : 0 ≤ v) (hvTwoPi : v ≤ 2 * Real.pi) :
    (1 : ℝ) / 2 - routeBKappaUpper * v ≤
      routeBMinorant routeBKappa routeBTheta v := by
  by_cases hvz : v = 0
  · subst v
    have htheta0 : (0 : ℝ) ≤ routeBTheta :=
      (lt_trans Real.pi_pos routeBTheta_mem.1).le
    simp [routeBMinorant, htheta0]
  · have hvPos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hvz)
    have hk : routeBKappa ≤ routeBKappaUpper := routeBKappa_lt_upper.le
    by_cases hvTheta : v ≤ routeBTheta
    · rw [routeBMinorant, if_pos hvTheta]
      exact sub_le_sub_left (mul_le_mul_of_nonneg_right hk hv0) _
    · rw [routeBMinorant, if_neg hvTheta, if_pos hvTwoPi]
      exact (sub_le_sub_left (mul_le_mul_of_nonneg_right hk hv0) _).trans
        (routeB_line_minorant v hvPos)

theorem prawitzHQLowBranch_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (2 * Real.pi * t) ^ 2 *
        ((1 : ℝ) / 2 - routeBKappaUpper * (2 * Real.pi * t)) ≤
      (2 * Real.pi * t) ^ 2 *
        routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t) := by
  let v := 2 * Real.pi * t
  have hv0 : 0 ≤ v := by dsimp only [v]; positivity
  have hvTwoPi : v ≤ 2 * Real.pi := by
    dsimp only [v]
    nlinarith [Real.pi_pos]
  have hline := checkerKappaUpper_line_le_routeBMinorant hv0 hvTwoPi
  dsimp only [v] at hline ⊢
  exact mul_le_mul_of_nonneg_left hline (sq_nonneg _)

theorem prawitzHQHighBranch_le {t : ℝ}
    (ht1 : t ≤ 1) (hv4 : 4 ≤ 2 * Real.pi * t) :
    prawitzCosineLossTaylor12 (2 * Real.pi * (1 - t)) ≤
      (2 * Real.pi * t) ^ 2 *
        routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t) := by
  let v := 2 * Real.pi * t
  have hvTwoPi : v ≤ 2 * Real.pi := by
    dsimp only [v]
    nlinarith [Real.pi_pos]
  have htheta4 : routeBTheta < 4 := by
    have h := routeBTheta_lt_upper
    norm_num [routeBThetaUpper] at h ⊢
    linarith
  have hv4' : 4 ≤ v := by simpa only [v] using hv4
  have hvTheta : ¬v ≤ routeBTheta := by linarith
  have hvPos : 0 < v := lt_of_lt_of_le (by norm_num) hv4'
  let x := 2 * Real.pi * (1 - t)
  have hxEq : x = 2 * Real.pi - v := by dsimp only [x, v]; ring
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (sub_nonneg.mpr ht1)
  have hxTwoPiFour : x ≤ 2 * Real.pi - 4 := by linarith
  have hpiUpper : Real.pi < piUpper20 := Real.pi_lt_d20
  have hxUpper : x ≤ 16 / 7 := by
    have hnumeric : 2 * piUpper20 - 4 < (16 / 7 : ℝ) := by
      norm_num [piUpper20]
    linarith
  have htaylor := prawitzCosineLossTaylor12_le hx0 hxUpper
  have hcos : Real.cos x = Real.cos v := by
    rw [hxEq, Real.cos_two_pi_sub]
  have hpsi : v ^ 2 * routeBPsi v = 1 - Real.cos v := by
    unfold routeBPsi
    field_simp [hvPos.ne']
  dsimp only [x, v] at htaylor hcos hpsi hvTheta hvTwoPi ⊢
  rw [routeBMinorant, if_neg hvTheta, if_pos hvTwoPi, hpsi]
  linarith

def prawitzHQLower (t : ℝ) : ℝ :=
  let v := 2 * Real.pi * t
  if 4 ≤ v then
    prawitzCosineLossTaylor12 (2 * Real.pi * (1 - t))
  else
    v ^ 2 * ((1 : ℝ) / 2 - routeBKappaUpper * v)

theorem prawitzHQLower_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    prawitzHQLower t ≤
      (2 * Real.pi * t) ^ 2 *
        routeBMinorant routeBKappa routeBTheta (2 * Real.pi * t) := by
  let v := 2 * Real.pi * t
  have hv0 : 0 ≤ v := by dsimp only [v]; positivity
  have hvTwoPi : v ≤ 2 * Real.pi := by
    dsimp only [v]
    nlinarith [Real.pi_pos]
  by_cases hv4 : 4 ≤ v
  · have htheta4 : routeBTheta < 4 := by
      have h := routeBTheta_lt_upper
      norm_num [routeBThetaUpper] at h ⊢
      linarith
    have hvTheta : ¬v ≤ routeBTheta := by linarith
    have hvPos : 0 < v := lt_of_lt_of_le (by norm_num) hv4
    let x := 2 * Real.pi * (1 - t)
    have hxEq : x = 2 * Real.pi - v := by dsimp only [x, v]; ring
    have hx0 : 0 ≤ x := by
      dsimp only [x]
      exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (sub_nonneg.mpr ht1)
    have hxTwoPiFour : x ≤ 2 * Real.pi - 4 := by linarith
    have hpiUpper : Real.pi < piUpper20 := Real.pi_lt_d20
    have hxUpper : x ≤ 16 / 7 := by
      have hnumeric : 2 * piUpper20 - 4 < (16 / 7 : ℝ) := by
        norm_num [piUpper20]
      linarith
    have htaylor := prawitzCosineLossTaylor12_le hx0 hxUpper
    have hcos : Real.cos x = Real.cos v := by
      rw [hxEq, Real.cos_two_pi_sub]
    have hpsi : v ^ 2 * routeBPsi v = 1 - Real.cos v := by
      unfold routeBPsi
      field_simp [hvPos.ne']
    unfold prawitzHQLower
    dsimp only [v] at hv4 ⊢
    rw [if_pos hv4, routeBMinorant, if_neg hvTheta, if_pos hvTwoPi, hpsi]
    linarith
  · have hline := checkerKappaUpper_line_le_routeBMinorant hv0 hvTwoPi
    unfold prawitzHQLower
    dsimp only [v] at hv4 hline ⊢
    rw [if_neg hv4]
    exact mul_le_mul_of_nonneg_left hline (sq_nonneg _)


end

end BerryEsseen
