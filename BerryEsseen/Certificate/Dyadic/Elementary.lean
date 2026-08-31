import BerryEsseen.Certificate.Dyadic.Interval
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Verified elementary-function interval kernels

This module formalizes the two alternating-series routines used by the Route B exact verifier.
For `exp (-x)`, it proves the degree-25/24 enclosure after dyadic range reduction and then proves
that repeated outward squaring reverses the halving.  For
`H(y) = (exp (-y) - 1 + y) / y²`, with removable value `H(0) = 1/2`, it derives the shifted
series from the exponential series and verifies the degree-25/24 interval recurrence on
`0 ≤ y ≤ 3`.  All executable routines use the precision-48 integer kernel from
`DyadicInterval.lean`.
-/

open Finset

namespace BerryEsseen

noncomputable section Analytic

def expMagnitude (x : ℝ) (n : ℕ) : ℝ := x ^ n / n.factorial

def hMagnitude (y : ℝ) (n : ℕ) : ℝ := y ^ n / (n + 2).factorial

def routeBH (y : ℝ) : ℝ :=
  if y = 0 then 1 / 2 else (Real.exp (-y) - 1 + y) / y ^ 2

theorem expMagnitude_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (expMagnitude x) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold expMagnitude
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hn : (1 : ℝ) ≤ n + 1 := by linarith
  rw [div_le_div_iff₀]
  · calc
      x ^ n * x * (n.factorial : ℝ) ≤
          x ^ n * 1 * (n.factorial : ℝ) := by gcongr
      _ ≤ x ^ n * (n + 1 : ℝ) * (n.factorial : ℝ) := by gcongr
      _ = x ^ n * ((n + 1 : ℝ) * (n.factorial : ℝ)) := by ring
  · positivity
  · positivity

theorem hMagnitude_antitone {y : ℝ} (hy0 : 0 ≤ y) (hy3 : y ≤ 3) :
    Antitone (hMagnitude y) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold hMagnitude
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.factorial_succ, pow_succ]
  push_cast
  have hfac : (0 : ℝ) < (n + 2).factorial := by positivity
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hyn : y ≤ (n : ℝ) + 3 := by linarith
  rw [div_le_div_iff₀]
  · calc
      y ^ n * y * ((n + 2).factorial : ℝ) ≤
          y ^ n * ((n : ℝ) + 3) * ((n + 2).factorial : ℝ) := by gcongr
      _ = y ^ n * (((n : ℝ) + 3) * ((n + 2).factorial : ℝ)) := by ring
      _ = y ^ n * (((n : ℝ) + 2 + 1) * ((n + 2).factorial : ℝ)) := by ring
  · positivity
  · positivity

theorem expNeg_lower_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    alternatingPartial (expMagnitude x) (2 * k) ≤ Real.exp (-x) := by
  have hsum : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * expMagnitude x n)
      (Real.exp (-x)) := by
    convert NormedSpace.expSeries_div_hasSum_exp (-x : ℝ) using 1 with n
    unfold expMagnitude
    funext n
    rw [neg_pow]
    ring
    rw [Real.exp_eq_exp_ℝ]
  exact (expMagnitude_antitone hx0 hx1).alternating_series_le_tendsto
    hsum.tendsto_sum_nat k

theorem expNeg_upper_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    Real.exp (-x) ≤ alternatingPartial (expMagnitude x) (2 * k + 1) := by
  have hsum : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * expMagnitude x n)
      (Real.exp (-x)) := by
    convert NormedSpace.expSeries_div_hasSum_exp (-x : ℝ) using 1 with n
    unfold expMagnitude
    funext n
    rw [neg_pow]
    ring
    rw [Real.exp_eq_exp_ℝ]
  exact (expMagnitude_antitone hx0 hx1).tendsto_le_alternating_series
    hsum.tendsto_sum_nat k

theorem hasSum_routeBH (y : ℝ) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * hMagnitude y n) (routeBH y) := by
  by_cases hy : y = 0
  · subst y
    convert hasSum_ite_eq 0 (1 / 2 : ℝ) using 1
    · funext n
      cases n <;> norm_num [hMagnitude]
    · simp [routeBH]
  · have hfull := NormedSpace.expSeries_div_hasSum_exp (-y : ℝ)
    have htail := (hasSum_nat_add_iff' 2).mpr hfull
    have hdiv := htail.div_const (y ^ 2)
    convert hdiv using 1 with n
    · funext n
      unfold hMagnitude
      rw [neg_pow]
      field_simp [hy]
      ring
    · rw [routeBH, if_neg hy]
      rw [Real.exp_eq_exp_ℝ]
      norm_num [Finset.sum_range_succ]
      ring

theorem routeBH_lower_bound {y : ℝ} (hy0 : 0 ≤ y) (hy3 : y ≤ 3) (k : ℕ) :
    alternatingPartial (hMagnitude y) (2 * k) ≤ routeBH y := by
  exact (hMagnitude_antitone hy0 hy3).alternating_series_le_tendsto
    (hasSum_routeBH y).tendsto_sum_nat k

theorem routeBH_upper_bound {y : ℝ} (hy0 : 0 ≤ y) (hy3 : y ≤ 3) (k : ℕ) :
    routeBH y ≤ alternatingPartial (hMagnitude y) (2 * k + 1) := by
  exact (hMagnitude_antitone hy0 hy3).tendsto_le_alternating_series
    (hasSum_routeBH y).tendsto_sum_nat k

end Analytic

open DyadicInterval

structure ExpNegState where
  term : DyadicInterval
  sum : DyadicInterval
deriving DecidableEq, Repr

def expNegStateStep (y : DyadicInterval) (k : ℕ) (s : ExpNegState) : ExpNegState :=
  let nextTerm := DyadicInterval.divPoint (DyadicInterval.mul s.term y) (Int.ofNat k)
  let nextSum := if Even k then DyadicInterval.add s.sum nextTerm
    else DyadicInterval.sub s.sum nextTerm
  ⟨nextTerm, nextSum⟩

def expNegState (y : DyadicInterval) : ℕ → ExpNegState
  | 0 => ⟨DyadicInterval.point 1, DyadicInterval.point 1⟩
  | n + 1 => expNegStateStep y (n + 1) (expNegState y n)

/-- Degree-13/12 alternating enclosure used after reduction to `x ≤ 1/8`.
The omitted term is far below the precision-48 rounding scale; soundness still follows directly
from the alternating-series bounds. -/
def expNegTaylor (y : DyadicInterval) : DyadicInterval :=
  ⟨max 0 (expNegState y 13).sum.lo,
    min dyadicScale (expNegState y 12).sum.hi⟩

def halfIter (I : DyadicInterval) : ℕ → DyadicInterval
  | 0 => I
  | n + 1 => DyadicInterval.half (halfIter I n)

def sqrIter (I : DyadicInterval) : ℕ → DyadicInterval
  | 0 => I
  | n + 1 => DyadicInterval.sqr (sqrIter I n)

def expNegWithHalvings (I : DyadicInterval) (j : ℕ) : DyadicInterval :=
  sqrIter (expNegTaylor (halfIter I j)) j

structure HState where
  term : DyadicInterval
  sum : DyadicInterval
deriving DecidableEq, Repr

def hStateStep (y : DyadicInterval) (k : ℕ) (s : HState) : HState :=
  let nextTerm := DyadicInterval.divPoint (DyadicInterval.mul s.term y)
    (Int.ofNat (k + 2))
  let nextSum := if Even k then DyadicInterval.add s.sum nextTerm
    else DyadicInterval.sub s.sum nextTerm
  ⟨nextTerm, nextSum⟩

def hState (y : DyadicInterval) : ℕ → HState
  | 0 =>
      let half := DyadicInterval.ofRat 1 2
      ⟨half, half⟩
  | n + 1 => hStateStep y (n + 1) (hState y n)

def hfunInterval (y : DyadicInterval) : DyadicInterval :=
  ⟨(hState y 25).sum.lo, (hState y 24).sum.hi⟩

noncomputable section Soundness

theorem expMagnitude_succ (x : ℝ) (n : ℕ) :
    expMagnitude x (n + 1) = expMagnitude x n * x / (n + 1 : ℝ) := by
  unfold expMagnitude
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hsucc : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hfac, hsucc]

theorem alternatingPartial_succ (x : ℝ) (n : ℕ) :
    alternatingPartial (expMagnitude x) (n + 1) =
      alternatingPartial (expMagnitude x) n +
        (-1 : ℝ) ^ n * expMagnitude x n := by
  simp [alternatingPartial, Finset.sum_range_succ]

theorem expNegStateStep_sound {y : DyadicInterval} {x : ℝ} {n : ℕ}
    {s : ExpNegState}
    (hy : y.Contains x)
    (hterm : s.term.Contains (expMagnitude x n))
    (hsum : s.sum.Contains (alternatingPartial (expMagnitude x) (n + 1))) :
    let next := expNegStateStep y (n + 1) s
    next.term.Contains (expMagnitude x (n + 1)) ∧
      next.sum.Contains (alternatingPartial (expMagnitude x) (n + 2)) := by
  let k : ℕ := n + 1
  let denom := DyadicInterval.point (Int.ofNat k)
  let nextTerm := DyadicInterval.div (DyadicInterval.mul s.term y) denom
  have hkNat : 0 < k := by simp [k]
  have hdenom : denom.Contains (k : ℝ) := by
    simpa [denom] using DyadicInterval.contains_point (Int.ofNat k)
  have hdenomOrdered : denom.Ordered := hdenom.ordered
  have hdenomLoPos : 0 < denom.lo := by
    dsimp [denom, DyadicInterval.point]
    exact mul_pos (by exact_mod_cast hkNat) dyadicScale_pos
  have hnextTermRaw : nextTerm.Contains
      ((expMagnitude x n * x) / (k : ℝ)) := by
    exact (hterm.mul hy).div hdenom hdenomOrdered hdenomLoPos
  have hnextTerm : nextTerm.Contains (expMagnitude x (n + 1)) := by
    rw [expMagnitude_succ]
    simpa only [k, Nat.cast_add, Nat.cast_one] using hnextTermRaw
  by_cases heven : Even k
  · have hnextSumRaw := hsum.add hnextTerm
    have hnextSum :
        (DyadicInterval.add s.sum nextTerm).Contains
          (alternatingPartial (expMagnitude x) (n + 2)) := by
      rw [show n + 2 = (n + 1) + 1 by omega, alternatingPartial_succ]
      rw [show n + 1 = k by rfl, heven.neg_one_pow]
      simpa only [one_mul] using hnextSumRaw
    simpa [expNegStateStep, nextTerm, k, heven] using And.intro hnextTerm hnextSum
  · have hodd : Odd k := Nat.not_even_iff_odd.mp heven
    have hnextSumRaw := hsum.sub hnextTerm
    have hnextSum :
        (DyadicInterval.sub s.sum nextTerm).Contains
          (alternatingPartial (expMagnitude x) (n + 2)) := by
      rw [show n + 2 = (n + 1) + 1 by omega, alternatingPartial_succ]
      rw [show n + 1 = k by rfl, hodd.neg_one_pow]
      simpa only [neg_one_mul, sub_eq_add_neg] using hnextSumRaw
    simpa [expNegStateStep, nextTerm, k, heven] using And.intro hnextTerm hnextSum

theorem expNegState_sound {y : DyadicInterval} {x : ℝ} (hy : y.Contains x) (n : ℕ) :
    (expNegState y n).term.Contains (expMagnitude x n) ∧
      (expNegState y n).sum.Contains
        (alternatingPartial (expMagnitude x) (n + 1)) := by
  induction n with
  | zero =>
      constructor
      · simpa [expNegState, expMagnitude] using DyadicInterval.contains_point (1 : ℤ)
      · simpa [expNegState, alternatingPartial, expMagnitude,
          Finset.sum_range_succ] using DyadicInterval.contains_point (1 : ℤ)
  | succ n ih =>
      simpa [expNegState] using expNegStateStep_sound hy ih.1 ih.2

theorem expNegTaylor_sound {y : DyadicInterval} {x : ℝ}
    (hy : y.Contains x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (expNegTaylor y).Contains (Real.exp (-x)) := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  have hstate13 := (expNegState_sound hy 13).2
  have hstate12 := (expNegState_sound hy 12).2
  have hlowerTaylor : (expNegState y 13).sum.lower ≤ Real.exp (-x) := by
    exact hstate13.1.trans (by simpa using expNeg_lower_bound hx0 hx1 7)
  have hupperTaylor : Real.exp (-x) ≤ (expNegState y 12).sum.upper := by
    have htaylor : Real.exp (-x) ≤
        alternatingPartial (expMagnitude x) 13 := by
      simpa using expNeg_upper_bound hx0 hx1 6
    exact htaylor.trans hstate12.2
  have hexpNonneg : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hexpLeOne : Real.exp (-x) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_monotone (neg_nonpos.mpr hx0)
  constructor
  · change ((max 0 (expNegState y 13).sum.lo : ℤ) : ℝ) /
      (dyadicScale : ℝ) ≤ Real.exp (-x)
    rw [Int.cast_max, Int.cast_zero, ← max_div_div_right hscale.le, zero_div]
    exact max_le hexpNonneg hlowerTaylor
  · change Real.exp (-x) ≤
      ((min dyadicScale (expNegState y 12).sum.hi : ℤ) : ℝ) /
        (dyadicScale : ℝ)
    rw [Int.cast_min, ← min_div_div_right hscale.le]
    rw [div_self hscale.ne']
    exact le_min hexpLeOne hupperTaylor

theorem halfIter_sound {I : DyadicInterval} {x : ℝ} (hx : I.Contains x) (n : ℕ) :
    (halfIter I n).Contains (x / (2 : ℝ) ^ n) := by
  induction n with
  | zero => simpa [halfIter] using hx
  | succ n ih =>
      have hhalf := ih.half
      simpa [halfIter, pow_succ, div_div] using hhalf

theorem sqrIter_sound {I : DyadicInterval} {x : ℝ} (hx : I.Contains x) (n : ℕ) :
    (sqrIter I n).Contains (x ^ (2 ^ n : ℕ)) := by
  induction n with
  | zero => simpa [sqrIter] using hx
  | succ n ih =>
      have hsq := ih.sqr ih.ordered
      simpa [sqrIter, pow_succ, pow_mul] using hsq

theorem expNegWithHalvings_sound {I : DyadicInterval} {x : ℝ} (hx : I.Contains x)
    (hx0 : 0 ≤ x) (j : ℕ) (hreduced : x / (2 : ℝ) ^ j ≤ 1) :
    (expNegWithHalvings I j).Contains (Real.exp (-x)) := by
  have hhalf := halfIter_sound hx j
  have hdivPos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hreduced0 : 0 ≤ x / (2 : ℝ) ^ j := div_nonneg hx0 hdivPos.le
  have htaylor := expNegTaylor_sound hhalf hreduced0 hreduced
  have hsquared := sqrIter_sound htaylor j
  have hpow : (Real.exp (-(x / (2 : ℝ) ^ j))) ^ (2 ^ j : ℕ) =
      Real.exp (-x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  simpa [expNegWithHalvings, hpow] using hsquared

theorem hMagnitude_succ (y : ℝ) (n : ℕ) :
    hMagnitude y (n + 1) = hMagnitude y n * y / (n + 3 : ℝ) := by
  unfold hMagnitude
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.factorial_succ, pow_succ]
  push_cast
  have hfac : ((n + 2).factorial : ℝ) ≠ 0 := by positivity
  have hsucc : (n + 3 : ℝ) ≠ 0 := by positivity
  field_simp [hfac, hsucc]
  ring

theorem hAlternatingPartial_succ (y : ℝ) (n : ℕ) :
    alternatingPartial (hMagnitude y) (n + 1) =
      alternatingPartial (hMagnitude y) n +
        (-1 : ℝ) ^ n * hMagnitude y n := by
  simp [alternatingPartial, Finset.sum_range_succ]

theorem hStateStep_sound {y : DyadicInterval} {x : ℝ} {n : ℕ}
    {s : HState}
    (hy : y.Contains x)
    (hterm : s.term.Contains (hMagnitude x n))
    (hsum : s.sum.Contains (alternatingPartial (hMagnitude x) (n + 1))) :
    let next := hStateStep y (n + 1) s
    next.term.Contains (hMagnitude x (n + 1)) ∧
      next.sum.Contains (alternatingPartial (hMagnitude x) (n + 2)) := by
  let k : ℕ := n + 1
  let denom := DyadicInterval.point (Int.ofNat (k + 2))
  let nextTerm := DyadicInterval.div (DyadicInterval.mul s.term y) denom
  have hkNat : 0 < k + 2 := by omega
  have hdenom : denom.Contains ((k + 2 : ℕ) : ℝ) := by
    simpa [denom] using DyadicInterval.contains_point (Int.ofNat (k + 2))
  have hdenomOrdered : denom.Ordered := hdenom.ordered
  have hdenomLoPos : 0 < denom.lo := by
    dsimp [denom, DyadicInterval.point]
    exact mul_pos (by exact_mod_cast hkNat) dyadicScale_pos
  have hnextTermRaw : nextTerm.Contains
      ((hMagnitude x n * x) / ((k + 2 : ℕ) : ℝ)) := by
    exact (hterm.mul hy).div hdenom hdenomOrdered hdenomLoPos
  have hnextTerm : nextTerm.Contains (hMagnitude x (n + 1)) := by
    rw [hMagnitude_succ]
    convert hnextTermRaw using 1
    simp only [k, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  by_cases heven : Even k
  · have hnextSumRaw := hsum.add hnextTerm
    have hnextSum :
        (DyadicInterval.add s.sum nextTerm).Contains
          (alternatingPartial (hMagnitude x) (n + 2)) := by
      rw [show n + 2 = (n + 1) + 1 by omega, hAlternatingPartial_succ]
      rw [show n + 1 = k by rfl, heven.neg_one_pow]
      simpa only [one_mul] using hnextSumRaw
    simpa [hStateStep, nextTerm, denom, k, heven] using And.intro hnextTerm hnextSum
  · have hodd : Odd k := Nat.not_even_iff_odd.mp heven
    have hnextSumRaw := hsum.sub hnextTerm
    have hnextSum :
        (DyadicInterval.sub s.sum nextTerm).Contains
          (alternatingPartial (hMagnitude x) (n + 2)) := by
      rw [show n + 2 = (n + 1) + 1 by omega, hAlternatingPartial_succ]
      rw [show n + 1 = k by rfl, hodd.neg_one_pow]
      simpa only [neg_one_mul, sub_eq_add_neg] using hnextSumRaw
    simpa [hStateStep, nextTerm, denom, k, heven] using And.intro hnextTerm hnextSum

theorem hState_sound {y : DyadicInterval} {x : ℝ} (hy : y.Contains x) (n : ℕ) :
    (hState y n).term.Contains (hMagnitude x n) ∧
      (hState y n).sum.Contains
        (alternatingPartial (hMagnitude x) (n + 1)) := by
  induction n with
  | zero =>
      have hhalf := DyadicInterval.contains_ofRat 1 (by norm_num : (0 : ℤ) < 2)
      constructor
      · simpa [hState, hMagnitude] using hhalf
      · simpa [hState, alternatingPartial, hMagnitude,
          Finset.sum_range_succ] using hhalf
  | succ n ih =>
      simpa [hState] using hStateStep_sound hy ih.1 ih.2

theorem hfunInterval_lower (y : DyadicInterval) :
    (hfunInterval y).lower = (hState y 25).sum.lower := by
  unfold hfunInterval DyadicInterval.lower
  rfl

theorem hfunInterval_upper (y : DyadicInterval) :
    (hfunInterval y).upper = (hState y 24).sum.upper := by
  unfold hfunInterval DyadicInterval.upper
  rfl

theorem hfunInterval_sound {y : DyadicInterval} {x : ℝ}
    (hy : y.Contains x) (hx0 : 0 ≤ x) (hx3 : x ≤ 3) :
    (hfunInterval y).Contains (routeBH x) := by
  have hstate25 := (hState_sound hy 25).2
  have hstate24 := (hState_sound hy 24).2
  constructor
  · rw [hfunInterval_lower]
    exact hstate25.1.trans (by simpa using routeBH_lower_bound hx0 hx3 13)
  · rw [hfunInterval_upper]
    have htaylor : routeBH x ≤ alternatingPartial (hMagnitude x) 25 := by
      simpa using routeBH_upper_bound hx0 hx3 12
    exact htaylor.trans hstate24.2

end Soundness

/-! ## Executable adaptive exponential kernel -/

/-- Exact dyadic enclosure of the checker threshold `1/8`. -/
def expNegEighth : DyadicInterval := DyadicInterval.ofRat 1 8

theorem expNegEighth_hi_pos : 0 < expNegEighth.hi := by
  norm_num [expNegEighth, DyadicInterval.ofRat, ceilDiv, dyadicScale,
    dyadicPrecision]

/--
Adaptive `exp (-x)` evaluator with the same control flow as `expneg` in the supplied checker.
For a valid nonnegative input it repeatedly halves until the upper endpoint is at most `1/8`,
uses the degree-13/12 alternating enclosure, and reverses the range reduction by outward-rounded
squaring.  The negative-input branch makes the Lean definition total; checker calls satisfy the
proved `0 ≤ I.lo` precondition and therefore never take it.
-/
def dyadicExpNeg (I : DyadicInterval) : DyadicInterval :=
  if I.lo < 0 then DyadicInterval.point 0
  else if I.hi ≤ expNegEighth.hi then expNegTaylor I
  else DyadicInterval.sqr (dyadicExpNeg (DyadicInterval.half I))
termination_by Int.natAbs I.hi
decreasing_by
  simp only [DyadicInterval.half]
  have hi2 : 2 ≤ I.hi := by
    have hthreshold := expNegEighth_hi_pos
    omega
  unfold ceilDiv
  omega

theorem half_lo_nonneg {I : DyadicInterval} (hI : 0 ≤ I.lo) :
    0 ≤ (DyadicInterval.half I).lo := by
  simp only [DyadicInterval.half]
  unfold floorDiv
  omega

theorem expNegEighth_upper : expNegEighth.upper = (1 : ℝ) / 8 := by
  norm_num [expNegEighth, DyadicInterval.ofRat, DyadicInterval.upper,
    ceilDiv, dyadicScale, dyadicPrecision]

noncomputable section AdaptiveExpSoundness

theorem dyadicExpNeg_sound {I : DyadicInterval} {x : ℝ}
    (hx : I.Contains x) (hlo : 0 ≤ I.lo) :
    (dyadicExpNeg I).Contains (Real.exp (-x)) := by
  refine dyadicExpNeg.induct
    (motive := fun J => ∀ {u : ℝ}, J.Contains u → 0 ≤ J.lo →
      (dyadicExpNeg J).Contains (Real.exp (-u))) ?_ ?_ ?_ I hx hlo
  · intro J hneg u hu hJlo
    omega
  · intro J hneg hstop u hu hJlo
    rw [dyadicExpNeg, if_neg hneg, if_pos hstop]
    apply expNegTaylor_sound hu
    · have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
      have hloR : (0 : ℝ) ≤ (J.lo : ℝ) := by exact_mod_cast hJlo
      exact (div_nonneg hloR hscale.le).trans hu.1
    · have hupper : J.upper ≤ expNegEighth.upper := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hstop)
          (by exact_mod_cast dyadicScale_pos.le)
      calc
        u ≤ J.upper := hu.2
        _ ≤ expNegEighth.upper := hupper
        _ = (1 : ℝ) / 8 := expNegEighth_upper
        _ ≤ 1 := by norm_num
  · intro J hneg hstop ih u hu hJlo
    rw [dyadicExpNeg, if_neg hneg, if_neg hstop]
    have hxhalf := hu.half
    have hsound := ih hxhalf (half_lo_nonneg hJlo)
    have hsq := hsound.sqr hsound.ordered
    have hexp : Real.exp (-(u / 2)) ^ 2 = Real.exp (-u) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simpa [hexp] using hsq

end AdaptiveExpSoundness

end BerryEsseen
