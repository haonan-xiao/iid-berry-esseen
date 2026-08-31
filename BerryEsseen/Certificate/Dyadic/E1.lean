import BerryEsseen.Smoothing.PrawitzE1
import BerryEsseen.Certificate.Dyadic.Darboux
/-!
# Exact dyadic implementation of `E1up`

This module mirrors the supplied checker's 769-point composite trapezoidal loop, including endpoint
half-weights, the `[24, ∞)` tail term, replacement of the parameter interval by its lower endpoint,
and the adaptive `expneg` operation order.  Its final theorem bounds the analytic exponential
integral for every real parameter enclosed by the input interval.
-/

open Finset

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 100000

def routeBE1NY : ℕ := 24 * 32

def routeBE1Dy : DyadicInterval := DyadicInterval.ofRat 1 32

def dyadicE1Grid (j : ℕ) : DyadicInterval :=
  DyadicInterval.mul (DyadicInterval.point (Int.ofNat j)) routeBE1Dy

noncomputable def routeBE1WeightedTerm (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 ∨ j = routeBE1NY then f ((j : ℝ) / 32) / 2
  else f ((j : ℝ) / 32)

theorem routeBE1_weighted_sum_eq (f : ℝ → ℝ) :
    (∑ j ∈ Finset.range (routeBE1NY + 1), routeBE1WeightedTerm f j) =
      (f 0 + f 24) / 2 +
        ∑ k ∈ Finset.range (routeBE1NY - 1), f (((k + 1 : ℕ) : ℝ) / 32) := by
  let term := routeBE1WeightedTerm f
  have hinterior :
      (∑ k ∈ Finset.range (routeBE1NY - 1), term (k + 1)) =
        ∑ k ∈ Finset.range (routeBE1NY - 1), f (((k + 1 : ℕ) : ℝ) / 32) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hklt := Finset.mem_range.mp hk
    have hk0 : k + 1 ≠ 0 := by omega
    have hkN : k + 1 ≠ routeBE1NY := by
      norm_num [routeBE1NY] at hklt ⊢
      omega
    simp only [term, routeBE1WeightedTerm, if_neg (not_or_intro hk0 hkN)]
  calc
    (∑ j ∈ Finset.range (routeBE1NY + 1), routeBE1WeightedTerm f j) =
        ∑ j ∈ Finset.range routeBE1NY, term j + term routeBE1NY := by
      simpa only [term] using Finset.sum_range_succ term routeBE1NY
    _ = term 0 + ∑ k ∈ Finset.range (routeBE1NY - 1), term (k + 1) +
        term routeBE1NY := by
      norm_num [routeBE1NY]
      rw [Finset.sum_range_succ']
      ring
    _ = f 0 / 2 +
        ∑ k ∈ Finset.range (routeBE1NY - 1), f (((k + 1 : ℕ) : ℝ) / 32) +
          f 24 / 2 := by
      rw [hinterior]
      norm_num [term, routeBE1WeightedTerm, routeBE1NY]
    _ = (f 0 + f 24) / 2 +
        ∑ k ∈ Finset.range (routeBE1NY - 1), f (((k + 1 : ℕ) : ℝ) / 32) := by
      ring

theorem routeBE1_trapezoidal_eq_weighted (f : ℝ → ℝ) :
    trapezoidal_integral f routeBE1NY 0 24 =
      (1 / 32 : ℝ) *
        ∑ j ∈ Finset.range (routeBE1NY + 1), routeBE1WeightedTerm f j := by
  rw [routeBE1_weighted_sum_eq]
  unfold trapezoidal_integral
  norm_num [routeBE1NY]
  congr 2
  funext k
  congr 1
  ring

def dyadicE1Exp (j : ℕ) : DyadicInterval :=
  dyadicExpNeg (dyadicE1Grid j)

def dyadicLowerPoint (I : DyadicInterval) : DyadicInterval := ⟨I.lo, I.lo⟩

def dyadicE1Term (xx : DyadicInterval) (j : ℕ) : DyadicInterval :=
  let y := dyadicE1Grid j
  let f := DyadicInterval.div (dyadicE1Exp j) (DyadicInterval.add xx y)
  if j = 0 ∨ j = routeBE1NY then
    DyadicInterval.div f (DyadicInterval.point 2)
  else f

def dyadicE1Sum (xx : DyadicInterval) : DyadicInterval :=
  intervalNatSum (dyadicE1Term xx) (routeBE1NY + 1)

def dyadicE1Trapezoid (xx : DyadicInterval) : DyadicInterval :=
  DyadicInterval.mul routeBE1Dy (dyadicE1Sum xx)

def dyadicE1Tail (xx : DyadicInterval) : DyadicInterval :=
  DyadicInterval.div (dyadicE1Exp routeBE1NY)
    (DyadicInterval.add xx (DyadicInterval.point 24))

/-- Exact Lean transcription of the checker's `E1up` routine. -/
def dyadicE1Up (x : DyadicInterval) : DyadicInterval :=
  let xx := dyadicLowerPoint x
  let integ := DyadicInterval.add (dyadicE1Trapezoid xx) (dyadicE1Tail xx)
  DyadicInterval.mul (dyadicExpNeg xx) integ

noncomputable section

theorem dyadicLowerPoint_contains (I : DyadicInterval) :
    (dyadicLowerPoint I).Contains I.lower := by
  constructor <;> rfl

theorem dyadicE1Grid_lo_nonneg (j : ℕ) : 0 ≤ (dyadicE1Grid j).lo := by
  simp [dyadicE1Grid, routeBE1Dy, DyadicInterval.mul,
    DyadicInterval.point, DyadicInterval.ofRat, cornerMinInt,
    floorDiv, ceilDiv, dyadicScale, dyadicPrecision]
  omega

theorem dyadicE1Grid_sound (j : ℕ) :
    (dyadicE1Grid j).Contains ((j : ℝ) / 32) := by
  have hj := DyadicInterval.contains_point (Int.ofNat j)
  have hdy := DyadicInterval.contains_ofRat 1 (by norm_num : (0 : ℤ) < 32)
  simpa [dyadicE1Grid, routeBE1Dy] using hj.mul hdy

theorem dyadicE1Exp_sound (j : ℕ) :
    (dyadicE1Exp j).Contains (Real.exp (-((j : ℝ) / 32))) := by
  exact dyadicExpNeg_sound (dyadicE1Grid_sound j) (dyadicE1Grid_lo_nonneg j)

theorem dyadicE1Term_sound {xx : DyadicInterval} {x₀ : ℝ}
    (hxx : xx.Contains x₀) (hxxLo : 0 < xx.lo) (j : ℕ) :
    (dyadicE1Term xx j).Contains (routeBE1WeightedTerm (routeBE1Integrand x₀) j) := by
  let denom := DyadicInterval.add xx (dyadicE1Grid j)
  have hy := dyadicE1Grid_sound j
  have he := dyadicE1Exp_sound j
  have hdenom := hxx.add hy
  have hdenomLo : 0 < denom.lo := by
    change 0 < xx.lo + (dyadicE1Grid j).lo
    have hylo := dyadicE1Grid_lo_nonneg j
    omega
  have hf : (DyadicInterval.div (dyadicE1Exp j) denom).Contains
      (routeBE1Integrand x₀ ((j : ℝ) / 32)) := by
    simpa only [denom, routeBE1Integrand] using
      he.div hdenom hdenom.ordered hdenomLo
  by_cases hend : j = 0 ∨ j = routeBE1NY
  · have htwo := DyadicInterval.contains_point (2 : ℤ)
    have htwoLo : 0 < (DyadicInterval.point 2).lo := by
      exact mul_pos (by norm_num) dyadicScale_pos
    simp only [dyadicE1Term, routeBE1WeightedTerm, hend, if_pos]
    simpa only [denom] using hf.div htwo htwo.ordered htwoLo
  · simp only [dyadicE1Term, routeBE1WeightedTerm, hend, if_false]
    simpa only [denom] using hf

theorem dyadicE1Sum_sound {xx : DyadicInterval} {x₀ : ℝ}
    (hxx : xx.Contains x₀) (hxxLo : 0 < xx.lo) :
    (dyadicE1Sum xx).Contains
      (∑ j ∈ Finset.range (routeBE1NY + 1),
        routeBE1WeightedTerm (routeBE1Integrand x₀) j) := by
  exact intervalNatSum_sound (routeBE1NY + 1)
    (fun j hj => dyadicE1Term_sound hxx hxxLo j)

theorem dyadicE1Trapezoid_sound {xx : DyadicInterval} {x₀ : ℝ}
    (hxx : xx.Contains x₀) (hxxLo : 0 < xx.lo) :
    (dyadicE1Trapezoid xx).Contains
      (trapezoidal_integral (routeBE1Integrand x₀) routeBE1NY 0 24) := by
  have hdy := DyadicInterval.contains_ofRat 1 (by norm_num : (0 : ℤ) < 32)
  have hsum := dyadicE1Sum_sound hxx hxxLo
  have hmul := hdy.mul hsum
  rw [routeBE1_trapezoidal_eq_weighted]
  simpa [dyadicE1Trapezoid, routeBE1Dy] using hmul

theorem dyadicE1Tail_sound {xx : DyadicInterval} {x₀ : ℝ}
    (hxx : xx.Contains x₀) (hxxLo : 0 < xx.lo) :
    (dyadicE1Tail xx).Contains (Real.exp (-24) / (x₀ + 24)) := by
  have he := dyadicE1Exp_sound routeBE1NY
  have he24 : (dyadicE1Exp routeBE1NY).Contains (Real.exp (-24)) := by
    norm_num [routeBE1NY] at he
    exact he
  have h24 := DyadicInterval.contains_point (24 : ℤ)
  have hdenom := hxx.add h24
  have hdenomLo : 0 < (DyadicInterval.add xx (DyadicInterval.point 24)).lo := by
    dsimp [DyadicInterval.add, DyadicInterval.point]
    have hscale := dyadicScale_pos
    omega
  simpa [dyadicE1Tail] using he24.div hdenom hdenom.ordered hdenomLo

theorem dyadicE1Up_sound {x : DyadicInterval} (hxLo : 0 < x.lo) :
    (dyadicE1Up x).Contains (routeBE1CheckerUpper x.lower) := by
  let xx := dyadicLowerPoint x
  have hxx : xx.Contains x.lower := dyadicLowerPoint_contains x
  have hxxLo : 0 < xx.lo := by simpa [xx, dyadicLowerPoint] using hxLo
  have hexp := dyadicExpNeg_sound hxx hxxLo.le
  have htrap := dyadicE1Trapezoid_sound hxx hxxLo
  have htail := dyadicE1Tail_sound hxx hxxLo
  have hinteg := htrap.add htail
  simpa [dyadicE1Up, xx, routeBE1CheckerUpper, routeBE1NY] using hexp.mul hinteg

theorem routeBE1_le_dyadicE1Up_upper {x : DyadicInterval} {xR : ℝ}
    (hx : x.Contains xR) (hxLo : 0 < x.lo) :
    routeBE1 xR ≤ (dyadicE1Up x).upper := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  have hxLowerPos : 0 < x.lower := div_pos (by exact_mod_cast hxLo) hscale
  have hmono : routeBE1 xR ≤ routeBE1 x.lower := by
    have hxRPos : 0 < xR := hxLowerPos.trans_le hx.1
    exact routeBE1_antitoneOn hxLowerPos hxRPos hx.1
  exact hmono.trans <|
    (routeBE1_le_checkerUpper hxLowerPos).trans (dyadicE1Up_sound hxLo).2

end

end BerryEsseen
