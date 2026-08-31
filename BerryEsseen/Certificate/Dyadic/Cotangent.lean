import BerryEsseen.Certificate.Dyadic.Interval
import BerryEsseen.Smoothing.PrawitzCotangentBounds
/-!
# Dyadic cotangent envelopes

This module implements the exact checker's `PI`, `dlow`, and `dup` expressions and connects
their outward-rounded endpoints to the analytic cotangent bounds.  The multiplication order is
the one used by the supplied C++ verifier.
-/

namespace BerryEsseen

open DyadicInterval

/-- The consecutive precision-48 dyadics used by the exact checker to enclose `π`. -/
def checkerPi : DyadicInterval :=
  ⟨884279719003555, 884279719003556⟩

theorem checkerPi_contains_pi : checkerPi.Contains Real.pi := by
  constructor
  · have hpi : piLower20 < Real.pi := Real.pi_gt_d20
    have hdyadic : checkerPi.lower < piLower20 := by
      norm_num [checkerPi, DyadicInterval.lower, dyadicScale, dyadicPrecision, piLower20]
    exact hdyadic.le.trans hpi.le
  · have hpi : Real.pi < piUpper20 := Real.pi_lt_d20
    have hdyadic : piUpper20 < checkerPi.upper := by
      norm_num [checkerPi, DyadicInterval.upper, dyadicScale, dyadicPrecision, piUpper20]
    exact hpi.le.trans hdyadic.le

/-- The exact checker's lower polynomial `dlow`. -/
def dyadicCotGapLower (x : DyadicInterval) : DyadicInterval :=
  let x2 := DyadicInterval.sqr x
  let x3 := DyadicInterval.mul x x2
  let x5 := DyadicInterval.mul x3 x2
  DyadicInterval.add
    (DyadicInterval.add
      (DyadicInterval.div x (DyadicInterval.point 3))
      (DyadicInterval.div x3 (DyadicInterval.point 45)))
    (DyadicInterval.div (DyadicInterval.mul (DyadicInterval.point 2) x5)
      (DyadicInterval.point 945))

theorem dyadicCotGapLower_sound {x : DyadicInterval} {xr : ℝ} (hx : x.Contains xr) :
    (dyadicCotGapLower x).Contains (prawitzCotGapLower xr) := by
  let x2 := DyadicInterval.sqr x
  let x3 := DyadicInterval.mul x x2
  let x5 := DyadicInterval.mul x3 x2
  have hx2 : x2.Contains (xr ^ 2) := hx.sqr hx.ordered
  have hx3 : x3.Contains (xr * xr ^ 2) := hx.mul hx2
  have hx5 : x5.Contains ((xr * xr ^ 2) * xr ^ 2) := hx3.mul hx2
  have h3 := DyadicInterval.contains_point (3 : ℤ)
  have h45 := DyadicInterval.contains_point (45 : ℤ)
  have h945 := DyadicInterval.contains_point (945 : ℤ)
  have h3pos : 0 < (DyadicInterval.point 3).lo := by
    norm_num [DyadicInterval.point, dyadicScale, dyadicPrecision]
  have h45pos : 0 < (DyadicInterval.point 45).lo := by
    norm_num [DyadicInterval.point, dyadicScale, dyadicPrecision]
  have h945pos : 0 < (DyadicInterval.point 945).lo := by
    norm_num [DyadicInterval.point, dyadicScale, dyadicPrecision]
  have ht1 := hx.div h3 h3.ordered h3pos
  have ht2 := hx3.div h45 h45.ordered h45pos
  have htwo := DyadicInterval.contains_point (2 : ℤ)
  have ht3 := (htwo.mul hx5).div h945 h945.ordered h945pos
  have hsum := (ht1.add ht2).add ht3
  change (dyadicCotGapLower x).Contains (prawitzCotGapLower xr)
  simp only [dyadicCotGapLower]
  convert hsum using 1
  unfold prawitzCotGapLower
  ring

/-- The exact checker's rational upper expression `dup`. -/
def dyadicCotGapUpper (u : DyadicInterval) : DyadicInterval :=
  let x := DyadicInterval.mul checkerPi u
  let dl := dyadicCotGapLower x
  let x2 := DyadicInterval.sqr x
  let x7 := DyadicInterval.mul
    (DyadicInterval.mul (DyadicInterval.mul x x2) x2) x2
  let denom := DyadicInterval.mul (DyadicInterval.point 4725)
    (DyadicInterval.sub (DyadicInterval.point 1) (DyadicInterval.sqr u))
  DyadicInterval.add dl (DyadicInterval.div x7 denom)

theorem dyadicCotGapUpper_sound {u : DyadicInterval} {s : ℝ}
    (hu : u.Contains s)
    (hdenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1) (DyadicInterval.sqr u))).lo) :
    (dyadicCotGapUpper u).Contains (prawitzCotGapUpperAt s) := by
  let x := DyadicInterval.mul checkerPi u
  let dl := dyadicCotGapLower x
  let x2 := DyadicInterval.sqr x
  let x7 := DyadicInterval.mul
    (DyadicInterval.mul (DyadicInterval.mul x x2) x2) x2
  let denom := DyadicInterval.mul (DyadicInterval.point 4725)
    (DyadicInterval.sub (DyadicInterval.point 1) (DyadicInterval.sqr u))
  have hx : x.Contains (Real.pi * s) := checkerPi_contains_pi.mul hu
  have hdl : dl.Contains (prawitzCotGapLower (Real.pi * s)) :=
    dyadicCotGapLower_sound hx
  have hx2 : x2.Contains ((Real.pi * s) ^ 2) := hx.sqr hx.ordered
  have hx3 : (DyadicInterval.mul x x2).Contains ((Real.pi * s) * (Real.pi * s) ^ 2) :=
    hx.mul hx2
  have hx5 : (DyadicInterval.mul (DyadicInterval.mul x x2) x2).Contains
      (((Real.pi * s) * (Real.pi * s) ^ 2) * (Real.pi * s) ^ 2) := hx3.mul hx2
  have hx7 : x7.Contains
      ((((Real.pi * s) * (Real.pi * s) ^ 2) * (Real.pi * s) ^ 2) *
        (Real.pi * s) ^ 2) := hx5.mul hx2
  have hu2 := hu.sqr hu.ordered
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have h4725 : (DyadicInterval.point 4725).Contains (4725 : ℝ) := by
    simpa using DyadicInterval.contains_point (4725 : ℤ)
  have hden : denom.Contains (4725 * (1 - s ^ 2)) := h4725.mul (hone.sub hu2)
  have hquot := hx7.div hden hden.ordered hdenom
  have hsum := hdl.add hquot
  change (dyadicCotGapUpper u).Contains (prawitzCotGapUpperAt s)
  simp only [dyadicCotGapUpper]
  convert hsum using 1
  unfold prawitzCotGapUpperAt
  ring

/-- The lower endpoint returned by `dlow(PI*u)` is a valid lower bound for the actual
cotangent gap. -/
theorem dyadicCotGapLower_lower_le {u : DyadicInterval} {s : ℝ}
    (hu : u.Contains s) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (dyadicCotGapLower (DyadicInterval.mul checkerPi u)).lower ≤
      1 / (Real.pi * s) - Real.cot (Real.pi * s) := by
  exact (dyadicCotGapLower_sound (checkerPi_contains_pi.mul hu)).1.trans
    (prawitzCotGapLower_le hs0 hs1)

/-- The upper endpoint returned by `dup(u)` is a valid upper bound for the actual
cotangent gap. -/
theorem cotGap_le_dyadicCotGapUpper_upper {u : DyadicInterval} {s : ℝ}
    (hu : u.Contains s) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hdenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1) (DyadicInterval.sqr u))).lo) :
    1 / (Real.pi * s) - Real.cot (Real.pi * s) ≤ (dyadicCotGapUpper u).upper := by
  exact (prawitzCotGap_le_upper hs0 hs1).trans (dyadicCotGapUpper_sound hu hdenom).2

end BerryEsseen
