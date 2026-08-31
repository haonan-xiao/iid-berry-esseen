import BerryEsseen.Certificate.LargeN.Cache
/-!
# Direct large-`n` parameter regions

The supplied certificate parametrizes the two regions away from `L = 0` by
unit squares.  This module records those exact dyadic maps and proves that
their interval evaluations contain the corresponding real maps.
-/

namespace BerryEsseen

open DyadicInterval

inductive DyadicRouteBLargeDirectRegion where
  | middle
  | upper
deriving DecidableEq, Repr

def dyadicRouteBUnitInterval : DyadicInterval := ⟨0, dyadicScale⟩

noncomputable def routeBLargeDirectRegionL
    (region : DyadicRouteBLargeDirectRegion) (x : ℝ) : ℝ :=
  match region with
  | .middle => (1 : ℝ) / 16 + x * ((1 : ℝ) / 10 - (1 : ℝ) / 16)
  | .upper => (1 : ℝ) / 10 + x * ((56 : ℝ) / 45 - (1 : ℝ) / 10)

noncomputable def routeBLargeDirectRegionR
    (region : DyadicRouteBLargeDirectRegion) (x z : ℝ) : ℝ :=
  match region with
  | .middle => 1 + z
  | .upper => 1 + z / (10 * routeBLargeDirectRegionL .upper x)

def dyadicRouteBLargeDirectRegionL
    (region : DyadicRouteBLargeDirectRegion)
    (x : DyadicInterval) : DyadicInterval :=
  match region with
  | .middle =>
      DyadicInterval.add (DyadicInterval.ofRat 1 16)
        (DyadicInterval.mul x
          (DyadicInterval.sub (DyadicInterval.ofRat 1 10)
            (DyadicInterval.ofRat 1 16)))
  | .upper =>
      DyadicInterval.add (DyadicInterval.ofRat 1 10)
        (DyadicInterval.mul x
          (DyadicInterval.sub (DyadicInterval.ofRat 56 45)
            (DyadicInterval.ofRat 1 10)))

def dyadicRouteBLargeDirectRegionR
    (region : DyadicRouteBLargeDirectRegion)
    (x z : DyadicInterval) : DyadicInterval :=
  match region with
  | .middle => DyadicInterval.add (DyadicInterval.point 1) z
  | .upper =>
      let L := dyadicRouteBLargeDirectRegionL .upper x
      DyadicInterval.add (DyadicInterval.point 1)
        (DyadicInterval.div z
          (DyadicInterval.mul (DyadicInterval.point 10) L))

theorem dyadicRouteBUnitInterval_contains
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    dyadicRouteBUnitInterval.Contains x := by
  constructor
  · simpa [dyadicRouteBUnitInterval, DyadicInterval.Contains,
      DyadicInterval.lower] using hx0
  · simpa [dyadicRouteBUnitInterval, DyadicInterval.Contains,
      DyadicInterval.upper, dyadicScale_pos.ne'] using hx1

noncomputable section

theorem dyadicRouteBLargeDirectRegionL_contains
    {region : DyadicRouteBLargeDirectRegion}
    {x : DyadicInterval} {xR : ℝ} (hx : x.Contains xR) :
    (dyadicRouteBLargeDirectRegionL region x).Contains
      (routeBLargeDirectRegionL region xR) := by
  have h16 := DyadicInterval.contains_ofRat 1 (b := 16) (by norm_num)
  have h10 := DyadicInterval.contains_ofRat 1 (b := 10) (by norm_num)
  have h56 := DyadicInterval.contains_ofRat 56 (b := 45) (by norm_num)
  cases region with
  | middle =>
      simpa [dyadicRouteBLargeDirectRegionL, routeBLargeDirectRegionL] using
        h16.add (hx.mul (h10.sub h16))
  | upper =>
      simpa [dyadicRouteBLargeDirectRegionL, routeBLargeDirectRegionL] using
        h10.add (hx.mul (h56.sub h10))

theorem dyadicPointTen_mul_lo_pos
    {I : DyadicInterval} (hI : I.Ordered) (hpos : 0 < I.lo) :
    0 < (DyadicInterval.mul (DyadicInterval.point 10) I).lo := by
  change I.lo ≤ I.hi at hI
  rw [← DyadicInterval.mulPoint_eq_mul]
  unfold DyadicInterval.mulPoint
  rw [if_pos ⟨by norm_num, hI⟩]
  dsimp only
  omega

theorem dyadicRouteBLargeDirectRegionR_contains
    {region : DyadicRouteBLargeDirectRegion}
    {x z : DyadicInterval} {xR zR : ℝ}
    (hx : x.Contains xR) (hz : z.Contains zR)
    (hLPos : 0 < (dyadicRouteBLargeDirectRegionL region x).lo) :
    (dyadicRouteBLargeDirectRegionR region x z).Contains
      (routeBLargeDirectRegionR region xR zR) := by
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  cases region with
  | middle =>
      simpa [dyadicRouteBLargeDirectRegionR, routeBLargeDirectRegionR] using
        hone.add hz
  | upper =>
      have hL :=
        dyadicRouteBLargeDirectRegionL_contains
          (region := DyadicRouteBLargeDirectRegion.upper) hx
      have hten : (DyadicInterval.point 10).Contains (10 : ℝ) := by
        simpa using DyadicInterval.contains_point (10 : ℤ)
      have hden := hten.mul hL
      have hdenPos :
          0 < (DyadicInterval.mul (DyadicInterval.point 10)
            (dyadicRouteBLargeDirectRegionL .upper x)).lo :=
        dyadicPointTen_mul_lo_pos hL.ordered hLPos
      have hquot := hz.div hden hden.ordered hdenPos
      simpa [dyadicRouteBLargeDirectRegionR, routeBLargeDirectRegionR] using
        hone.add hquot

end

end BerryEsseen
