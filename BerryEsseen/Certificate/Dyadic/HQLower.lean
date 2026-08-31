import BerryEsseen.Certificate.Dyadic.Kernel
import BerryEsseen.Smoothing.PrawitzHQLower
/-!
# Verifier-matching dyadic `hq_lower`

This module implements the exact checker's branch test and outward-rounded operation order.
Its main theorem proves that the returned lower endpoint bounds the true Route B minorant term.
-/

namespace BerryEsseen

noncomputable section

open DyadicInterval


/-- The exact checker's upper enclosure for the certified slope. -/
def checkerKappaUpper : DyadicInterval :=
  DyadicInterval.ofRat 9916191353 100000000000

/-- The exact checker's lower enclosure for the certified slope. -/
def checkerKappaLower : DyadicInterval :=
  DyadicInterval.ofRat 9916191350 100000000000

theorem checkerKappaUpper_contains : checkerKappaUpper.Contains routeBKappaUpper := by
  convert DyadicInterval.contains_ofRat 9916191353
      (by norm_num : (0 : ℤ) < 100000000000) using 1
  norm_num [routeBKappaUpper]

theorem checkerKappaLower_contains : checkerKappaLower.Contains routeBKappaLower := by
  convert DyadicInterval.contains_ofRat 9916191350
      (by norm_num : (0 : ℤ) < 100000000000) using 1
  norm_num [routeBKappaLower]

theorem dyadicContains_div_point {I : DyadicInterval} {x : ℝ}
    (hx : I.Contains x) (n : ℤ) (hn : 0 < n) :
    (DyadicInterval.div I (DyadicInterval.point n)).Contains (x / (n : ℝ)) := by
  have hp := DyadicInterval.contains_point n
  have hlo : 0 < (DyadicInterval.point n).lo := by
    dsimp only [DyadicInterval.point]
    exact mul_pos hn dyadicScale_pos
  exact hx.div hp hp.ordered hlo

/-- The exact operation order used by the high branch of `hq_lower`. -/
def dyadicCosineLossTaylor12 (x : DyadicInterval) : DyadicInterval :=
  let x2 := DyadicInterval.sqr x
  let x4 := DyadicInterval.sqr x2
  let x6 := DyadicInterval.mul x4 x2
  let x8 := DyadicInterval.sqr x4
  let x10 := DyadicInterval.mul x8 x2
  let x12 := DyadicInterval.mul x10 x2
  DyadicInterval.sub
    (DyadicInterval.add
      (DyadicInterval.sub
        (DyadicInterval.add
          (DyadicInterval.sub
            (DyadicInterval.div x2 (DyadicInterval.point 2))
            (DyadicInterval.div x4 (DyadicInterval.point 24)))
          (DyadicInterval.div x6 (DyadicInterval.point 720)))
        (DyadicInterval.div x8 (DyadicInterval.point 40320)))
      (DyadicInterval.div x10 (DyadicInterval.point 3628800)))
    (DyadicInterval.div x12 (DyadicInterval.point 479001600))

theorem dyadicCosineLossTaylor12_sound {x : DyadicInterval} {y : ℝ}
    (hx : x.Contains y) :
    (dyadicCosineLossTaylor12 x).Contains (prawitzCosineLossTaylor12 y) := by
  let x2 := DyadicInterval.sqr x
  let x4 := DyadicInterval.sqr x2
  let x6 := DyadicInterval.mul x4 x2
  let x8 := DyadicInterval.sqr x4
  let x10 := DyadicInterval.mul x8 x2
  let x12 := DyadicInterval.mul x10 x2
  have hx2 : x2.Contains (y ^ 2) := hx.sqr hx.ordered
  have hx4 : x4.Contains ((y ^ 2) ^ 2) := hx2.sqr hx2.ordered
  have hx6 : x6.Contains ((y ^ 2) ^ 2 * y ^ 2) := hx4.mul hx2
  have hx8 : x8.Contains (((y ^ 2) ^ 2) ^ 2) := hx4.sqr hx4.ordered
  have hx10 : x10.Contains (((y ^ 2) ^ 2) ^ 2 * y ^ 2) := hx8.mul hx2
  have hx12 : x12.Contains ((((y ^ 2) ^ 2) ^ 2 * y ^ 2) * y ^ 2) := hx10.mul hx2
  have h2 := dyadicContains_div_point hx2 2 (by norm_num)
  have h24 := dyadicContains_div_point hx4 24 (by norm_num)
  have h720 := dyadicContains_div_point hx6 720 (by norm_num)
  have h40320 := dyadicContains_div_point hx8 40320 (by norm_num)
  have h3628800 := dyadicContains_div_point hx10 3628800 (by norm_num)
  have h479001600 := dyadicContains_div_point hx12 479001600 (by norm_num)
  have hresult := ((((h2.sub h24).add h720).sub h40320).add h3628800).sub h479001600
  change (dyadicCosineLossTaylor12 x).Contains (prawitzCosineLossTaylor12 y)
  simp only [dyadicCosineLossTaylor12]
  convert hresult using 1
  unfold prawitzCosineLossTaylor12
  ring

/-- Verifier-matching implementation of `hq_lower`. -/
def dyadicPrawitzHQLower (t : DyadicInterval) : DyadicInterval :=
  let v := DyadicInterval.mul
    (DyadicInterval.mul (DyadicInterval.point 2) checkerPi) t
  if (DyadicInterval.point 4).lo ≤ v.lo then
    let x := DyadicInterval.mul
      (DyadicInterval.mul (DyadicInterval.point 2) checkerPi)
      (DyadicInterval.sub (DyadicInterval.point 1) t)
    dyadicCosineLossTaylor12 x
  else
    DyadicInterval.mul (DyadicInterval.sqr v)
      (DyadicInterval.sub (DyadicInterval.ofRat 1 2)
        (DyadicInterval.mul checkerKappaUpper v))

theorem dyadicPrawitzHQLowBranch_sound {t : DyadicInterval} {s : ℝ}
    (ht : t.Contains s) :
    let v := DyadicInterval.mul
      (DyadicInterval.mul (DyadicInterval.point 2) checkerPi) t
    (DyadicInterval.mul (DyadicInterval.sqr v)
      (DyadicInterval.sub (DyadicInterval.ofRat 1 2)
        (DyadicInterval.mul checkerKappaUpper v))).Contains
      ((2 * Real.pi * s) ^ 2 *
        ((1 : ℝ) / 2 - routeBKappaUpper * (2 * Real.pi * s))) := by
  let v := DyadicInterval.mul
    (DyadicInterval.mul (DyadicInterval.point 2) checkerPi) t
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hv : v.Contains ((2 * Real.pi) * s) :=
    (htwo.mul checkerPi_contains_pi).mul ht
  have hv2 := hv.sqr hv.ordered
  have hhalf : (DyadicInterval.ofRat 1 2).Contains ((1 : ℝ) / 2) :=
    by simpa only [Int.cast_one, Int.cast_ofNat] using
      DyadicInterval.contains_ofRat 1 (b := 2) (by norm_num)
  have hline := hhalf.sub (checkerKappaUpper_contains.mul hv)
  have hresult := hv2.mul hline
  dsimp only [v]
  exact hresult

theorem dyadicPrawitzHQHighBranch_sound {t : DyadicInterval} {s : ℝ}
    (ht : t.Contains s) :
    let x := DyadicInterval.mul
      (DyadicInterval.mul (DyadicInterval.point 2) checkerPi)
      (DyadicInterval.sub (DyadicInterval.point 1) t)
    (dyadicCosineLossTaylor12 x).Contains
      (prawitzCosineLossTaylor12 (2 * Real.pi * (1 - s))) := by
  let x := DyadicInterval.mul
    (DyadicInterval.mul (DyadicInterval.point 2) checkerPi)
    (DyadicInterval.sub (DyadicInterval.point 1) t)
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have hx : x.Contains ((2 * Real.pi) * (1 - s)) :=
    (htwo.mul checkerPi_contains_pi).mul (hone.sub ht)
  dsimp only [x]
  exact dyadicCosineLossTaylor12_sound hx

theorem dyadicPrawitzHQLower_lower_le {t : DyadicInterval} {s : ℝ}
    (ht : t.Contains s) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (dyadicPrawitzHQLower t).lower ≤
      (2 * Real.pi * s) ^ 2 *
        routeBMinorant routeBKappa routeBTheta (2 * Real.pi * s) := by
  let v := DyadicInterval.mul
    (DyadicInterval.mul (DyadicInterval.point 2) checkerPi) t
  by_cases hbranch : (DyadicInterval.point 4).lo ≤ v.lo
  · have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
      simpa using DyadicInterval.contains_point (2 : ℤ)
    have hv : v.Contains ((2 * Real.pi) * s) :=
      (htwo.mul checkerPi_contains_pi).mul ht
    have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
    have hlo : (DyadicInterval.point 4).lower ≤ v.lower := by
      unfold DyadicInterval.lower
      apply (div_le_div_iff_of_pos_right hscale).2
      exact_mod_cast hbranch
    have hv4 : (4 : ℝ) ≤ 2 * Real.pi * s := by
      have := hlo.trans hv.1
      simpa [DyadicInterval.lower, DyadicInterval.point, dyadicScale_pos.ne'] using this
    unfold dyadicPrawitzHQLower
    dsimp only [v] at hbranch ⊢
    rw [if_pos hbranch]
    exact (dyadicPrawitzHQHighBranch_sound ht).1.trans
      (prawitzHQHighBranch_le hs1 hv4)
  · unfold dyadicPrawitzHQLower
    dsimp only [v] at hbranch ⊢
    rw [if_neg hbranch]
    exact (dyadicPrawitzHQLowBranch_sound ht).1.trans
      (prawitzHQLowBranch_le hs0 hs1)

end

end BerryEsseen
