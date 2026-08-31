import BerryEsseen.Smoothing.PrawitzLargeNSmallCell
import BerryEsseen.Certificate.LargeN.Cell
import BerryEsseen.Certificate.Dyadic.GaussianTail
/-!
# Exact cells for the endpoint-regular large-`n` region

This module transcribes the supplied checker's `ycells` and `tail_small`
arithmetic.  The cell variable is `y ∈ [0,4]`; the parameter-dependent
frequencies are `t = L*y` and `1 - L*y`.
-/

namespace BerryEsseen

open DyadicInterval
open MeasureTheory intervalIntegral

def dyadicRouteBLargeSmallYCell (N i : ℕ) : DyadicInterval :=
  dyadicPrawitzCellRange (DyadicInterval.point 0)
    (DyadicInterval.point 4) N i

def dyadicRouteBLargeSmallYWidth (N i : ℕ) : DyadicInterval :=
  dyadicPrawitzCellRawWidth (DyadicInterval.point 0)
    (DyadicInterval.point 4) N i

def dyadicRouteBLargeSmallT
    (L y : DyadicInterval) : DyadicInterval :=
  DyadicInterval.mul L y

def dyadicRouteBLargeSmallV
    (L y : DyadicInterval) : DyadicInterval :=
  DyadicInterval.mul dyadicRouteBTwoPi (dyadicRouteBLargeSmallT L y)

def dyadicRouteBLargeSmallYV (y : DyadicInterval) : DyadicInterval :=
  DyadicInterval.mul dyadicRouteBTwoPi y

def dyadicRouteBLargeSmallLowLine
    (L y : DyadicInterval) : DyadicInterval :=
  DyadicInterval.maxZero
    (DyadicInterval.sub (DyadicInterval.ofRat 1 2)
      (DyadicInterval.mul checkerKappaUpper
        (dyadicRouteBLargeSmallV L y)))

def dyadicRouteBLargeSmallLowQRaw
    (L r y : DyadicInterval) : DyadicInterval :=
  DyadicInterval.div
    (DyadicInterval.mul (DyadicInterval.sqr (dyadicRouteBLargeSmallYV y))
      (dyadicCellLowerPoint (dyadicRouteBLargeSmallLowLine L y)))
    (DyadicInterval.sqr r)

def dyadicRouteBLargeSmallLowQ
    (L r y : DyadicInterval) : DyadicInterval :=
  DyadicInterval.maxZero (dyadicRouteBLargeSmallLowQRaw L r y)

def dyadicRouteBLargeSmallAlphaExp
    (L r y : DyadicInterval) : DyadicInterval :=
  dyadicExpNeg (DyadicInterval.mul dyadicRouteBLargeAlpha
    (dyadicRouteBLargeSmallLowQ L r y))

def dyadicRouteBLargeSmallNormalArg
    (r y : DyadicInterval) : DyadicInterval :=
  DyadicInterval.div (DyadicInterval.sqr (dyadicRouteBLargeSmallYV y))
    (DyadicInterval.mul (DyadicInterval.point 2) (DyadicInterval.sqr r))

def dyadicRouteBLargeSmallNormal
    (r y : DyadicInterval) : DyadicInterval :=
  dyadicExpNeg (dyadicRouteBLargeSmallNormalArg r y)

def dyadicRouteBLargeSmallP0
    (L y : DyadicInterval) : DyadicInterval :=
  DyadicInterval.mul dyadicRouteBTwoPi
    (dyadicPrawitzK0Upper (dyadicRouteBLargeSmallT L y))

def dyadicRouteBLargeSmallD
    (L r y : DyadicInterval) : DyadicInterval :=
  dyadicPrawitzDstar r (dyadicRouteBLargeSmallV L y)

/-- Exact operation order of the checker's endpoint-regular first term. -/
def dyadicRouteBLargeSmallF1
    (L r y : DyadicInterval) : DyadicInterval :=
  let scale := DyadicInterval.div
    (DyadicInterval.mul (DyadicInterval.point 8)
      (DyadicInterval.sqr checkerPi))
    (powi r 3)
  let withY := DyadicInterval.mul scale (DyadicInterval.sqr y)
  let withP0 := DyadicInterval.mul withY
    (dyadicRouteBLargeSmallP0 L y)
  DyadicInterval.mul withP0
    (DyadicInterval.mul (dyadicRouteBLargeSmallD L r y)
      (dyadicRouteBLargeSmallAlphaExp L r y))

def dyadicRouteBLargeSmallF3
    (L r y : DyadicInterval) : DyadicInterval :=
  DyadicInterval.mul
    (dyadicPrawitzKD2Upper (dyadicRouteBLargeSmallT L y))
    (dyadicRouteBLargeSmallNormal r y)

def dyadicRouteBLargeSmallCosRatio
    (L y : DyadicInterval) : DyadicInterval :=
  let x := dyadicRouteBLargeSmallV L y
  let x2 := DyadicInterval.sqr x
  let x4 := DyadicInterval.sqr x2
  let x6 := DyadicInterval.mul x4 x2
  let x8 := DyadicInterval.sqr x4
  let x10 := DyadicInterval.mul x8 x2
  DyadicInterval.sub
    (DyadicInterval.add
      (DyadicInterval.sub
        (DyadicInterval.add
          (DyadicInterval.sub (DyadicInterval.ofRat 1 2)
            (DyadicInterval.divPoint x2 24))
          (DyadicInterval.divPoint x4 720))
        (DyadicInterval.divPoint x6 40320))
      (DyadicInterval.divPoint x8 3628800))
    (DyadicInterval.divPoint x10 479001600)

def dyadicRouteBLargeSmallHighQRaw
    (L r y : DyadicInterval) : DyadicInterval :=
  DyadicInterval.div
    (DyadicInterval.mul (DyadicInterval.sqr (dyadicRouteBLargeSmallYV y))
      (dyadicRouteBLargeSmallCosRatio L y))
    (DyadicInterval.sqr r)

def dyadicRouteBLargeSmallHighQ
    (L r y : DyadicInterval) : DyadicInterval :=
  DyadicInterval.maxZero (dyadicRouteBLargeSmallHighQRaw L r y)

def dyadicRouteBLargeSmallF2
    (L r y : DyadicInterval) : DyadicInterval :=
  let t := dyadicRouteBLargeSmallT L y
  let highT := DyadicInterval.sub (DyadicInterval.point 1) t
  DyadicInterval.mul (dyadicPrawitzKH2Upper highT)
    (dyadicExpNeg (dyadicRouteBLargeSmallHighQ L r y))

def dyadicRouteBLargeSmallCellValue
    (L r y : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add
    (DyadicInterval.add (dyadicRouteBLargeSmallF1 L r y)
      (dyadicRouteBLargeSmallF3 L r y))
    (dyadicRouteBLargeSmallF2 L r y)

def dyadicRouteBLargeSmallFiniteSum
    (L r : DyadicInterval) (N : ℕ) : DyadicInterval :=
  intervalNatSum (fun i =>
    DyadicInterval.mul (dyadicRouteBLargeSmallYWidth N i)
      (dyadicRouteBLargeSmallCellValue L r
        (dyadicRouteBLargeSmallYCell N i))) N

def dyadicRouteBLargeSmallOmission : DyadicInterval :=
  DyadicInterval.ofRat 3 100000000000

def dyadicRouteBLargeSmallBound
    (L r : DyadicInterval) (N : ℕ) : DyadicInterval :=
  DyadicInterval.add (dyadicRouteBLargeSmallFiniteSum L r N)
    dyadicRouteBLargeSmallOmission

/-- Parameter-box conditions needed by the endpoint-regular evaluator.  They
are stated only in exact dyadic arithmetic, so a generated certificate can be
rechecked by the kernel. -/
structure DyadicLargeSmallBoxAdmissible
    (L r : DyadicInterval) : Prop where
  LNonnegative : 0 ≤ L.lo
  LLeSixteenth : L.hi ≤ (DyadicInterval.ofRat 1 16).lo
  rPos : 0 < r.lo
  oneLeR : (DyadicInterval.point 1).hi ≤ r.lo
  rLeTwo : r.hi ≤ (DyadicInterval.point 2).lo
  rSqPos : 0 < (DyadicInterval.sqr r).lo
  normalDenPos : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
    (DyadicInterval.sqr r)).lo
  rCubePos : 0 < (powi r 3).lo

/-- Cell-local conditions needed for the three exact endpoint-regular terms. -/
structure DyadicLargeSmallCellAdmissible
    (L r y : DyadicInterval) : Prop where
  alphaArgNonnegative : 0 ≤ (DyadicInterval.mul dyadicRouteBLargeAlpha
    (dyadicRouteBLargeSmallLowQ L r y)).lo
  normalArgNonnegative : 0 ≤ (dyadicRouteBLargeSmallNormalArg r y).lo
  highArgNonnegative : 0 ≤ (dyadicRouteBLargeSmallHighQ L r y).lo
  lowCotDenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
    (DyadicInterval.sub (DyadicInterval.point 1)
      (DyadicInterval.sqr (dyadicRouteBLargeSmallT L y)))).lo
  highCotDenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
    (DyadicInterval.sub (DyadicInterval.point 1)
      (DyadicInterval.sqr (DyadicInterval.sub (DyadicInterval.point 1)
        (DyadicInterval.sub (DyadicInterval.point 1)
          (dyadicRouteBLargeSmallT L y)))))).lo
  valueOrdered : (dyadicRouteBLargeSmallCellValue L r y).Ordered

instance (L r : DyadicInterval) :
    Decidable (DyadicLargeSmallBoxAdmissible L r) :=
  decidable_of_iff
    (0 ≤ L.lo ∧
      L.hi ≤ (DyadicInterval.ofRat 1 16).lo ∧
      0 < r.lo ∧
      (DyadicInterval.point 1).hi ≤ r.lo ∧
      r.hi ≤ (DyadicInterval.point 2).lo ∧
      0 < (DyadicInterval.sqr r).lo ∧
      0 < (DyadicInterval.mul (DyadicInterval.point 2)
        (DyadicInterval.sqr r)).lo ∧
      0 < (powi r 3).lo) <| by
        constructor
        · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
          exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
        · intro h
          exact ⟨h.LNonnegative, h.LLeSixteenth, h.rPos, h.oneLeR,
            h.rLeTwo, h.rSqPos, h.normalDenPos, h.rCubePos⟩

instance (L r y : DyadicInterval) :
    Decidable (DyadicLargeSmallCellAdmissible L r y) :=
  decidable_of_iff
    (0 ≤ (DyadicInterval.mul dyadicRouteBLargeAlpha
        (dyadicRouteBLargeSmallLowQ L r y)).lo ∧
      0 ≤ (dyadicRouteBLargeSmallNormalArg r y).lo ∧
      0 ≤ (dyadicRouteBLargeSmallHighQ L r y).lo ∧
      0 < (DyadicInterval.mul (DyadicInterval.point 4725)
        (DyadicInterval.sub (DyadicInterval.point 1)
          (DyadicInterval.sqr (dyadicRouteBLargeSmallT L y)))).lo ∧
      0 < (DyadicInterval.mul (DyadicInterval.point 4725)
        (DyadicInterval.sub (DyadicInterval.point 1)
          (DyadicInterval.sqr (DyadicInterval.sub (DyadicInterval.point 1)
            (DyadicInterval.sub (DyadicInterval.point 1)
              (dyadicRouteBLargeSmallT L y)))))).lo ∧
      (dyadicRouteBLargeSmallCellValue L r y).lo ≤
        (dyadicRouteBLargeSmallCellValue L r y).hi) <| by
        constructor
        · rintro ⟨h1, h2, h3, h4, h5, h6⟩
          exact ⟨h1, h2, h3, h4, h5, h6⟩
        · intro h
          exact ⟨h.alphaArgNonnegative, h.normalArgNonnegative,
            h.highArgNonnegative, h.lowCotDenom, h.highCotDenom,
            h.valueOrdered⟩

noncomputable section

lemma dyadicRouteBTwoPi_sound :
    dyadicRouteBTwoPi.Contains (2 * Real.pi) := by
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  simpa [dyadicRouteBTwoPi] using htwo.mul checkerPi_contains_pi

theorem dyadicRouteBLargeSmallYCell_contains
    {N i : ℕ} (hN : 0 < N) (hi : i < N) {y : ℝ}
    (hy : y ∈ Set.Icc (routeBEqualPartitionPoint 0 4 N i)
      (routeBEqualPartitionPoint 0 4 N (i + 1))) :
    (dyadicRouteBLargeSmallYCell N i).Contains y := by
  have hzero : (DyadicInterval.point 0).Contains (0 : ℝ) := by
    simpa using DyadicInterval.contains_point (0 : ℤ)
  have hfour : (DyadicInterval.point 4).Contains (4 : ℝ) := by
    simpa using DyadicInterval.contains_point (4 : ℤ)
  simpa [dyadicRouteBLargeSmallYCell] using
    dyadicPrawitzCellRange_contains hzero hfour hN hi hy

theorem dyadicRouteBLargeSmallYWidth_contains
    {N i : ℕ} (hN : 0 < N) (hi : i < N) :
    (dyadicRouteBLargeSmallYWidth N i).Contains
      (routeBEqualPartitionPoint 0 4 N (i + 1) -
        routeBEqualPartitionPoint 0 4 N i) := by
  have hzero : (DyadicInterval.point 0).Contains (0 : ℝ) := by
    simpa using DyadicInterval.contains_point (0 : ℤ)
  have hfour : (DyadicInterval.point 4).Contains (4 : ℝ) := by
    simpa using DyadicInterval.contains_point (4 : ℤ)
  simpa [dyadicRouteBLargeSmallYWidth] using
    dyadicPrawitzCellRawWidth_sound hzero hfour hN hi

lemma dyadicRouteBLargeSmallT_sound
    {L y : DyadicInterval} {LR yR : ℝ}
    (hL : L.Contains LR) (hy : y.Contains yR) :
    (dyadicRouteBLargeSmallT L y).Contains (LR * yR) := by
  simpa [dyadicRouteBLargeSmallT] using hL.mul hy

lemma dyadicRouteBLargeSmallV_sound
    {L y : DyadicInterval} {LR yR : ℝ}
    (hL : L.Contains LR) (hy : y.Contains yR) :
    (dyadicRouteBLargeSmallV L y).Contains (2 * Real.pi * LR * yR) := by
  have ht := dyadicRouteBLargeSmallT_sound hL hy
  convert dyadicRouteBTwoPi_sound.mul ht using 1 <;> ring

lemma dyadicRouteBLargeSmallYV_sound
    {y : DyadicInterval} {yR : ℝ} (hy : y.Contains yR) :
    (dyadicRouteBLargeSmallYV y).Contains (2 * Real.pi * yR) := by
  simpa [dyadicRouteBLargeSmallYV] using dyadicRouteBTwoPi_sound.mul hy

lemma dyadicRouteBLargeSmallLowLine_sound
    {L y : DyadicInterval} {LR yR : ℝ}
    (hL : L.Contains LR) (hy : y.Contains yR) :
    (dyadicRouteBLargeSmallLowLine L y).Contains
      (max ((1 : ℝ) / 2 -
        routeBKappaUpper * (2 * Real.pi * LR * yR)) 0) := by
  have hhalf : (DyadicInterval.ofRat 1 2).Contains ((1 : ℝ) / 2) :=
    by simpa using DyadicInterval.contains_ofRat 1 (b := 2) (by norm_num)
  have hv := dyadicRouteBLargeSmallV_sound hL hy
  have hline := hhalf.sub (checkerKappaUpper_contains.mul hv)
  have hmax := hline.maxZero
  simpa [dyadicRouteBLargeSmallLowLine, max_comm] using hmax

lemma dyadicRouteBLargeSmallCosRatio_sound
    {L y : DyadicInterval} {LR yR : ℝ}
    (hL : L.Contains LR) (hy : y.Contains yR) :
    (dyadicRouteBLargeSmallCosRatio L y).Contains
      (routeBSmallCosineRatioLower (2 * Real.pi * LR * yR)) := by
  let x := dyadicRouteBLargeSmallV L y
  have hx : x.Contains (2 * Real.pi * LR * yR) :=
    dyadicRouteBLargeSmallV_sound hL hy
  have hx2 := hx.sqr hx.ordered
  have hx4 := hx2.sqr hx2.ordered
  have hx6 := hx4.mul hx2
  have hx8 := hx4.sqr hx4.ordered
  have hx10 := hx8.mul hx2
  have hhalf : (DyadicInterval.ofRat 1 2).Contains ((1 : ℝ) / 2) :=
    by simpa using DyadicInterval.contains_ofRat 1 (b := 2) (by norm_num)
  have h24 := dyadicContains_div_point hx2 24 (by norm_num)
  have h720 := dyadicContains_div_point hx4 720 (by norm_num)
  have h40320 := dyadicContains_div_point hx6 40320 (by norm_num)
  have h3628800 := dyadicContains_div_point hx8 3628800 (by norm_num)
  have h479001600 := dyadicContains_div_point hx10 479001600 (by norm_num)
  have hresult := ((((hhalf.sub h24).add h720).sub h40320).add h3628800).sub
    h479001600
  dsimp only [x] at hresult
  unfold dyadicRouteBLargeSmallCosRatio
  dsimp only
  convert hresult using 1 <;>
    simp [routeBSmallCosineRatioLower] <;> ring

lemma dyadicRouteBLargeSmallLowQ_sound
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hr2Lo : 0 < (DyadicInterval.sqr r).lo) :
    (dyadicRouteBLargeSmallLowQ L r y).Contains
      (routeBLargeSmallLowCellQ rR yR
        (dyadicRouteBLargeSmallLowLine L y).lower) := by
  have hyv := dyadicRouteBLargeSmallYV_sound hy
  have hyv2 := hyv.sqr hyv.ordered
  have hql := dyadicCellLowerPoint_contains
    (dyadicRouteBLargeSmallLowLine L y)
  have hnum := hyv2.mul hql
  have hr2 := hr.sqr hr.ordered
  have hraw := hnum.div hr2 hr2.ordered hr2Lo
  have hmax := hraw.maxZero
  simpa [dyadicRouteBLargeSmallLowQ, dyadicRouteBLargeSmallLowQRaw,
    routeBLargeSmallLowCellQ, max_comm] using hmax

lemma routeBLargeSmallLowCellQ_le
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hrPos : 0 < rR) :
    routeBLargeSmallLowCellQ rR yR
        (dyadicRouteBLargeSmallLowLine L y).lower ≤
      routeBLargeSmallLowQ LR rR yR := by
  have hline := dyadicRouteBLargeSmallLowLine_sound hL hy
  have hmul :
      (2 * Real.pi * yR) ^ 2 *
          (dyadicRouteBLargeSmallLowLine L y).lower ≤
        (2 * Real.pi * yR) ^ 2 *
          max ((1 : ℝ) / 2 -
            routeBKappaUpper * (2 * Real.pi * LR * yR)) 0 :=
    mul_le_mul_of_nonneg_left hline.1 (sq_nonneg _)
  have hquot := div_le_div_of_nonneg_right hmul (sq_nonneg rR)
  let line : ℝ := (1 : ℝ) / 2 -
    routeBKappaUpper * (2 * Real.pi * LR * yR)
  have hupperEq :
      max (((2 * Real.pi * yR) ^ 2 * max line 0) / rR ^ 2) 0 =
        max (((2 * Real.pi * yR) ^ 2 * line) / rR ^ 2) 0 := by
    by_cases hline : 0 ≤ line
    · rw [max_eq_left hline]
    · have hline' : line ≤ 0 := le_of_not_ge hline
      have hraw : (2 * Real.pi * yR) ^ 2 * line / rR ^ 2 ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hline')
          (sq_nonneg _)
      rw [max_eq_right hline', mul_zero, zero_div, max_self,
        max_eq_right hraw]
  unfold routeBLargeSmallLowCellQ routeBLargeSmallLowQ
  have hmax :
      max ((2 * Real.pi * yR) ^ 2 *
          (dyadicRouteBLargeSmallLowLine L y).lower / rR ^ 2) 0 ≤
        max ((2 * Real.pi * yR) ^ 2 *
          max ((1 : ℝ) / 2 -
            routeBKappaUpper * (2 * Real.pi * LR * yR)) 0 / rR ^ 2) 0 :=
    max_le_max hquot (le_refl (0 : ℝ))
  dsimp only [line] at hupperEq
  exact hmax.trans_eq hupperEq

lemma dyadicRouteBLargeSmallHighQ_sound
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hr2Lo : 0 < (DyadicInterval.sqr r).lo) :
    (dyadicRouteBLargeSmallHighQ L r y).Contains
      (routeBLargeSmallHighQ LR rR yR) := by
  have hyv := dyadicRouteBLargeSmallYV_sound hy
  have hyv2 := hyv.sqr hyv.ordered
  have hcos := dyadicRouteBLargeSmallCosRatio_sound hL hy
  have hnum := hyv2.mul hcos
  have hr2 := hr.sqr hr.ordered
  have hraw := hnum.div hr2 hr2.ordered hr2Lo
  have hmax := hraw.maxZero
  simpa [dyadicRouteBLargeSmallHighQ, dyadicRouteBLargeSmallHighQRaw,
    routeBLargeSmallHighQ, max_comm] using hmax

lemma dyadicRouteBLargeSmallAlphaExp_sound
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hr2Lo : 0 < (DyadicInterval.sqr r).lo)
    (harg : 0 ≤ (DyadicInterval.mul dyadicRouteBLargeAlpha
      (dyadicRouteBLargeSmallLowQ L r y)).lo) :
    (dyadicRouteBLargeSmallAlphaExp L r y).Contains
      (Real.exp (-routeBLargeNAlpha *
        routeBLargeSmallLowCellQ rR yR
          (dyadicRouteBLargeSmallLowLine L y).lower)) := by
  have hq := dyadicRouteBLargeSmallLowQ_sound hL hr hy hr2Lo
  have hproduct := dyadicRouteBLargeAlpha_sound.mul hq
  simpa [dyadicRouteBLargeSmallAlphaExp] using
    dyadicExpNeg_sound hproduct harg

lemma dyadicRouteBLargeSmallNormal_sound
    {r y : DyadicInterval} {rR yR : ℝ}
    (hr : r.Contains rR) (hy : y.Contains yR)
    (hden : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (DyadicInterval.sqr r)).lo)
    (harg : 0 ≤ (dyadicRouteBLargeSmallNormalArg r y).lo) :
    (dyadicRouteBLargeSmallNormal r y).Contains
      (Real.exp (-((2 * Real.pi * yR) ^ 2 / (2 * rR ^ 2)))) := by
  have hyv := dyadicRouteBLargeSmallYV_sound hy
  have hyv2 := hyv.sqr hyv.ordered
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hr2 := hr.sqr hr.ordered
  have hdenSound := htwo.mul hr2
  have hquot := hyv2.div hdenSound hdenSound.ordered hden
  have hexp := dyadicExpNeg_sound hquot harg
  simpa [dyadicRouteBLargeSmallNormal,
    dyadicRouteBLargeSmallNormalArg] using hexp

lemma dyadicRouteBLargeSmallP0_sound
    {L y : DyadicInterval} {LR yR : ℝ}
    (hL : L.Contains LR) (hy : y.Contains yR)
    (hCot : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
      (DyadicInterval.sub (DyadicInterval.point 1)
        (DyadicInterval.sqr (dyadicRouteBLargeSmallT L y)))).lo) :
    (dyadicRouteBLargeSmallP0 L y).Contains
      (2 * Real.pi * prawitzK0Envelope (LR * yR)) := by
  have ht := dyadicRouteBLargeSmallT_sound hL hy
  have hk0 := dyadicPrawitzK0Upper_sound ht hCot
  simpa [dyadicRouteBLargeSmallP0] using dyadicRouteBTwoPi_sound.mul hk0

lemma dyadicRouteBLargeSmallD_sound
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hrLo : 0 < r.lo) (hr1 : 1 ≤ rR) (hr2 : rR ≤ 2)
    (hLR0 : 0 ≤ LR) (hLR16 : LR ≤ 1 / 16)
    (hy0 : 0 ≤ yR) (hy4 : yR ≤ 4) :
    (dyadicRouteBLargeSmallD L r y).Contains
      (routeBDiskStar rR (2 * Real.pi * LR * yR / rR)) := by
  have hv := dyadicRouteBLargeSmallV_sound hL hy
  have ht0 : 0 ≤ LR * yR := mul_nonneg hLR0 hy0
  have htSplit : LR * yR ≤ prawitzSplit := by
    have hquarter : LR * yR ≤ 1 / 4 := by
      nlinarith [mul_le_mul hLR16 hy4 hy0 (by norm_num : (0 : ℝ) ≤ 1 / 16)]
    norm_num [prawitzSplit] at hquarter ⊢
    linarith
  have hy3 := routeBLargeDstar_y_le_three hr1 ht0 htSplit
  have hy3' : (2 * Real.pi * LR * yR / rR) ^ 2 / 2 ≤ 3 := by
    simpa [mul_assoc] using hy3
  have hv0 : 0 ≤ 2 * Real.pi * LR * yR := by positivity
  simpa [dyadicRouteBLargeSmallD, mul_assoc] using
    dyadicPrawitzDstar_sound hr hv hrLo hr1 hr2 hv0 hy3'

lemma dyadicRouteBLargeSmallHighExp_sound
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hr2Lo : 0 < (DyadicInterval.sqr r).lo)
    (harg : 0 ≤ (dyadicRouteBLargeSmallHighQ L r y).lo) :
    (dyadicExpNeg (dyadicRouteBLargeSmallHighQ L r y)).Contains
      (Real.exp (-routeBLargeSmallHighQ LR rR yR)) := by
  exact dyadicExpNeg_sound
    (dyadicRouteBLargeSmallHighQ_sound hL hr hy hr2Lo) harg

theorem DyadicLargeSmallBoxAdmissible.real_L_nonnegative
    {L r : DyadicInterval} (hbox : DyadicLargeSmallBoxAdmissible L r)
    {LR : ℝ} (hL : L.Contains LR) : 0 ≤ LR := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  have hlower : (0 : ℝ) ≤ L.lower := by
    unfold DyadicInterval.lower
    exact div_nonneg (by exact_mod_cast hbox.LNonnegative) hscale.le
  exact hlower.trans hL.1

theorem DyadicLargeSmallBoxAdmissible.real_L_le_sixteenth
    {L r : DyadicInterval} (hbox : DyadicLargeSmallBoxAdmissible L r)
    {LR : ℝ} (hL : L.Contains LR) : LR ≤ 1 / 16 := by
  have hmiddle := dyadic_upper_le_lower_of_hi_le_lo hbox.LLeSixteenth
  have hrat : (DyadicInterval.ofRat 1 16).Contains ((1 : ℝ) / 16) := by
    simpa using DyadicInterval.contains_ofRat 1 (b := 16) (by norm_num)
  exact hL.2.trans (hmiddle.trans hrat.1)

theorem DyadicLargeSmallBoxAdmissible.real_r_pos
    {L r : DyadicInterval} (hbox : DyadicLargeSmallBoxAdmissible L r)
    {rR : ℝ} (hr : r.Contains rR) : 0 < rR := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  have hlower : (0 : ℝ) < r.lower := by
    unfold DyadicInterval.lower
    exact div_pos (by exact_mod_cast hbox.rPos) hscale
  exact hlower.trans_le hr.1

theorem DyadicLargeSmallBoxAdmissible.real_one_le_r
    {L r : DyadicInterval} (hbox : DyadicLargeSmallBoxAdmissible L r)
    {rR : ℝ} (hr : r.Contains rR) : 1 ≤ rR := by
  have hmiddle := dyadic_upper_le_lower_of_hi_le_lo hbox.oneLeR
  have hone : (DyadicInterval.point 1).upper = (1 : ℝ) := by
    simp [DyadicInterval.upper, DyadicInterval.point, dyadicScale_pos.ne']
  rw [hone] at hmiddle
  exact hmiddle.trans hr.1

theorem DyadicLargeSmallBoxAdmissible.real_r_le_two
    {L r : DyadicInterval} (hbox : DyadicLargeSmallBoxAdmissible L r)
    {rR : ℝ} (hr : r.Contains rR) : rR ≤ 2 := by
  have hmiddle := dyadic_upper_le_lower_of_hi_le_lo hbox.rLeTwo
  have htwo : (DyadicInterval.point 2).lower = (2 : ℝ) := by
    simp [DyadicInterval.lower, DyadicInterval.point, dyadicScale_pos.ne']
  rw [htwo] at hmiddle
  exact hr.2.trans hmiddle

lemma dyadicRouteBLargeSmallF1_sound
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hbox : DyadicLargeSmallBoxAdmissible L r)
    (hcell : DyadicLargeSmallCellAdmissible L r y)
    (hy0 : 0 ≤ yR) (hy4 : yR ≤ 4) :
    (dyadicRouteBLargeSmallF1 L r y).Contains
      (routeBLargeSmallCellF1 rR yR
        (prawitzK0Envelope (LR * yR))
        (routeBLargeSmallLowCellQ rR yR
          (dyadicRouteBLargeSmallLowLine L y).lower)
        (routeBDiskStar rR (2 * Real.pi * LR * yR / rR))) := by
  have height : (DyadicInterval.point 8).Contains (8 : ℝ) := by
    simpa using DyadicInterval.contains_point (8 : ℤ)
  have hpi2 := checkerPi_contains_pi.sqr checkerPi_contains_pi.ordered
  have hnum := height.mul hpi2
  have hr3 := powi_sound hr 3
  have hscale := hnum.div hr3 hr3.ordered hbox.rCubePos
  have hy2 := hy.sqr hy.ordered
  have hwithY := hscale.mul hy2
  have hP0 := dyadicRouteBLargeSmallP0_sound hL hy hcell.lowCotDenom
  have hwithP0 := hwithY.mul hP0
  have hD := dyadicRouteBLargeSmallD_sound hL hr hy hbox.rPos
    (hbox.real_one_le_r hr) (hbox.real_r_le_two hr)
    (hbox.real_L_nonnegative hL) (hbox.real_L_le_sixteenth hL) hy0 hy4
  have hExp := dyadicRouteBLargeSmallAlphaExp_sound hL hr hy hbox.rSqPos
    hcell.alphaArgNonnegative
  have hresult := hwithP0.mul (hD.mul hExp)
  unfold dyadicRouteBLargeSmallF1 routeBLargeSmallCellF1
  dsimp only
  convert hresult using 1 <;> ring

lemma dyadicRouteBLargeSmallF3_sound
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hbox : DyadicLargeSmallBoxAdmissible L r)
    (hcell : DyadicLargeSmallCellAdmissible L r y) :
    (dyadicRouteBLargeSmallF3 L r y).Contains
      (routeBLargeSmallCellF3 rR yR
        (prawitzKD2Envelope (LR * yR))) := by
  have ht := dyadicRouteBLargeSmallT_sound hL hy
  have hkd2 := dyadicPrawitzKD2Upper_sound ht hcell.lowCotDenom
  have hnormal := dyadicRouteBLargeSmallNormal_sound hr hy
    hbox.normalDenPos hcell.normalArgNonnegative
  simpa [dyadicRouteBLargeSmallF3, routeBLargeSmallCellF3] using
    hkd2.mul hnormal

lemma dyadicRouteBLargeSmallF2_sound
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hbox : DyadicLargeSmallBoxAdmissible L r)
    (hcell : DyadicLargeSmallCellAdmissible L r y) :
    (dyadicRouteBLargeSmallF2 L r y).Contains
      (routeBLargeSmallCellF2 (prawitzKH2Envelope (1 - LR * yR))
        (routeBLargeSmallHighQ LR rR yR)) := by
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have ht := dyadicRouteBLargeSmallT_sound hL hy
  have hhigh := hone.sub ht
  have hkh2 := dyadicPrawitzKH2Upper_sound hhigh hcell.highCotDenom
  have hexp := dyadicRouteBLargeSmallHighExp_sound hL hr hy hbox.rSqPos
    hcell.highArgNonnegative
  simpa [dyadicRouteBLargeSmallF2, routeBLargeSmallCellF2] using hkh2.mul hexp

theorem routeBLargeSmallIntegrand_le_dyadicCellValue_upper
    {L r y : DyadicInterval} {LR rR yR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hy : y.Contains yR)
    (hbox : DyadicLargeSmallBoxAdmissible L r)
    (hcell : DyadicLargeSmallCellAdmissible L r y)
    (hLR : 0 < LR) (hy0 : 0 ≤ yR) (hy4 : yR ≤ 4) :
    routeBLargeSmallIntegrand LR rR yR ≤
      (dyadicRouteBLargeSmallCellValue L r y).upper := by
  have hrR := hbox.real_r_pos hr
  have hLu := hbox.real_L_le_sixteenth hL
  have ht0 : 0 ≤ LR * yR := mul_nonneg hLR.le hy0
  have hquarter : LR * yR ≤ 1 / 4 := by
    nlinarith [mul_le_mul hLu hy4 hy0 (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have ht1 : LR * yR < 1 := hquarter.trans_lt (by norm_num)
  let qlow := routeBLargeSmallLowCellQ rR yR
    (dyadicRouteBLargeSmallLowLine L y).lower
  have hqLow0 : 0 ≤ qlow := by
    dsimp only [qlow]
    exact le_max_right _ _
  have hqLow : qlow ≤ routeBLargeSmallLowQ LR rR yR := by
    dsimp only [qlow]
    exact routeBLargeSmallLowCellQ_le hL hr hy hrR
  have hF1Real := routeBLargeSmallF1_le_cell hrR hy0 ht0 ht1 le_rfl
    hqLow0 hqLow le_rfl
  have hF1Contains := dyadicRouteBLargeSmallF1_sound hL hr hy hbox hcell hy0 hy4
  have hF1 : routeBLargeSmallF1 LR rR yR ≤
      (dyadicRouteBLargeSmallF1 L r y).upper :=
    hF1Real.trans hF1Contains.2
  have hF3Real := routeBLargeSmallF3_le_cell
    (L := LR) (r := rR) (y := yR) (kd2 := prawitzKD2Envelope (LR * yR))
    ht0 ht1 le_rfl
  have hF3Contains := dyadicRouteBLargeSmallF3_sound hL hr hy hbox hcell
  have hF3 : routeBLargeSmallF3 LR rR yR ≤
      (dyadicRouteBLargeSmallF3 L r y).upper :=
    hF3Real.trans hF3Contains.2
  have hhigh0 : 0 < 1 - LR * yR := by linarith
  have hhigh1 : 1 - LR * yR ≤ 1 := by linarith
  have hqHigh0 : 0 ≤ routeBLargeSmallHighQ LR rR yR :=
    routeBLargeSmallHighQ_nonneg _ _ _
  have hF2Real := routeBLargeSmallF2_le_cell
    (L := LR) (r := rR) (y := yR)
    (kh2 := prawitzKH2Envelope (1 - LR * yR))
    (q := routeBLargeSmallHighQ LR rR yR)
    hhigh0 hhigh1 le_rfl hqHigh0 le_rfl
  have hF2Contains := dyadicRouteBLargeSmallF2_sound hL hr hy hbox hcell
  have hF2 : routeBLargeSmallF2 LR rR yR ≤
      (dyadicRouteBLargeSmallF2 L r y).upper :=
    hF2Real.trans hF2Contains.2
  have hsum := add_le_add (add_le_add hF1 hF3) hF2
  simpa [routeBLargeSmallIntegrand, routeBLargeSmallLowIntegrand,
    dyadicRouteBLargeSmallCellValue, DyadicInterval.add,
    DyadicInterval.upper, Int.cast_add, add_div] using hsum

/-- Darboux bridge for any integrable function dominated by the compact
endpoint-regular integrand.  The later change-of-variables theorem instantiates
`f` with the two original normalized Prawitz endpoint terms. -/
theorem intervalIntegral_le_dyadicRouteBLargeSmallFiniteSum_upper
    {f : ℝ → ℝ} {N : ℕ} (hN : 0 < N)
    {L r : DyadicInterval} {LR rR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR)
    (hbox : DyadicLargeSmallBoxAdmissible L r)
    (hLR : 0 < LR)
    (hint : IntervalIntegrable f volume 0 4)
    (hdom : ∀ y ∈ Set.Icc (0 : ℝ) 4,
      f y ≤ routeBLargeSmallIntegrand LR rR y)
    (hadmissible : ∀ i < N, DyadicLargeSmallCellAdmissible L r
      (dyadicRouteBLargeSmallYCell N i)) :
    (∫ y in (0 : ℝ)..4, f y) ≤
      (dyadicRouteBLargeSmallFiniteSum L r N).upper := by
  let p := routeBEqualPartitionPoint (0 : ℝ) 4 N
  have hbound := intervalIntegral_le_intervalNatSum_upper
    (f := f) (p := p) (N := N)
    (fun i hi => routeBEqualPartitionPoint_mono (by norm_num) hN (Nat.le_succ i))
    (fun i hi => intervalIntegrable_equalPartitionCell hint
      (by norm_num) hN hi)
    (fun i => dyadicRouteBLargeSmallCellValue L r
      (dyadicRouteBLargeSmallYCell N i))
    (fun i => dyadicRouteBLargeSmallYWidth N i)
    (fun i hi => (hadmissible i hi).valueOrdered)
    (fun i hi y hy => by
      have hpLeft := routeBEqualPartitionPoint_mem_Icc
        (a := (0 : ℝ)) (b := (4 : ℝ)) (by norm_num) hN (Nat.le_of_lt hi)
      have hpRight := routeBEqualPartitionPoint_mem_Icc
        (a := (0 : ℝ)) (b := (4 : ℝ)) (by norm_num) hN
          (Nat.succ_le_iff.mpr hi)
      have hy0 : 0 ≤ y := hpLeft.1.trans hy.1
      have hy4 : y ≤ 4 := hy.2.trans hpRight.2
      have hyCell := dyadicRouteBLargeSmallYCell_contains hN hi hy
      exact (hdom y ⟨hy0, hy4⟩).trans
        (routeBLargeSmallIntegrand_le_dyadicCellValue_upper
          hL hr hyCell hbox (hadmissible i hi) hLR hy0 hy4))
    (fun i hi => dyadicRouteBLargeSmallYWidth_contains hN hi)
  simpa [p, dyadicRouteBLargeSmallFiniteSum,
    routeBEqualPartitionPoint_zero, routeBEqualPartitionPoint_at_N hN] using hbound

end

end BerryEsseen
