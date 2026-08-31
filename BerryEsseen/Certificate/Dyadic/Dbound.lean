import BerryEsseen.Smoothing.PrawitzDbound
import BerryEsseen.Certificate.Dyadic.HQLower
/-!
# Verifier-matching dyadic `Dbound`

This module implements the exact checker's correlation-preserving disk-bound evaluator.  Every
intermediate interval is connected to its real semantics, all three `a`/`kappa` branches are
proved sound, and the returned square-root upper endpoint bounds the analytic Route B disk term.
-/

namespace BerryEsseen

open DyadicInterval

def dyadicDboundW (rho z : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add rho z

def dyadicDboundP (rho : DyadicInterval) : DyadicInterval :=
  DyadicInterval.div (DyadicInterval.point 1) rho

def dyadicDboundY (rho z v : DyadicInterval) : DyadicInterval :=
  let w := dyadicDboundW rho z
  DyadicInterval.div (DyadicInterval.sqr v)
    (DyadicInterval.mul (DyadicInterval.point 2) (DyadicInterval.sqr w))

def dyadicDboundC (rho z v : DyadicInterval) : DyadicInterval :=
  let w := dyadicDboundW rho z
  let y := dyadicDboundY rho z v
  DyadicInterval.mul
    (DyadicInterval.div v (DyadicInterval.mul (DyadicInterval.point 4) w))
    (hfunInterval y)

def dyadicDboundV0 (rho z v : DyadicInterval) : DyadicInterval :=
  let w := dyadicDboundW rho z
  let p := dyadicDboundP rho
  let C := dyadicDboundC rho z v
  let C2 := DyadicInterval.sqr C
  let w2 := DyadicInterval.sqr w
  let p2 := DyadicInterval.sqr p
  DyadicInterval.add
    (DyadicInterval.mul
      (DyadicInterval.sub C2
        (DyadicInterval.div w2 (DyadicInterval.point 36))) p2)
    (DyadicInterval.div (DyadicInterval.mul w p) (DyadicInterval.point 18))

def dyadicDboundVa (rho z v : DyadicInterval) : DyadicInterval :=
  let w := dyadicDboundW rho z
  let p := dyadicDboundP rho
  let C := dyadicDboundC rho z v
  let C2 := DyadicInterval.sqr C
  let p2 := DyadicInterval.sqr p
  DyadicInterval.add
    (DyadicInterval.add (DyadicInterval.ofRat 1 36)
      (DyadicInterval.mul
        (DyadicInterval.sub C2
          (DyadicInterval.div (DyadicInterval.mul C w) (DyadicInterval.point 3))) p2))
    (DyadicInterval.div (DyadicInterval.mul C p) (DyadicInterval.point 3))

def dyadicDboundVk (rho z v : DyadicInterval) : DyadicInterval :=
  let w := dyadicDboundW rho z
  let p := dyadicDboundP rho
  let C := dyadicDboundC rho z v
  let C2 := DyadicInterval.sqr C
  let w2 := DyadicInterval.sqr w
  let p2 := DyadicInterval.sqr p
  DyadicInterval.add
    (DyadicInterval.add (DyadicInterval.sqr checkerKappaUpper)
      (DyadicInterval.mul
        (DyadicInterval.sub C2
          (DyadicInterval.div w2 (DyadicInterval.point 36))) p2))
    (DyadicInterval.mul
      (DyadicInterval.sub
        (DyadicInterval.div w (DyadicInterval.point 18))
        (DyadicInterval.mul (DyadicInterval.point 2)
          (DyadicInterval.mul checkerKappaLower C))) p)

def dyadicDboundA (rho z : DyadicInterval) : DyadicInterval :=
  let w := dyadicDboundW rho z
  let p := dyadicDboundP rho
  DyadicInterval.div
    (DyadicInterval.sub (DyadicInterval.mul w p) (DyadicInterval.point 1))
    (DyadicInterval.point 6)

def dyadicUpperHull (hi : ℤ) : DyadicInterval :=
  ⟨0, max 0 hi⟩

def dyadicPrawitzDbound (rho z v : DyadicInterval) : DyadicInterval :=
  let V0 := dyadicDboundV0 rho z v
  let Va := dyadicDboundVa rho z v
  let Vk := dyadicDboundVk rho z v
  let a := dyadicDboundA rho z
  let hi :=
    if a.hi ≤ checkerKappaLower.lo then max V0.hi Va.hi
    else if checkerKappaUpper.hi ≤ a.lo then max V0.hi Vk.hi
    else max (max V0.hi Va.hi) Vk.hi
  DyadicInterval.sqrt (dyadicUpperHull hi)

/-- Let-shared form of `dyadicPrawitzDbound`.  The exact checker computes the common
`w`, `p`, `C`, `C²`, `w²`, and `p²` values once before forming its three branch candidates.
This definition preserves the exact interval result while avoiding three independent
re-evaluations of the expensive `hfunInterval` term in compiled certificates. -/
def dyadicPrawitzDboundShared (rho z v : DyadicInterval) : DyadicInterval :=
  let w := dyadicDboundW rho z
  let p := dyadicDboundP rho
  let y := DyadicInterval.div (DyadicInterval.sqr v)
    (DyadicInterval.mulPoint 2 (DyadicInterval.sqr w))
  let C := DyadicInterval.mul
    (DyadicInterval.div v (DyadicInterval.mulPoint 4 w))
    (hfunInterval y)
  let C2 := DyadicInterval.sqr C
  let w2 := DyadicInterval.sqr w
  let p2 := DyadicInterval.sqr p
  let V0 := DyadicInterval.add
    (DyadicInterval.mul
      (DyadicInterval.sub C2
        (DyadicInterval.divPoint w2 36)) p2)
    (DyadicInterval.divPoint (DyadicInterval.mul w p) 18)
  let Va := DyadicInterval.add
    (DyadicInterval.add (DyadicInterval.ofRat 1 36)
      (DyadicInterval.mul
        (DyadicInterval.sub C2
          (DyadicInterval.divPoint (DyadicInterval.mul C w) 3)) p2))
    (DyadicInterval.divPoint (DyadicInterval.mul C p) 3)
  let Vk := DyadicInterval.add
    (DyadicInterval.add (DyadicInterval.sqr checkerKappaUpper)
      (DyadicInterval.mul
        (DyadicInterval.sub C2
          (DyadicInterval.divPoint w2 36)) p2))
    (DyadicInterval.mul
      (DyadicInterval.sub
        (DyadicInterval.divPoint w 18)
        (DyadicInterval.mulPoint 2 (DyadicInterval.mul checkerKappaLower C))) p)
  let a := DyadicInterval.divPoint
    (DyadicInterval.sub (DyadicInterval.mul w p) (DyadicInterval.point 1)) 6
  let hi :=
    if a.hi ≤ checkerKappaLower.lo then max V0.hi Va.hi
    else if checkerKappaUpper.hi ≤ a.lo then max V0.hi Vk.hi
    else max (max V0.hi Va.hi) Vk.hi
  DyadicInterval.sqrt (dyadicUpperHull hi)

theorem dyadicPrawitzDboundShared_eq (rho z v : DyadicInterval) :
    dyadicPrawitzDboundShared rho z v = dyadicPrawitzDbound rho z v := by
  simp only [dyadicPrawitzDboundShared, DyadicInterval.mulPoint_eq_mul,
    DyadicInterval.divPoint_eq_div]
  rfl

noncomputable section

lemma dyadicUpperHull_contains {hi : ℤ} {x : ℝ}
    (hx0 : 0 ≤ x) (hxhi : x ≤ (hi : ℝ) / (dyadicScale : ℝ)) :
    (dyadicUpperHull hi).Contains x := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  constructor
  · simpa [dyadicUpperHull, DyadicInterval.lower] using hx0
  · change x ≤ ((max 0 hi : ℤ) : ℝ) / (dyadicScale : ℝ)
    rw [Int.cast_max, Int.cast_zero, ← max_div_div_right hscale.le, zero_div]
    exact hxhi.trans (le_max_right _ _)

lemma dyadic_max_upper_eq (I J : DyadicInterval) :
    max I.upper J.upper = ((max I.hi J.hi : ℤ) : ℝ) / (dyadicScale : ℝ) := by
  have hscale : (0 : ℝ) ≤ (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos.le
  simp only [DyadicInterval.upper, Int.cast_max, max_div_div_right hscale]

theorem dyadicDboundW_sound {rho z : DyadicInterval} {rhoR zR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) :
    (dyadicDboundW rho z).Contains (routeBDboundW rhoR zR) := by
  simpa [dyadicDboundW, routeBDboundW] using hrho.add hz

theorem dyadicDboundP_sound {rho : DyadicInterval} {rhoR : ℝ}
    (hrho : rho.Contains rhoR) (hrhoLo : 0 < rho.lo) :
    (dyadicDboundP rho).Contains (routeBDboundP rhoR) := by
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have h := hone.div hrho hrho.ordered hrhoLo
  simpa [dyadicDboundP, routeBDboundP] using h

theorem dyadicDboundY_sound {rho z v : DyadicInterval} {rhoR zR vR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (hv : v.Contains vR)
    (hden : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (DyadicInterval.sqr (dyadicDboundW rho z))).lo) :
    (dyadicDboundY rho z v).Contains (routeBDboundY rhoR zR vR) := by
  have hw := dyadicDboundW_sound hrho hz
  have hv2 := hv.sqr hv.ordered
  have hw2 := hw.sqr hw.ordered
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hdenSound := htwo.mul hw2
  have hquot := hv2.div hdenSound hdenSound.ordered hden
  simpa [dyadicDboundY, routeBDboundY] using hquot

theorem dyadicDboundC_sound {rho z v : DyadicInterval} {rhoR zR vR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (hv : v.Contains vR)
    (hyDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (DyadicInterval.sqr (dyadicDboundW rho z))).lo)
    (hCDen : 0 < (DyadicInterval.mul (DyadicInterval.point 4)
      (dyadicDboundW rho z)).lo)
    (hy0 : 0 ≤ routeBDboundY rhoR zR vR)
    (hy3 : routeBDboundY rhoR zR vR ≤ 3) :
    (dyadicDboundC rho z v).Contains (routeBDboundC rhoR zR vR) := by
  have hw := dyadicDboundW_sound hrho hz
  have hy := dyadicDboundY_sound hrho hz hv hyDen
  have hfour : (DyadicInterval.point 4).Contains (4 : ℝ) := by
    simpa using DyadicInterval.contains_point (4 : ℤ)
  have hdenSound := hfour.mul hw
  have hquot := hv.div hdenSound hdenSound.ordered hCDen
  have hH := hfunInterval_sound hy hy0 hy3
  have hresult := hquot.mul hH
  simpa [dyadicDboundC, routeBDboundC] using hresult

theorem dyadicDboundV0_sound {rho z v : DyadicInterval} {rhoR zR vR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (hv : v.Contains vR)
    (hrhoLo : 0 < rho.lo)
    (hyDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (DyadicInterval.sqr (dyadicDboundW rho z))).lo)
    (hCDen : 0 < (DyadicInterval.mul (DyadicInterval.point 4)
      (dyadicDboundW rho z)).lo)
    (hy0 : 0 ≤ routeBDboundY rhoR zR vR)
    (hy3 : routeBDboundY rhoR zR vR ≤ 3) :
    (dyadicDboundV0 rho z v).Contains (routeBDboundV0 rhoR zR vR) := by
  have hw := dyadicDboundW_sound hrho hz
  have hp := dyadicDboundP_sound hrho hrhoLo
  have hC := dyadicDboundC_sound hrho hz hv hyDen hCDen hy0 hy3
  have hC2 := hC.sqr hC.ordered
  have hw2 := hw.sqr hw.ordered
  have hp2 := hp.sqr hp.ordered
  have hw36 := dyadicContains_div_point hw2 36 (by norm_num)
  have hfirst := (hC2.sub hw36).mul hp2
  have hwp18 := dyadicContains_div_point (hw.mul hp) 18 (by norm_num)
  have hresult := hfirst.add hwp18
  simp only [dyadicDboundV0]
  convert hresult using 1
  unfold routeBDboundV0
  dsimp only
  ring

theorem dyadicDboundVa_sound {rho z v : DyadicInterval} {rhoR zR vR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (hv : v.Contains vR)
    (hrhoLo : 0 < rho.lo)
    (hyDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (DyadicInterval.sqr (dyadicDboundW rho z))).lo)
    (hCDen : 0 < (DyadicInterval.mul (DyadicInterval.point 4)
      (dyadicDboundW rho z)).lo)
    (hy0 : 0 ≤ routeBDboundY rhoR zR vR)
    (hy3 : routeBDboundY rhoR zR vR ≤ 3) :
    (dyadicDboundVa rho z v).Contains (routeBDboundVa rhoR zR vR) := by
  have hw := dyadicDboundW_sound hrho hz
  have hp := dyadicDboundP_sound hrho hrhoLo
  have hC := dyadicDboundC_sound hrho hz hv hyDen hCDen hy0 hy3
  have hC2 := hC.sqr hC.ordered
  have hp2 := hp.sqr hp.ordered
  have hthird := dyadicContains_div_point (hC.mul hw) 3 (by norm_num)
  have hmiddle := (hC2.sub hthird).mul hp2
  have hone36 : (DyadicInterval.ofRat 1 36).Contains ((1 : ℝ) / 36) := by
    simpa only [Int.cast_one, Int.cast_ofNat] using
      DyadicInterval.contains_ofRat 1 (b := 36) (by norm_num)
  have hlast := dyadicContains_div_point (hC.mul hp) 3 (by norm_num)
  have hresult := (hone36.add hmiddle).add hlast
  simp only [dyadicDboundVa]
  convert hresult using 1
  unfold routeBDboundVa
  dsimp only
  ring

theorem dyadicDboundVk_sound {rho z v : DyadicInterval} {rhoR zR vR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (hv : v.Contains vR)
    (hrhoLo : 0 < rho.lo)
    (hyDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (DyadicInterval.sqr (dyadicDboundW rho z))).lo)
    (hCDen : 0 < (DyadicInterval.mul (DyadicInterval.point 4)
      (dyadicDboundW rho z)).lo)
    (hy0 : 0 ≤ routeBDboundY rhoR zR vR)
    (hy3 : routeBDboundY rhoR zR vR ≤ 3) :
    (dyadicDboundVk rho z v).Contains (routeBDboundVkChecker rhoR zR vR) := by
  have hw := dyadicDboundW_sound hrho hz
  have hp := dyadicDboundP_sound hrho hrhoLo
  have hC := dyadicDboundC_sound hrho hz hv hyDen hCDen hy0 hy3
  have hC2 := hC.sqr hC.ordered
  have hw2 := hw.sqr hw.ordered
  have hp2 := hp.sqr hp.ordered
  have hkU2 := checkerKappaUpper_contains.sqr checkerKappaUpper_contains.ordered
  have hw36 := dyadicContains_div_point hw2 36 (by norm_num)
  have hcommon := (hC2.sub hw36).mul hp2
  have hw18 := dyadicContains_div_point hw 18 (by norm_num)
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hcross := htwo.mul (checkerKappaLower_contains.mul hC)
  have hlast := (hw18.sub hcross).mul hp
  have hresult := (hkU2.add hcommon).add hlast
  simp only [dyadicDboundVk]
  convert hresult using 1
  unfold routeBDboundVkChecker
  dsimp only
  ring

theorem dyadicDboundA_sound {rho z : DyadicInterval} {rhoR zR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hrhoLo : 0 < rho.lo) :
    (dyadicDboundA rho z).Contains
      (routeBTransition (routeBDboundR rhoR zR)) := by
  have hw := dyadicDboundW_sound hrho hz
  have hp := dyadicDboundP_sound hrho hrhoLo
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have hraw := dyadicContains_div_point ((hw.mul hp).sub hone) 6 (by norm_num)
  rw [routeBTransition_DboundR (by
    have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
    have hloReal : 0 < rho.lower := by
      unfold DyadicInterval.lower
      exact div_pos (by exact_mod_cast hrhoLo) hscale
    exact (hloReal.trans_le hrho.1).ne')]
  simpa [dyadicDboundA] using hraw

lemma dyadic_upper_le_lower_of_hi_le_lo {I J : DyadicInterval}
    (h : I.hi ≤ J.lo) : I.upper ≤ J.lower := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  unfold DyadicInterval.upper DyadicInterval.lower
  exact (div_le_div_iff_of_pos_right hscale).2 (by exact_mod_cast h)

theorem dyadicPrawitzDbound_sound
    {rho z v : DyadicInterval} {rhoR zR vR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (hv : v.Contains vR)
    (hrhoLo : 0 < rho.lo)
    (hyDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (DyadicInterval.sqr (dyadicDboundW rho z))).lo)
    (hCDen : 0 < (DyadicInterval.mul (DyadicInterval.point 4)
      (dyadicDboundW rho z)).lo)
    (hrhoR : 0 < rhoR) (hz0 : 0 ≤ zR) (hz1 : zR ≤ rhoR)
    (hv0 : 0 ≤ vR) (hy3 : routeBDboundY rhoR zR vR ≤ 3) :
    (dyadicPrawitzDbound rho z v).Contains
      (routeBDiskBound routeBKappa rhoR (routeBDboundR rhoR zR)
        (routeBDboundFrequency rhoR zR vR)) := by
  let V0 := dyadicDboundV0 rho z v
  let Va := dyadicDboundVa rho z v
  let Vk := dyadicDboundVk rho z v
  let a := dyadicDboundA rho z
  let S := routeBDiskBoundSq routeBKappa rhoR (routeBDboundR rhoR zR)
    (routeBDboundFrequency rhoR zR vR)
  have hy0 : 0 ≤ routeBDboundY rhoR zR vR := by
    unfold routeBDboundY routeBDboundW
    positivity
  have hV0 : V0.Contains (routeBDboundV0 rhoR zR vR) :=
    dyadicDboundV0_sound hrho hz hv hrhoLo hyDen hCDen hy0 hy3
  have hVa : Va.Contains (routeBDboundVa rhoR zR vR) :=
    dyadicDboundVa_sound hrho hz hv hrhoLo hyDen hCDen hy0 hy3
  have hVk : Vk.Contains (routeBDboundVkChecker rhoR zR vR) :=
    dyadicDboundVk_sound hrho hz hv hrhoLo hyDen hCDen hy0 hy3
  have ha : a.Contains (routeBTransition (routeBDboundR rhoR zR)) :=
    dyadicDboundA_sound hrho hz hrhoLo
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    exact routeBDiskBoundSq_nonneg _ _ _ _
  have hullSqrt (hi : ℤ) (hhi : S ≤ (hi : ℝ) / (dyadicScale : ℝ)) :
      (DyadicInterval.sqrt (dyadicUpperHull hi)).Contains (Real.sqrt S) := by
    have hHull := dyadicUpperHull_contains hS0 hhi
    exact hHull.sqrt hHull.ordered (by simp [dyadicUpperHull])
  by_cases hLow : a.hi ≤ checkerKappaLower.lo
  · have haUpperLe : a.upper ≤ checkerKappaLower.lower :=
      dyadic_upper_le_lower_of_hi_le_lo hLow
    have haKappa : routeBTransition (routeBDboundR rhoR zR) ≤ routeBKappa :=
      calc
        routeBTransition (routeBDboundR rhoR zR) ≤ a.upper := ha.2
        _ ≤ checkerKappaLower.lower := haUpperLe
        _ ≤ routeBKappaLower := checkerKappaLower_contains.1
        _ ≤ routeBKappa := routeBKappa_gt_lower.le
    have hSq : S ≤ max (routeBDboundV0 rhoR zR vR) (routeBDboundVa rhoR zR vR) := by
      simpa only [S] using
        routeBDiskBoundSq_le_Dbound_V0_Va hrhoR hz0 hz1 hv0 haKappa
    have hUpper : S ≤ max V0.upper Va.upper := hSq.trans <| max_le
      (hV0.2.trans (le_max_left _ _)) (hVa.2.trans (le_max_right _ _))
    rw [dyadic_max_upper_eq] at hUpper
    have hsqrt := hullSqrt (max V0.hi Va.hi) hUpper
    simpa [dyadicPrawitzDbound, V0, Va, Vk, a, hLow,
      routeBDiskBound, S] using hsqrt
  · by_cases hHigh : checkerKappaUpper.hi ≤ a.lo
    · have hUpperLeA : checkerKappaUpper.upper ≤ a.lower :=
        dyadic_upper_le_lower_of_hi_le_lo hHigh
      have hKappaA : routeBKappa ≤ routeBTransition (routeBDboundR rhoR zR) :=
        calc
          routeBKappa ≤ routeBKappaUpper := routeBKappa_lt_upper.le
          _ ≤ checkerKappaUpper.upper := checkerKappaUpper_contains.2
          _ ≤ a.lower := hUpperLeA
          _ ≤ routeBTransition (routeBDboundR rhoR zR) := ha.1
      have hSq : S ≤ max (routeBDboundV0 rhoR zR vR) (routeBDboundVk rhoR zR vR) := by
        simpa only [S] using
          routeBDiskBoundSq_le_Dbound_V0_Vk hrhoR hz0 hz1 hKappaA
      have hVkActual : routeBDboundVk rhoR zR vR ≤ Vk.upper :=
        (routeBDboundVk_le_checker hrhoR hz0 hv0).trans hVk.2
      have hUpper : S ≤ max V0.upper Vk.upper := hSq.trans <| max_le
        (hV0.2.trans (le_max_left _ _)) (hVkActual.trans (le_max_right _ _))
      rw [dyadic_max_upper_eq] at hUpper
      have hsqrt := hullSqrt (max V0.hi Vk.hi) hUpper
      simpa [dyadicPrawitzDbound, V0, Va, Vk, a, hLow, hHigh,
        routeBDiskBound, S] using hsqrt
    · have hSq : S ≤ max (routeBDboundV0 rhoR zR vR)
          (max (routeBDboundVa rhoR zR vR) (routeBDboundVkChecker rhoR zR vR)) := by
        simpa only [S] using
          routeBDiskBoundSq_le_Dbound_all_candidates hrhoR hz0 hz1 hv0
      have hUpper : S ≤ max V0.upper (max Va.upper Vk.upper) := hSq.trans <| max_le
        (hV0.2.trans (le_max_left _ _))
        (max_le
          (hVa.2.trans ((le_max_left _ _).trans (le_max_right _ _)))
          (hVk.2.trans ((le_max_right _ _).trans (le_max_right _ _))))
      have hscale : (0 : ℝ) ≤ (dyadicScale : ℝ) := by
        exact_mod_cast dyadicScale_pos.le
      have hUpper' : S ≤
          ((max (max V0.hi Va.hi) Vk.hi : ℤ) : ℝ) / (dyadicScale : ℝ) := by
        simpa [DyadicInterval.upper, Int.cast_max, max_div_div_right hscale,
          max_assoc] using hUpper
      have hsqrt := hullSqrt (max (max V0.hi Va.hi) Vk.hi) hUpper'
      simpa [dyadicPrawitzDbound, V0, Va, Vk, a, hLow, hHigh,
        routeBDiskBound, S] using hsqrt

theorem routeBDiskBound_le_dyadicPrawitzDbound_upper
    {rho z v : DyadicInterval} {rhoR zR vR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (hv : v.Contains vR)
    (hrhoLo : 0 < rho.lo)
    (hyDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (DyadicInterval.sqr (dyadicDboundW rho z))).lo)
    (hCDen : 0 < (DyadicInterval.mul (DyadicInterval.point 4)
      (dyadicDboundW rho z)).lo)
    (hrhoR : 0 < rhoR) (hz0 : 0 ≤ zR) (hz1 : zR ≤ rhoR)
    (hv0 : 0 ≤ vR) (hy3 : routeBDboundY rhoR zR vR ≤ 3) :
    routeBDiskBound routeBKappa rhoR (routeBDboundR rhoR zR)
        (routeBDboundFrequency rhoR zR vR) ≤
      (dyadicPrawitzDbound rho z v).upper :=
  (dyadicPrawitzDbound_sound hrho hz hv hrhoLo hyDen hCDen
    hrhoR hz0 hz1 hv0 hy3).2

end


end BerryEsseen
