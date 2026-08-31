import BerryEsseen.Smoothing.PrawitzLargeNCell
import BerryEsseen.Certificate.LargeN.Disk
import BerryEsseen.Certificate.Dyadic.CellPartition
/-!
# Verifier-matching direct large-`n` cells

This module transcribes the per-cell arithmetic in the supplied checker's
`tail_direct` routine.  Its definitions preserve the checker's fixed-point
operation order; the external program is therefore only a certificate
generator, while Lean proves containment of the real cell semantics.
-/

namespace BerryEsseen

open DyadicInterval

def dyadicRouteBLargeAlpha : DyadicInterval :=
  DyadicInterval.ofRat 99 100

def dyadicLargeDen (L r : DyadicInterval) : DyadicInterval :=
  DyadicInterval.mul (DyadicInterval.sqr r) (DyadicInterval.sqr L)

def dyadicLargeQ
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  DyadicInterval.maxZero
    (DyadicInterval.div (dyadicCellLowerPoint c.hq) (dyadicLargeDen L r))

def dyadicLargeM
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  dyadicExpNeg (dyadicLargeQ L r c)

def dyadicLargeNArg
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  DyadicInterval.div (DyadicInterval.sqr c.v)
    (DyadicInterval.mul (DyadicInterval.point 2) (dyadicLargeDen L r))

def dyadicLargeN
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  dyadicExpNeg (dyadicLargeNArg L r c)

def dyadicLargeD
    (r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  dyadicPrawitzDstar r c.v

def dyadicLargeAlphaExp
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  dyadicExpNeg
    (DyadicInterval.mul dyadicRouteBLargeAlpha (dyadicLargeQ L r c))

/-- Exact transcription of the `tel` expression in `tail_direct`. -/
def dyadicLargeTelescoping
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  let kernelFrequency := DyadicInterval.mul c.k0
    (DyadicInterval.mul (DyadicInterval.point 2)
      (DyadicInterval.mul (DyadicInterval.sqr c.t) dyadicCellTwoPiCubed))
  let diskScale := DyadicInterval.div (dyadicLargeD r c)
    (DyadicInterval.mul (powi r 3) (powi L 3))
  let withDisk := DyadicInterval.mul kernelFrequency diskScale
  let withExp := DyadicInterval.mul withDisk (dyadicLargeAlphaExp L r c)
  DyadicInterval.mul withExp (DyadicInterval.point 1)

/-- Exact transcription of the positive-`t` `triv` expression.  As in the
checker, the first cell receives a huge fallback interval. -/
def dyadicLargeTrivial
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  if 0 < c.t.lo then
    DyadicInterval.mul (DyadicInterval.mul (DyadicInterval.point 2) c.k0)
      (DyadicInterval.div
        (DyadicInterval.add (dyadicLargeM L r c) (dyadicLargeN L r c))
        (DyadicInterval.mul c.t L))
  else dyadicCellHuge

def dyadicLargeF1
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  ⟨0, min (dyadicLargeTelescoping L r c).hi
    (dyadicLargeTrivial L r c).hi⟩

def dyadicLargeF3
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  DyadicInterval.div
    (DyadicInterval.mul c.kd2 (dyadicLargeN L r c)) L

def dyadicLargeLowCellValue
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  DyadicInterval.add (dyadicLargeF1 L r c) (dyadicLargeF3 L r c)

def dyadicLargeF2
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  DyadicInterval.div
    (DyadicInterval.mul c.kh2 (dyadicLargeM L r c)) L

def dyadicLargeHighCellValue
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  dyadicLargeF2 L r c

/-- Parameter-box conditions needed by every direct large-`n` cell. -/
structure DyadicLargeBoxAdmissible
    (L r : DyadicInterval) : Prop where
  LPos : 0 < L.lo
  rPos : 0 < r.lo
  oneLeR : (DyadicInterval.point 1).hi ≤ r.lo
  rLeTwo : r.hi ≤ (DyadicInterval.point 2).lo
  denPos : 0 < (dyadicLargeDen L r).lo
  normalDenPos : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
    (dyadicLargeDen L r)).lo
  diskDenPos : 0 < (DyadicInterval.mul (powi r 3) (powi L 3)).lo

structure DyadicLargeLowCellAdmissible
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : Prop where
  normalArgNonnegative : 0 ≤ (dyadicLargeNArg L r c).lo
  alphaArgNonnegative : 0 ≤ (DyadicInterval.mul dyadicRouteBLargeAlpha
    (dyadicLargeQ L r c)).lo
  trivialDen : 0 < c.t.lo → 0 < (DyadicInterval.mul c.t L).lo
  hugeFallback : ¬ 0 < c.t.lo →
    (dyadicLargeTelescoping L r c).hi ≤ dyadicCellHuge.hi
  cotDenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
    (DyadicInterval.sub (DyadicInterval.point 1)
      (DyadicInterval.sqr c.t))).lo
  valueOrdered : (dyadicLargeLowCellValue L r c).Ordered

structure DyadicLargeHighCellAdmissible
    (L r : DyadicInterval) (c : DyadicPrawitzCell) : Prop where
  cotDenom : 0 < (DyadicInterval.mul (DyadicInterval.point 4725)
    (DyadicInterval.sub (DyadicInterval.point 1)
      (DyadicInterval.sqr (DyadicInterval.sub (DyadicInterval.point 1) c.t)))).lo
  valueOrdered : (dyadicLargeHighCellValue L r c).Ordered

instance (L r : DyadicInterval) :
    Decidable (DyadicLargeBoxAdmissible L r) :=
  decidable_of_iff
    (0 < L.lo ∧
      0 < r.lo ∧
      (DyadicInterval.point 1).hi ≤ r.lo ∧
      r.hi ≤ (DyadicInterval.point 2).lo ∧
      0 < (dyadicLargeDen L r).lo ∧
      0 < (DyadicInterval.mul (DyadicInterval.point 2)
        (dyadicLargeDen L r)).lo ∧
      0 < (DyadicInterval.mul (powi r 3) (powi L 3)).lo) <| by
        constructor
        · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
          exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
        · intro h
          exact ⟨h.LPos, h.rPos, h.oneLeR, h.rLeTwo, h.denPos,
            h.normalDenPos, h.diskDenPos⟩

instance (L r : DyadicInterval) (c : DyadicPrawitzCell) :
    Decidable (DyadicLargeLowCellAdmissible L r c) :=
  decidable_of_iff
    (0 ≤ (dyadicLargeNArg L r c).lo ∧
      0 ≤ (DyadicInterval.mul dyadicRouteBLargeAlpha
        (dyadicLargeQ L r c)).lo ∧
      (0 < c.t.lo → 0 < (DyadicInterval.mul c.t L).lo) ∧
      (¬ 0 < c.t.lo →
        (dyadicLargeTelescoping L r c).hi ≤ dyadicCellHuge.hi) ∧
      0 < (DyadicInterval.mul (DyadicInterval.point 4725)
        (DyadicInterval.sub (DyadicInterval.point 1)
          (DyadicInterval.sqr c.t))).lo ∧
      (dyadicLargeLowCellValue L r c).lo ≤
        (dyadicLargeLowCellValue L r c).hi) <| by
        constructor
        · rintro ⟨h1, h2, h3, h4, h5, h6⟩
          exact ⟨h1, h2, h3, h4, h5, h6⟩
        · intro h
          exact ⟨h.normalArgNonnegative, h.alphaArgNonnegative, h.trivialDen,
            h.hugeFallback, h.cotDenom, h.valueOrdered⟩

instance (L r : DyadicInterval) (c : DyadicPrawitzCell) :
    Decidable (DyadicLargeHighCellAdmissible L r c) :=
  decidable_of_iff
    (0 < (DyadicInterval.mul (DyadicInterval.point 4725)
        (DyadicInterval.sub (DyadicInterval.point 1)
          (DyadicInterval.sqr
            (DyadicInterval.sub (DyadicInterval.point 1) c.t)))).lo ∧
      (dyadicLargeHighCellValue L r c).lo ≤
        (dyadicLargeHighCellValue L r c).hi) <| by
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2⟩
        · intro h
          exact ⟨h.cotDenom, h.valueOrdered⟩

noncomputable section

theorem dyadicRouteBLargeAlpha_sound :
    dyadicRouteBLargeAlpha.Contains routeBLargeNAlpha := by
  simpa [dyadicRouteBLargeAlpha, routeBLargeNAlpha] using
    DyadicInterval.contains_ofRat 99 (b := 100) (by norm_num)

theorem dyadicLargeDen_sound
    {L r : DyadicInterval} {LR rR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) :
    (dyadicLargeDen L r).Contains (rR ^ 2 * LR ^ 2) := by
  have hr2 := hr.sqr hr.ordered
  have hL2 := hL.sqr hL.ordered
  simpa [dyadicLargeDen] using hr2.mul hL2

theorem dyadicLargeQ_sound
    {L r : DyadicInterval} {c : DyadicPrawitzCell} {LR rR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR)
    (hden : 0 < (dyadicLargeDen L r).lo) :
    (dyadicLargeQ L r c).Contains
      (routeBLargeCellQLower LR rR c.hq.lower) := by
  have hhq := dyadicCellLowerPoint_contains c.hq
  have hdenSound := dyadicLargeDen_sound hL hr
  have hquot := hhq.div hdenSound hdenSound.ordered hden
  have hresult := hquot.maxZero
  simpa [dyadicLargeQ, routeBLargeCellQLower, max_comm] using hresult

theorem dyadicLargeM_sound
    {L r : DyadicInterval} {c : DyadicPrawitzCell} {LR rR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR)
    (hden : 0 < (dyadicLargeDen L r).lo) :
    (dyadicLargeM L r c).Contains
      (routeBLargeCellM LR rR c.hq.lower) := by
  have hQ := dyadicLargeQ_sound (c := c) hL hr hden
  have hQlo : 0 ≤ (dyadicLargeQ L r c).lo := by
    simp [dyadicLargeQ, DyadicInterval.maxZero]
  simpa [dyadicLargeM, routeBLargeCellM] using dyadicExpNeg_sound hQ hQlo

theorem dyadicLargeNArg_sound
    {L r : DyadicInterval} {c : DyadicPrawitzCell} {LR rR vR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hv : c.v.Contains vR)
    (hden : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (dyadicLargeDen L r)).lo) :
    (dyadicLargeNArg L r c).Contains
      (vR ^ 2 / (2 * (rR ^ 2 * LR ^ 2))) := by
  have hv2 := hv.sqr hv.ordered
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hdenSound := htwo.mul (dyadicLargeDen_sound hL hr)
  simpa [dyadicLargeNArg] using hv2.div hdenSound hdenSound.ordered hden

theorem dyadicLargeN_sound
    {L r : DyadicInterval} {c : DyadicPrawitzCell} {LR rR vR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (hv : c.v.Contains vR)
    (hden : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (dyadicLargeDen L r)).lo)
    (harg : 0 ≤ (dyadicLargeNArg L r c).lo) :
    (dyadicLargeN L r c).Contains (routeBLargeCellN LR rR vR) := by
  have hNArg := dyadicLargeNArg_sound hL hr hv hden
  simpa [dyadicLargeN, routeBLargeCellN] using dyadicExpNeg_sound hNArg harg

theorem dyadicLargeAlphaExp_sound
    {L r : DyadicInterval} {c : DyadicPrawitzCell} {LR rR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR)
    (hden : 0 < (dyadicLargeDen L r).lo)
    (harg : 0 ≤ (DyadicInterval.mul dyadicRouteBLargeAlpha
      (dyadicLargeQ L r c)).lo) :
    (dyadicLargeAlphaExp L r c).Contains
      (Real.exp (-routeBLargeNAlpha *
        routeBLargeCellQLower LR rR c.hq.lower)) := by
  have hQ := dyadicLargeQ_sound (c := c) hL hr hden
  have hproduct := dyadicRouteBLargeAlpha_sound.mul hQ
  simpa [dyadicLargeAlphaExp] using dyadicExpNeg_sound hproduct harg

theorem dyadicLargeD_sound
    {r : DyadicInterval} {c : DyadicPrawitzCell} {rR vR : ℝ}
    (hr : r.Contains rR) (hv : c.v.Contains vR) (hrLo : 0 < r.lo)
    (hr1 : 1 ≤ rR) (hr2 : rR ≤ 2) (hv0 : 0 ≤ vR)
    (hy3 : (vR / rR) ^ 2 / 2 ≤ 3) :
    (dyadicLargeD r c).Contains (routeBDiskStar rR (vR / rR)) := by
  simpa [dyadicLargeD] using
    dyadicPrawitzDstar_sound hr hv hrLo hr1 hr2 hv0 hy3

theorem dyadicLargeTelescoping_sound
    {L r : DyadicInterval} {c : DyadicPrawitzCell}
    {LR rR tR k0R vR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (ht : c.t.Contains tR)
    (hk0 : c.k0.Contains k0R) (hv : c.v.Contains vR)
    (hrLo : 0 < r.lo) (hr1 : 1 ≤ rR) (hr2 : rR ≤ 2)
    (hv0 : 0 ≤ vR) (hy3 : (vR / rR) ^ 2 / 2 ≤ 3)
    (hden : 0 < (dyadicLargeDen L r).lo)
    (hexpArg : 0 ≤ (DyadicInterval.mul dyadicRouteBLargeAlpha
      (dyadicLargeQ L r c)).lo)
    (hdiskDen : 0 < (DyadicInterval.mul (powi r 3) (powi L 3)).lo) :
    (dyadicLargeTelescoping L r c).Contains
      (routeBLargeCellTelescoping LR rR tR k0R c.hq.lower
        (routeBDiskStar rR (vR / rR))) := by
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have ht2 := ht.sqr ht.ordered
  have hfrequency := ht2.mul dyadicCellTwoPiCubed_sound
  have hkernelFrequency := hk0.mul (htwo.mul hfrequency)
  have hD := dyadicLargeD_sound hr hv hrLo hr1 hr2 hv0 hy3
  have hr3 := powi_sound hr 3
  have hL3 := powi_sound hL 3
  have hdiskDenSound := hr3.mul hL3
  have hdiskScale := hD.div hdiskDenSound hdiskDenSound.ordered hdiskDen
  have hwithDisk := hkernelFrequency.mul hdiskScale
  have hexp := dyadicLargeAlphaExp_sound (c := c) hL hr hden hexpArg
  have hwithExp := hwithDisk.mul hexp
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have hresult := hwithExp.mul hone
  unfold dyadicLargeTelescoping routeBLargeCellTelescoping
  dsimp only
  convert hresult using 1 <;> ring

theorem dyadicLargeTrivial_sound
    {L r : DyadicInterval} {c : DyadicPrawitzCell}
    {LR rR tR k0R vR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (ht : c.t.Contains tR)
    (hk0 : c.k0.Contains k0R) (hv : c.v.Contains vR)
    (hden : 0 < (dyadicLargeDen L r).lo)
    (hnDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (dyadicLargeDen L r)).lo)
    (hnArg : 0 ≤ (dyadicLargeNArg L r c).lo)
    (htLo : 0 < c.t.lo) (htrDen : 0 < (DyadicInterval.mul c.t L).lo) :
    (dyadicLargeTrivial L r c).Contains
      (routeBLargeCellTrivial LR rR tR k0R c.hq.lower vR) := by
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hM := dyadicLargeM_sound (c := c) hL hr hden
  have hN := dyadicLargeN_sound hL hr hv hnDen hnArg
  have hsum := hM.add hN
  have htr := ht.mul hL
  have hquot := hsum.div htr htr.ordered htrDen
  have hresult := (htwo.mul hk0).mul hquot
  rw [dyadicLargeTrivial, if_pos htLo]
  simpa [routeBLargeCellTrivial] using hresult

theorem dyadicLargeF3_sound
    {L r : DyadicInterval} {c : DyadicPrawitzCell}
    {LR rR kd2R vR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR)
    (hkd2 : c.kd2.Contains kd2R) (hv : c.v.Contains vR)
    (hnDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (dyadicLargeDen L r)).lo)
    (hnArg : 0 ≤ (dyadicLargeNArg L r c).lo) (hLLo : 0 < L.lo) :
    (dyadicLargeF3 L r c).Contains (routeBLargeCellF3 LR rR kd2R vR) := by
  have hN := dyadicLargeN_sound hL hr hv hnDen hnArg
  have hnum := hkd2.mul hN
  have hresult := hnum.div hL hL.ordered hLLo
  simpa [dyadicLargeF3, routeBLargeCellF3] using hresult

theorem dyadicLargeF2_sound
    {L r : DyadicInterval} {c : DyadicPrawitzCell}
    {LR rR kh2R : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR)
    (hkh2 : c.kh2.Contains kh2R)
    (hden : 0 < (dyadicLargeDen L r).lo) (hLLo : 0 < L.lo) :
    (dyadicLargeF2 L r c).Contains
      (routeBLargeCellF2 LR rR kh2R c.hq.lower) := by
  have hM := dyadicLargeM_sound (c := c) hL hr hden
  have hnum := hkh2.mul hM
  have hresult := hnum.div hL hL.ordered hLLo
  simpa [dyadicLargeF2, routeBLargeCellF2] using hresult

theorem DyadicLargeBoxAdmissible.real_L_pos
    {L r : DyadicInterval} (hbox : DyadicLargeBoxAdmissible L r)
    {LR : ℝ} (hL : L.Contains LR) : 0 < LR := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  have hlower : 0 < L.lower := by
    unfold DyadicInterval.lower
    exact div_pos (by exact_mod_cast hbox.LPos) hscale
  exact hlower.trans_le hL.1

theorem DyadicLargeBoxAdmissible.real_r_pos
    {L r : DyadicInterval} (hbox : DyadicLargeBoxAdmissible L r)
    {rR : ℝ} (hr : r.Contains rR) : 0 < rR := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  have hlower : 0 < r.lower := by
    unfold DyadicInterval.lower
    exact div_pos (by exact_mod_cast hbox.rPos) hscale
  exact hlower.trans_le hr.1

theorem DyadicLargeBoxAdmissible.real_one_le_r
    {L r : DyadicInterval} (hbox : DyadicLargeBoxAdmissible L r)
    {rR : ℝ} (hr : r.Contains rR) : 1 ≤ rR := by
  have hmiddle := dyadic_upper_le_lower_of_hi_le_lo hbox.oneLeR
  have hone : (DyadicInterval.point 1).upper = (1 : ℝ) := by
    simp [DyadicInterval.upper, DyadicInterval.point, dyadicScale_pos.ne']
  rw [hone] at hmiddle
  exact hmiddle.trans hr.1

theorem DyadicLargeBoxAdmissible.real_r_le_two
    {L r : DyadicInterval} (hbox : DyadicLargeBoxAdmissible L r)
    {rR : ℝ} (hr : r.Contains rR) : rR ≤ 2 := by
  have hmiddle := dyadic_upper_le_lower_of_hi_le_lo hbox.rLeTwo
  have htwo : (DyadicInterval.point 2).lower = (2 : ℝ) := by
    simp [DyadicInterval.lower, DyadicInterval.point, dyadicScale_pos.ne']
  rw [htwo] at hmiddle
  exact hr.2.trans hmiddle

theorem routeBLargeLowerDifference_le_dyadicLargeF1_upper
    {L r : DyadicInterval} {c : DyadicPrawitzCell}
    {LR rR tR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (ht : c.t.Contains tR)
    (hv : c.v.Contains (routeBCellV tR))
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hk0 : c.k0.Contains (prawitzK0Envelope tR))
    (hbox : DyadicLargeBoxAdmissible L r)
    (hcell : DyadicLargeLowCellAdmissible L r c)
    (ht0 : 0 ≤ tR) (ht1 : tR ≤ prawitzSplit) :
    routeBLargeLowerDifferenceIntegrand LR rR tR ≤
      (dyadicLargeF1 L r c).upper := by
  have hLR := hbox.real_L_pos hL
  have hrR := hbox.real_r_pos hr
  have hr1 := hbox.real_one_le_r hr
  have hr2 := hbox.real_r_le_two hr
  have hy3 := routeBLargeDstar_y_le_three hr1 ht0 ht1
  have hk0Real : tR * ‖prawitzKernel tR‖ ≤ prawitzK0Envelope tR :=
    t_mul_norm_prawitzKernel_le_K0Envelope ht0
      (ht1.trans_lt (by norm_num [prawitzSplit]))
  have hTelContains := dyadicLargeTelescoping_sound
    (LR := LR) (rR := rR) (tR := tR) (k0R := prawitzK0Envelope tR)
    (vR := routeBCellV tR) hL hr ht hk0 hv hbox.rPos hr1 hr2
      (by unfold routeBCellV; positivity) hy3 hbox.denPos
      hcell.alphaArgNonnegative hbox.diskDenPos
  have hTelReal := routeBLargeLowerDifference_le_cellTelescoping
    hLR hrR ht0 hhq hk0Real le_rfl
  have hTelUpper : routeBLargeLowerDifferenceIntegrand LR rR tR ≤
      (dyadicLargeTelescoping L r c).upper := hTelReal.trans hTelContains.2
  have hTrivUpper : routeBLargeLowerDifferenceIntegrand LR rR tR ≤
      (dyadicLargeTrivial L r c).upper := by
    by_cases htLo : 0 < c.t.lo
    · have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
      have hcLowerPos : 0 < c.t.lower := by
        unfold DyadicInterval.lower
        exact div_pos (by exact_mod_cast htLo) hscale
      have htRPos : 0 < tR := hcLowerPos.trans_le ht.1
      have hTrivContains := dyadicLargeTrivial_sound
        (LR := LR) (rR := rR) (tR := tR) (k0R := prawitzK0Envelope tR)
        (vR := routeBCellV tR) hL hr ht hk0 hv hbox.denPos
          hbox.normalDenPos hcell.normalArgNonnegative htLo (hcell.trivialDen htLo)
      exact (routeBLargeLowerDifference_le_cellTrivial
        hLR hrR htRPos hhq hk0Real).trans hTrivContains.2
    · rw [dyadicLargeTrivial, if_neg htLo]
      have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
      exact hTelUpper.trans
        (div_le_div_of_nonneg_right
          (by exact_mod_cast hcell.hugeFallback htLo) hscale.le)
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  change routeBLargeLowerDifferenceIntegrand LR rR tR ≤
    ((min (dyadicLargeTelescoping L r c).hi
      (dyadicLargeTrivial L r c).hi : ℤ) : ℝ) / (dyadicScale : ℝ)
  rw [Int.cast_min, ← min_div_div_right hscale.le]
  exact le_min hTelUpper hTrivUpper

theorem routeBLargeCorrection_le_dyadicLargeF3_upper
    {L r : DyadicInterval} {c : DyadicPrawitzCell}
    {LR rR tR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR)
    (hv : c.v.Contains (routeBCellV tR))
    (hkd2 : c.kd2.Contains (prawitzKD2Envelope tR))
    (hbox : DyadicLargeBoxAdmissible L r)
    (hcell : DyadicLargeLowCellAdmissible L r c)
    (ht0 : 0 ≤ tR) (ht1 : tR < 1) :
    routeBLargeCorrectionIntegrand LR rR tR ≤
      (dyadicLargeF3 L r c).upper := by
  have hLR := hbox.real_L_pos hL
  have hF3 := dyadicLargeF3_sound
    (LR := LR) (rR := rR) (kd2R := prawitzKD2Envelope tR)
    (vR := routeBCellV tR) hL hr hkd2 hv hbox.normalDenPos
      hcell.normalArgNonnegative hbox.LPos
  have hkernel : 2 * ‖prawitzKernelCorrection tR‖ ≤
      prawitzKD2Envelope tR :=
    two_mul_norm_prawitzKernelCorrection_le_KD2Envelope ht0 ht1
  exact (routeBLargeCorrection_le_cellF3 hLR hkernel).trans hF3.2

theorem routeBLargeLowIntegrand_le_dyadicLargeLowCellValue_upper
    {L r : DyadicInterval} {c : DyadicPrawitzCell}
    {LR rR tR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR) (ht : c.t.Contains tR)
    (hv : c.v.Contains (routeBCellV tR))
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hk0 : c.k0.Contains (prawitzK0Envelope tR))
    (hkd2 : c.kd2.Contains (prawitzKD2Envelope tR))
    (hbox : DyadicLargeBoxAdmissible L r)
    (hcell : DyadicLargeLowCellAdmissible L r c)
    (ht0 : 0 ≤ tR) (ht1 : tR ≤ prawitzSplit) :
    routeBLargeLowerDifferenceIntegrand LR rR tR +
        routeBLargeCorrectionIntegrand LR rR tR ≤
      (dyadicLargeLowCellValue L r c).upper := by
  have hF1 := routeBLargeLowerDifference_le_dyadicLargeF1_upper
    hL hr ht hv hhq hk0 hbox hcell ht0 ht1
  have hF3 := routeBLargeCorrection_le_dyadicLargeF3_upper
    hL hr hv hkd2 hbox hcell ht0
      (ht1.trans_lt (by norm_num [prawitzSplit]))
  have hsum := add_le_add hF1 hF3
  simpa [dyadicLargeLowCellValue, DyadicInterval.add, DyadicInterval.upper,
    Int.cast_add, add_div] using hsum

theorem routeBLargeHighIntegrand_le_dyadicLargeHighCellValue_upper
    {L r : DyadicInterval} {c : DyadicPrawitzCell}
    {LR rR tR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR)
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hkh2 : c.kh2.Contains (prawitzKH2Envelope tR))
    (hbox : DyadicLargeBoxAdmissible L r)
    (_hcell : DyadicLargeHighCellAdmissible L r c)
    (ht0 : 0 < tR) (ht1 : tR ≤ 1) :
    routeBLargeHighIntegrand LR rR tR ≤
      (dyadicLargeHighCellValue L r c).upper := by
  have hLR := hbox.real_L_pos hL
  have hrR := hbox.real_r_pos hr
  have hF2 := dyadicLargeF2_sound
    (LR := LR) (rR := rR) (kh2R := prawitzKH2Envelope tR)
      hL hr hkh2 hbox.denPos hbox.LPos
  have hkernel : 2 * ‖prawitzKernel tR‖ ≤ prawitzKH2Envelope tR :=
    two_mul_norm_prawitzKernel_le_KH2Envelope ht0 ht1
  exact (routeBLargeHigh_le_cellF2 hLR hrR ht0.le hhq hkernel).trans hF2.2

end

end BerryEsseen
