import BerryEsseen.Smoothing.PrawitzFiniteCell
import BerryEsseen.Certificate.Dyadic.Dbound
import BerryEsseen.Certificate.Dyadic.Power
/-!
# Verifier-matching finite-cell evaluator

This module transcribes the per-cell arithmetic in the supplied checker's `finite_bound` routine.
The construction deliberately preserves the checker's multiplication, division, power, branch,
and endpoint-selection order.  Soundness is proved against the real cell semantics in
`PrawitzFiniteCell.lean` before the evaluator is connected to a concrete partition and the
exhaustive parameter traversal.
-/

namespace BerryEsseen

open DyadicInterval

structure DyadicPrawitzCell where
  t : DyadicInterval
  wid : DyadicInterval
  k0 : DyadicInterval
  kd2 : DyadicInterval
  kh2 : DyadicInterval
  hq : DyadicInterval
  v : DyadicInterval
deriving DecidableEq, Repr

def dyadicCellLowerPoint (I : DyadicInterval) : DyadicInterval := ⟨I.lo, I.lo⟩

def dyadicCellNonnegativeHull
    (I J : DyadicInterval) : DyadicInterval := ⟨0, max I.hi J.hi⟩

def dyadicCellHuge : DyadicInterval := ⟨0, (2 : ℤ) ^ 126⟩

def dyadicCellSqrtN (n : ℕ) : DyadicInterval :=
  DyadicInterval.sqrt (DyadicInterval.point (Int.ofNat n))

def dyadicCellP (rho : DyadicInterval) : DyadicInterval :=
  DyadicInterval.div (DyadicInterval.point 1) rho

def dyadicCellW (rho z : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add rho z

def dyadicCellW2 (rho z : DyadicInterval) : DyadicInterval :=
  DyadicInterval.sqr (dyadicCellW rho z)

def dyadicCellA2
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  DyadicInterval.maxZero
    (DyadicInterval.sub (DyadicInterval.point 1)
      (DyadicInterval.div
        (DyadicInterval.mul (DyadicInterval.point 2) (dyadicCellLowerPoint c.hq))
        (dyadicCellW2 rho z)))

def dyadicCellA
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  DyadicInterval.sqrt (dyadicCellA2 rho z c)

def dyadicCellBArg
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  DyadicInterval.div (DyadicInterval.sqr c.v)
    (DyadicInterval.mul (DyadicInterval.point 2) (dyadicCellW2 rho z))

def dyadicCellB
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  dyadicExpNeg (dyadicCellBArg rho z c)

def dyadicCellM
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  powi (dyadicCellA rho z c) n

def dyadicCellNArg
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  DyadicInterval.div
    (DyadicInterval.mul (DyadicInterval.point (Int.ofNat n))
      (DyadicInterval.sqr c.v))
    (DyadicInterval.mul (DyadicInterval.point 2) (dyadicCellW2 rho z))

def dyadicCellN
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  dyadicExpNeg (dyadicCellNArg n rho z c)

def dyadicCellH
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  powi (dyadicCellNonnegativeHull (dyadicCellA rho z c) (dyadicCellB rho z c))
    (n - 1)

def dyadicCellD
    (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  dyadicPrawitzDbound rho z c.v

def dyadicCellTwoPiCubed : DyadicInterval :=
  powi (DyadicInterval.mul (DyadicInterval.point 2) checkerPi) 3

def dyadicCellTelescoping
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  let prefactor := DyadicInterval.mul
    (DyadicInterval.point (Int.ofNat (2 * n))) (dyadicCellSqrtN n)
  let withKernel := DyadicInterval.mul prefactor c.k0
  let frequency := DyadicInterval.mul (DyadicInterval.sqr c.t) dyadicCellTwoPiCubed
  let withFrequency := DyadicInterval.mul withKernel frequency
  let diskScale := DyadicInterval.div (dyadicCellD rho z c)
    (powi (dyadicCellW rho z) 3)
  let withDisk := DyadicInterval.mul withFrequency diskScale
  DyadicInterval.mul withDisk (dyadicCellH n rho z c)

def dyadicCellTrivial
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  if 0 < c.t.lo then
    DyadicInterval.mul
      (DyadicInterval.mul
        (DyadicInterval.mul (DyadicInterval.point 2) (dyadicCellSqrtN n))
        (dyadicCellP rho))
      (DyadicInterval.mul c.k0
        (DyadicInterval.div
          (DyadicInterval.add (dyadicCellM n rho z c) (dyadicCellN n rho z c)) c.t))
  else dyadicCellHuge

def dyadicCellF1
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  ⟨0, min (dyadicCellTelescoping n rho z c).hi
    (dyadicCellTrivial n rho z c).hi⟩

def dyadicCellF3
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  DyadicInterval.mul
    (DyadicInterval.mul (dyadicCellSqrtN n) (dyadicCellP rho))
    (DyadicInterval.mul c.kd2 (dyadicCellN n rho z c))

def dyadicLowCellValue
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  DyadicInterval.add (dyadicCellF1 n rho z c) (dyadicCellF3 n rho z c)

def dyadicCellF2
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  DyadicInterval.mul
    (DyadicInterval.mul (dyadicCellSqrtN n) (dyadicCellP rho))
    (DyadicInterval.mul c.kh2 (dyadicCellM n rho z c))

def dyadicHighCellValue
    (n : ℕ) (rho z : DyadicInterval) (c : DyadicPrawitzCell) : DyadicInterval :=
  dyadicCellF2 n rho z c

noncomputable section

theorem dyadicCellLowerPoint_contains (I : DyadicInterval) :
    (dyadicCellLowerPoint I).Contains I.lower := by
  constructor <;> rfl

theorem dyadicCellNonnegativeHull_contains
    {I J : DyadicInterval} {x y : ℝ}
    (hI : I.Contains x) (hJ : J.Contains y) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (dyadicCellNonnegativeHull I J).Contains (max x y) := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  constructor
  · simpa [dyadicCellNonnegativeHull, DyadicInterval.lower] using
      hx.trans (le_max_left x y)
  · change max x y ≤ ((max I.hi J.hi : ℤ) : ℝ) / (dyadicScale : ℝ)
    rw [Int.cast_max, ← max_div_div_right hscale.le]
    exact max_le_max hI.2 hJ.2

theorem dyadicCellSqrtN_sound (n : ℕ) :
    (dyadicCellSqrtN n).Contains (Real.sqrt (n : ℝ)) := by
  have hn : (DyadicInterval.point (Int.ofNat n)).Contains (n : ℝ) := by
    simpa using DyadicInterval.contains_point (Int.ofNat n)
  have hordered : (DyadicInterval.point (Int.ofNat n)).Ordered := by
    simp [DyadicInterval.Ordered, DyadicInterval.point]
  have hlo : 0 ≤ (DyadicInterval.point (Int.ofNat n)).lo := by
    simp only [DyadicInterval.point]
    exact mul_nonneg (by simp) dyadicScale_pos.le
  simpa [dyadicCellSqrtN] using hn.sqrt hordered hlo

theorem dyadicCellP_sound {rho : DyadicInterval} {rhoR : ℝ}
    (hrho : rho.Contains rhoR) (hrhoLo : 0 < rho.lo) :
    (dyadicCellP rho).Contains (routeBDboundP rhoR) := by
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have hdiv := hone.div hrho hrho.ordered hrhoLo
  simpa [dyadicCellP, routeBDboundP] using hdiv

theorem dyadicCellW_sound {rho z : DyadicInterval} {rhoR zR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) :
    (dyadicCellW rho z).Contains (routeBDboundW rhoR zR) := by
  simpa [dyadicCellW, routeBDboundW] using hrho.add hz

theorem dyadicCellW2_sound {rho z : DyadicInterval} {rhoR zR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) :
    (dyadicCellW2 rho z).Contains (routeBDboundW rhoR zR ^ 2) := by
  have hw := dyadicCellW_sound hrho hz
  simpa [dyadicCellW2] using hw.sqr hw.ordered

theorem dyadicCellA2_sound
    {rho z : DyadicInterval} {c : DyadicPrawitzCell} {rhoR zR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hW2Den : 0 < (dyadicCellW2 rho z).lo) :
    (dyadicCellA2 rho z c).Contains
      (max (1 - 2 * c.hq.lower / routeBDboundW rhoR zR ^ 2) 0) := by
  have hone : (DyadicInterval.point 1).Contains (1 : ℝ) := by
    simpa using DyadicInterval.contains_point (1 : ℤ)
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hhq := dyadicCellLowerPoint_contains c.hq
  have hw2 := dyadicCellW2_sound hrho hz
  have hquot := (htwo.mul hhq).div hw2 hw2.ordered hW2Den
  have hresult := (hone.sub hquot).maxZero
  simpa [dyadicCellA2, max_comm] using hresult

theorem dyadicCellA_sound
    {rho z : DyadicInterval} {c : DyadicPrawitzCell} {rhoR zR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hW2Den : 0 < (dyadicCellW2 rho z).lo) :
    (dyadicCellA rho z c).Contains (routeBCellA rhoR zR c.hq.lower) := by
  have hA2 := dyadicCellA2_sound (c := c) hrho hz hW2Den
  have hA2Lo : 0 ≤ (dyadicCellA2 rho z c).lo := by
    simp [dyadicCellA2, DyadicInterval.maxZero]
  have hsqrt := hA2.sqrt hA2.ordered hA2Lo
  simpa [dyadicCellA, routeBCellA] using hsqrt

theorem dyadicCellBArg_sound
    {rho z : DyadicInterval} {c : DyadicPrawitzCell} {rhoR zR vR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (hv : c.v.Contains vR)
    (hBDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (dyadicCellW2 rho z)).lo) :
    (dyadicCellBArg rho z c).Contains
      (vR ^ 2 / (2 * routeBDboundW rhoR zR ^ 2)) := by
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hv2 := hv.sqr hv.ordered
  have hw2 := dyadicCellW2_sound hrho hz
  have hden := htwo.mul hw2
  simpa [dyadicCellBArg] using hv2.div hden hden.ordered hBDen

theorem dyadicCellB_sound
    {rho z : DyadicInterval} {c : DyadicPrawitzCell} {rhoR zR vR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (hv : c.v.Contains vR)
    (hBDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (dyadicCellW2 rho z)).lo)
    (hBArgLo : 0 ≤ (dyadicCellBArg rho z c).lo) :
    (dyadicCellB rho z c).Contains
      (Real.exp (-(vR ^ 2 / (2 * routeBDboundW rhoR zR ^ 2)))) := by
  have harg := dyadicCellBArg_sound hrho hz hv hBDen
  simpa [dyadicCellB] using dyadicExpNeg_sound harg hBArgLo

theorem dyadicCellNArg_sound
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell} {rhoR zR vR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (hv : c.v.Contains vR)
    (hBDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (dyadicCellW2 rho z)).lo) :
    (dyadicCellNArg n rho z c).Contains
      ((n : ℝ) * vR ^ 2 / (2 * routeBDboundW rhoR zR ^ 2)) := by
  have hn : (DyadicInterval.point (Int.ofNat n)).Contains (n : ℝ) := by
    simpa using DyadicInterval.contains_point (Int.ofNat n)
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hv2 := hv.sqr hv.ordered
  have hw2 := dyadicCellW2_sound hrho hz
  have hden := htwo.mul hw2
  simpa [dyadicCellNArg] using (hn.mul hv2).div hden hden.ordered hBDen

theorem dyadicCellN_sound
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell} {rhoR zR vR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (hv : c.v.Contains vR)
    (hBDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (dyadicCellW2 rho z)).lo)
    (hNArgLo : 0 ≤ (dyadicCellNArg n rho z c).lo) :
    (dyadicCellN n rho z c).Contains
      (Real.exp (-((n : ℝ) * vR ^ 2 /
        (2 * routeBDboundW rhoR zR ^ 2)))) := by
  have harg := dyadicCellNArg_sound (n := n) hrho hz hv hBDen
  simpa [dyadicCellN] using dyadicExpNeg_sound harg hNArgLo

theorem dyadicCellB_route_sound
    {rho z : DyadicInterval} {c : DyadicPrawitzCell} {rhoR zR tR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hv : c.v.Contains (routeBCellV tR))
    (hBDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (dyadicCellW2 rho z)).lo)
    (hBArgLo : 0 ≤ (dyadicCellBArg rho z c).lo) :
    (dyadicCellB rho z c).Contains (routeBCellB rhoR zR tR) := by
  unfold routeBCellB
  convert dyadicCellB_sound hrho hz hv hBDen hBArgLo using 1 <;> ring

theorem dyadicCellM_sound
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell} {rhoR zR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hW2Den : 0 < (dyadicCellW2 rho z).lo) :
    (dyadicCellM n rho z c).Contains (routeBCellA rhoR zR c.hq.lower ^ n) := by
  simpa [dyadicCellM] using powi_sound (dyadicCellA_sound (c := c) hrho hz hW2Den) n

theorem dyadicCellN_route_sound
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell} {rhoR zR tR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hv : c.v.Contains (routeBCellV tR))
    (hBDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (dyadicCellW2 rho z)).lo)
    (hNArgLo : 0 ≤ (dyadicCellNArg n rho z c).lo) :
    (dyadicCellN n rho z c).Contains (routeBCellN n rhoR zR tR) := by
  unfold routeBCellN
  convert dyadicCellN_sound (n := n) hrho hz hv hBDen hNArgLo using 1 <;> ring

theorem dyadicCellH_sound
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell} {rhoR zR tR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hv : c.v.Contains (routeBCellV tR))
    (hW2Den : 0 < (dyadicCellW2 rho z).lo)
    (hBDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (dyadicCellW2 rho z)).lo)
    (hBArgLo : 0 ≤ (dyadicCellBArg rho z c).lo) :
    (dyadicCellH n rho z c).Contains
      (routeBCellH n rhoR zR tR c.hq.lower) := by
  have hA := dyadicCellA_sound (c := c) hrho hz hW2Den
  have hB := dyadicCellB_route_sound hrho hz hv hBDen hBArgLo
  have hhull := dyadicCellNonnegativeHull_contains hA hB
    (Real.sqrt_nonneg _) (Real.exp_pos _).le
  simpa [dyadicCellH, routeBCellH] using powi_sound hhull (n - 1)

theorem dyadicCellTwoPiCubed_sound :
    dyadicCellTwoPiCubed.Contains ((2 * Real.pi) ^ 3) := by
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hbase := htwo.mul checkerPi_contains_pi
  simpa [dyadicCellTwoPiCubed] using powi_sound hbase 3

theorem dyadicCellD_sound
    {rho z : DyadicInterval} {c : DyadicPrawitzCell} {rhoR zR vR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (hv : c.v.Contains vR)
    (hrhoLo : 0 < rho.lo)
    (hyDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (DyadicInterval.sqr (dyadicCellW rho z))).lo)
    (hCDen : 0 < (DyadicInterval.mul (DyadicInterval.point 4)
      (dyadicCellW rho z)).lo)
    (hrhoR : 0 < rhoR) (hz0 : 0 ≤ zR) (hz1 : zR ≤ rhoR)
    (hv0 : 0 ≤ vR) (hy3 : routeBDboundY rhoR zR vR ≤ 3) :
    (dyadicCellD rho z c).Contains
      (routeBDiskBound routeBKappa rhoR (routeBDboundR rhoR zR)
        (routeBDboundFrequency rhoR zR vR)) := by
  simpa [dyadicCellD, dyadicCellW] using
    dyadicPrawitzDbound_sound hrho hz hv hrhoLo hyDen hCDen
      hrhoR hz0 hz1 hv0 hy3

theorem dyadicCellTelescoping_sound_of_components
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    {rhoR zR tR k0R DR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (ht : c.t.Contains tR)
    (hk0 : c.k0.Contains k0R)
    (hD : (dyadicCellD rho z c).Contains DR)
    (hH : (dyadicCellH n rho z c).Contains
      (routeBCellH n rhoR zR tR c.hq.lower))
    (hW3Den : 0 < (powi (dyadicCellW rho z) 3).lo) :
    (dyadicCellTelescoping n rho z c).Contains
      (routeBCellTelescopingBound n rhoR zR tR k0R c.hq.lower DR) := by
  have h2n : (DyadicInterval.point (Int.ofNat (2 * n))).Contains
      (2 * (n : ℝ)) := by
    simpa [Nat.cast_mul] using DyadicInterval.contains_point (Int.ofNat (2 * n))
  have hsn := dyadicCellSqrtN_sound n
  have hprefactor := h2n.mul hsn
  have hwithKernel := hprefactor.mul hk0
  have ht2 := ht.sqr ht.ordered
  have hfrequency := ht2.mul dyadicCellTwoPiCubed_sound
  have hwithFrequency := hwithKernel.mul hfrequency
  have hw := dyadicCellW_sound hrho hz
  have hw3 := powi_sound hw 3
  have hdiskScale := hD.div hw3 hw3.ordered hW3Den
  have hwithDisk := hwithFrequency.mul hdiskScale
  have hresult := hwithDisk.mul hH
  unfold dyadicCellTelescoping
  dsimp only
  convert hresult using 1

theorem dyadicCellTrivial_sound_of_components
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    {rhoR zR tR k0R : ℝ}
    (hrho : rho.Contains rhoR) (ht : c.t.Contains tR)
    (hk0 : c.k0.Contains k0R)
    (hM : (dyadicCellM n rho z c).Contains
      (routeBCellA rhoR zR c.hq.lower ^ n))
    (hN : (dyadicCellN n rho z c).Contains (routeBCellN n rhoR zR tR))
    (hrhoLo : 0 < rho.lo) (htLo : 0 < c.t.lo) :
    (dyadicCellTrivial n rho z c).Contains
      (routeBCellTrivialBound n rhoR zR tR k0R c.hq.lower) := by
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hsn := dyadicCellSqrtN_sound n
  have hp := dyadicCellP_sound hrho hrhoLo
  have hsum := hM.add hN
  have hquot := hsum.div ht ht.ordered htLo
  have hresult := ((htwo.mul hsn).mul hp).mul (hk0.mul hquot)
  rw [dyadicCellTrivial, if_pos htLo]
  convert hresult using 1
  unfold routeBCellTrivialBound
  ring

theorem dyadicCellF3_sound_of_components
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    {rhoR zR tR kd2R : ℝ}
    (hrho : rho.Contains rhoR) (hkd2 : c.kd2.Contains kd2R)
    (hN : (dyadicCellN n rho z c).Contains (routeBCellN n rhoR zR tR))
    (hrhoLo : 0 < rho.lo) :
    (dyadicCellF3 n rho z c).Contains
      (routeBCellCorrectionBound n rhoR zR tR kd2R) := by
  have hsn := dyadicCellSqrtN_sound n
  have hp := dyadicCellP_sound hrho hrhoLo
  have hresult := (hsn.mul hp).mul (hkd2.mul hN)
  unfold dyadicCellF3 routeBCellCorrectionBound
  convert hresult using 1 <;> ring

theorem dyadicCellF2_sound_of_components
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    {rhoR zR tR kh2R : ℝ}
    (hrho : rho.Contains rhoR) (hkh2 : c.kh2.Contains kh2R)
    (hM : (dyadicCellM n rho z c).Contains
      (routeBCellA rhoR zR c.hq.lower ^ n))
    (hrhoLo : 0 < rho.lo) :
    (dyadicCellF2 n rho z c).Contains
      (routeBCellHighBound n rhoR zR tR kh2R c.hq.lower) := by
  have hsn := dyadicCellSqrtN_sound n
  have hp := dyadicCellP_sound hrho hrhoLo
  have hresult := (hsn.mul hp).mul (hkh2.mul hM)
  unfold dyadicCellF2 routeBCellHighBound
  convert hresult using 1 <;> ring

theorem routeBNormalizedHighIntegrand_le_dyadicCellF2_upper
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    {rhoR zR tR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (ht : c.t.Contains tR)
    (hrhoLo : 0 < rho.lo) (hrhoR : 0 < rhoR) (hz0 : 0 ≤ zR)
    (ht0 : 0 < tR) (ht1 : tR ≤ 1)
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hkh2 : c.kh2.Contains (prawitzKH2Envelope tR))
    (hW2Den : 0 < (dyadicCellW2 rho z).lo) :
    routeBNormalizedHighIntegrand n rhoR zR tR ≤
      (dyadicCellF2 n rho z c).upper := by
  have hw : 0 < routeBDboundW rhoR zR := by
    unfold routeBDboundW
    linarith
  have hM := dyadicCellM_sound (n := n) (c := c) hrho hz hW2Den
  have hF2 := dyadicCellF2_sound_of_components
    (n := n) (tR := tR) hrho hkh2 hM hrhoLo
  have hkernel : 2 * ‖prawitzKernel tR‖ ≤ prawitzKH2Envelope tR :=
    two_mul_norm_prawitzKernel_le_KH2Envelope ht0 ht1
  exact (routeBNormalizedHighIntegrand_le_cell
    hrhoR hw hhq hkernel).trans hF2.2

theorem routeBNormalizedCorrectionIntegrand_le_dyadicCellF3_upper
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    {rhoR zR tR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (ht : c.t.Contains tR)
    (hv : c.v.Contains (routeBCellV tR))
    (hrhoLo : 0 < rho.lo) (hrhoR : 0 < rhoR)
    (ht0 : 0 ≤ tR) (ht1 : tR < 1)
    (hkd2 : c.kd2.Contains (prawitzKD2Envelope tR))
    (hBDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (dyadicCellW2 rho z)).lo)
    (hNArgLo : 0 ≤ (dyadicCellNArg n rho z c).lo) :
    routeBNormalizedCorrectionIntegrand n rhoR zR tR ≤
      (dyadicCellF3 n rho z c).upper := by
  have hN := dyadicCellN_route_sound
    (n := n) hrho hz hv hBDen hNArgLo
  have hF3 := dyadicCellF3_sound_of_components
    (n := n) hrho hkd2 hN hrhoLo
  have hkernel : 2 * ‖prawitzKernelCorrection tR‖ ≤ prawitzKD2Envelope tR :=
    two_mul_norm_prawitzKernelCorrection_le_KD2Envelope ht0 ht1
  exact (routeBNormalizedCorrectionIntegrand_le_cell hrhoR hkernel).trans hF3.2

theorem routeBNormalizedLowerDifferenceIntegrand_le_dyadicCellF1_upper
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    {rhoR zR tR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) (ht : c.t.Contains tR)
    (hv : c.v.Contains (routeBCellV tR))
    (hrhoLo : 0 < rho.lo) (hrhoR : 0 < rhoR) (hz0 : 0 ≤ zR)
    (hz1 : zR ≤ rhoR) (ht0 : 0 ≤ tR) (ht1 : tR < 1)
    (hhq : c.hq.lower ≤ routeBCellV tR ^ 2 *
      routeBMinorant routeBKappa routeBTheta (routeBCellV tR))
    (hk0 : c.k0.Contains (prawitzK0Envelope tR))
    (hW2Den : 0 < (dyadicCellW2 rho z).lo)
    (hBDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (dyadicCellW2 rho z)).lo)
    (hBArgLo : 0 ≤ (dyadicCellBArg rho z c).lo)
    (hNArgLo : 0 ≤ (dyadicCellNArg n rho z c).lo)
    (hCDen : 0 < (DyadicInterval.mul (DyadicInterval.point 4)
      (dyadicCellW rho z)).lo)
    (hW3Den : 0 < (powi (dyadicCellW rho z) 3).lo)
    (hy3 : routeBDboundY rhoR zR (routeBCellV tR) ≤ 3)
    (hHuge : ¬ 0 < c.t.lo →
      (dyadicCellTelescoping n rho z c).hi ≤ dyadicCellHuge.hi) :
    routeBNormalizedLowerDifferenceIntegrand n rhoR zR tR ≤
      (dyadicCellF1 n rho z c).upper := by
  have hw : 0 < routeBDboundW rhoR zR := by
    unfold routeBDboundW
    linarith
  have hv0 : 0 ≤ routeBCellV tR := by
    unfold routeBCellV
    positivity
  have hM := dyadicCellM_sound (n := n) (c := c) hrho hz hW2Den
  have hN := dyadicCellN_route_sound
    (n := n) hrho hz hv hBDen hNArgLo
  have hH := dyadicCellH_sound
    (n := n) hrho hz hv hW2Den hBDen hBArgLo
  have hyDen : 0 < (DyadicInterval.mul (DyadicInterval.point 2)
      (DyadicInterval.sqr (dyadicCellW rho z))).lo := by
    simpa [dyadicCellW2] using hBDen
  have hD := dyadicCellD_sound hrho hz hv hrhoLo hyDen hCDen
    hrhoR hz0 hz1 hv0 hy3
  have hTel := dyadicCellTelescoping_sound_of_components
    (n := n) (rhoR := rhoR) (zR := zR) (tR := tR)
    (k0R := prawitzK0Envelope tR)
    (DR := routeBDiskBound routeBKappa rhoR (routeBDboundR rhoR zR)
      (routeBDboundFrequency rhoR zR (routeBCellV tR)))
    hrho hz ht hk0 hD hH hW3Den
  have hkernel : tR * ‖prawitzKernel tR‖ ≤ prawitzK0Envelope tR :=
    t_mul_norm_prawitzKernel_le_K0Envelope ht0 ht1
  have hTelUpper :
      routeBNormalizedLowerDifferenceIntegrand n rhoR zR tR ≤
        (dyadicCellTelescoping n rho z c).upper :=
    (routeBNormalizedLowerDifferenceIntegrand_le_telescoping
      hrhoR hw ht0 hhq hkernel le_rfl).trans hTel.2
  have hTrivialUpper :
      routeBNormalizedLowerDifferenceIntegrand n rhoR zR tR ≤
        (dyadicCellTrivial n rho z c).upper := by
    by_cases htLo : 0 < c.t.lo
    · have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
        exact_mod_cast dyadicScale_pos
      have hcLowerPos : 0 < c.t.lower := by
        unfold DyadicInterval.lower
        exact div_pos (by exact_mod_cast htLo) hscale
      have htRPos : 0 < tR := hcLowerPos.trans_le ht.1
      have hTrivial := dyadicCellTrivial_sound_of_components
        (n := n) (rhoR := rhoR) (zR := zR) (tR := tR)
        (k0R := prawitzK0Envelope tR)
        hrho ht hk0 hM hN hrhoLo htLo
      exact (routeBNormalizedLowerDifferenceIntegrand_le_trivial
        hrhoR hw htRPos hhq hkernel).trans hTrivial.2
    · rw [dyadicCellTrivial, if_neg htLo]
      have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
        exact_mod_cast dyadicScale_pos
      exact hTelUpper.trans
        (div_le_div_of_nonneg_right (by exact_mod_cast hHuge htLo) hscale.le)
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  change routeBNormalizedLowerDifferenceIntegrand n rhoR zR tR ≤
    ((min (dyadicCellTelescoping n rho z c).hi
      (dyadicCellTrivial n rho z c).hi : ℤ) : ℝ) / (dyadicScale : ℝ)
  rw [Int.cast_min, ← min_div_div_right hscale.le]
  exact le_min hTelUpper hTrivialUpper

theorem routeBNormalizedLowIntegrand_le_dyadicLowCellValue_upper
    {n : ℕ} {rho z : DyadicInterval} {c : DyadicPrawitzCell}
    {rhoR zR tR : ℝ}
    (hF1 : routeBNormalizedLowerDifferenceIntegrand n rhoR zR tR ≤
      (dyadicCellF1 n rho z c).upper)
    (hF3 : routeBNormalizedCorrectionIntegrand n rhoR zR tR ≤
      (dyadicCellF3 n rho z c).upper) :
    routeBNormalizedLowIntegrand n rhoR zR tR ≤
      (dyadicLowCellValue n rho z c).upper := by
  unfold routeBNormalizedLowIntegrand
  have hsum := add_le_add hF1 hF3
  simpa [dyadicLowCellValue, DyadicInterval.add, DyadicInterval.upper,
    Int.cast_add, add_div] using hsum

end

end BerryEsseen
