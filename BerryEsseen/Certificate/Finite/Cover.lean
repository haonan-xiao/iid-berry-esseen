import BerryEsseen.Certificate.Dyadic.GaussianTail
/-!
# Exhaustive dyadic cover for the finite-`n` Route B certificate

This module transcribes the finite-parameter traversal in the supplied exact checker.  A leaf
uses the complete Darboux-plus-`E1up` bound at `N = 256`, with the same conditional refinements
to `N = 1024` and `N = 2048`.  Rejected boxes are bisected along the checker-selected parameter
direction, to a maximum depth of thirty.

The recursive cover is a Boolean program.  Its soundness theorem proves that a successful cover
bounds every real parameter pair in the root box; concrete `native_decide` evaluations can
therefore serve as proof-producing numerical certificates rather than imported log files.
-/

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 10000

/-- The strict certificate threshold `0.4495`, represented exactly as in the checker. -/
def dyadicRouteBThreshold : DyadicInterval := DyadicInterval.ofRat 4495 10000

theorem dyadicRouteBThreshold_contains :
    dyadicRouteBThreshold.Contains ((4495 : ℝ) / 10000) := by
  exact DyadicInterval.contains_ofRat 4495 (b := 10000) (by norm_num)

/-- The first checker refinement, from `256` cells to `1024` cells. -/
def dyadicRouteBRefineTo1024 (q : DyadicInterval) : Prop :=
  dyadicRouteBThreshold.lo ≤ q.hi ∧ q.hi * 100 < 46 * dyadicScale

instance (q : DyadicInterval) : Decidable (dyadicRouteBRefineTo1024 q) := by
  unfold dyadicRouteBRefineTo1024
  infer_instance

/-- The second checker refinement, from the current result to `2048` cells. -/
def dyadicRouteBRefineTo2048 (q : DyadicInterval) : Prop :=
  dyadicRouteBThreshold.lo ≤ q.hi ∧ q.hi * 250 < 113 * dyadicScale

instance (q : DyadicInterval) : Decidable (dyadicRouteBRefineTo2048 q) := by
  unfold dyadicRouteBRefineTo2048
  infer_instance

/-- The exact adaptive `N = 256/1024/2048` evaluation from `finite_cover`. -/
def dyadicRouteBAdaptiveChoice
    (n : ℕ) (rho z : DyadicInterval) : ℕ × DyadicInterval :=
  let q256 := dyadicRouteBFullBound n rho z 256
  let first :=
    if dyadicRouteBRefineTo1024 q256 then
      (1024, dyadicRouteBFullBound n rho z 1024)
    else
      (256, q256)
  if dyadicRouteBRefineTo2048 first.2 then
    (2048, dyadicRouteBFullBound n rho z 2048)
  else
    first

theorem dyadicRouteBAdaptiveChoice_cells_pos
    (n : ℕ) (rho z : DyadicInterval) :
    0 < (dyadicRouteBAdaptiveChoice n rho z).1 := by
  simp only [dyadicRouteBAdaptiveChoice]
  split_ifs <;> norm_num

/-- A checker leaf is accepted only when every arithmetic side condition holds and the complete
upper endpoint is strictly below the lower endpoint of the `0.4495` interval. -/
structure DyadicRouteBFiniteBoxAccepted
    (n : ℕ) (rho z : DyadicInterval) : Prop where
  full : DyadicRouteBFullAdmissible n
    (dyadicRouteBAdaptiveChoice n rho z).1 rho z
  strict : (dyadicRouteBAdaptiveChoice n rho z).2.hi <
    dyadicRouteBThreshold.lo

instance (n : ℕ) (rho z : DyadicInterval) :
    Decidable (DyadicRouteBFiniteBoxAccepted n rho z) := by
  exact decidable_of_iff
    (DyadicRouteBFullAdmissible n
        (dyadicRouteBAdaptiveChoice n rho z).1 rho z ∧
      (dyadicRouteBAdaptiveChoice n rho z).2.hi < dyadicRouteBThreshold.lo) <| by
        constructor
        · rintro ⟨hfull, hstrict⟩
          exact ⟨hfull, hstrict⟩
        · intro h
          exact ⟨h.full, h.strict⟩

theorem dyadic_upper_lt_lower_of_hi_lt_lo
    {I J : DyadicInterval} (h : I.hi < J.lo) :
    I.upper < J.lower := by
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by
    exact_mod_cast dyadicScale_pos
  unfold DyadicInterval.upper DyadicInterval.lower
  exact (div_lt_div_iff_of_pos_right hscale).2 (by exact_mod_cast h)

theorem routeB_normalizedRouteBU_lt_threshold_of_finiteBoxAccepted
    {n : ℕ} (hn : 0 < n) {rho z : DyadicInterval} {rhoR zR : ℝ}
    (haccepted : DyadicRouteBFiniteBoxAccepted n rho z)
    (hrho : rho.Contains rhoR) (hz : z.Contains zR) :
    Real.sqrt (n : ℝ) / rhoR *
        routeBU routeBKappa routeBTheta n rhoR (routeBDboundR rhoR zR) <
      (4495 : ℝ) / 10000 := by
  have hN : 0 < (dyadicRouteBAdaptiveChoice n rho z).1 :=
    dyadicRouteBAdaptiveChoice_cells_pos n rho z
  have hfull := haccepted.full
  have hstrict := haccepted.strict
  rcases hfull with ⟨hbox, htail, hlow, hhigh⟩
  have hbound := routeB_normalizedRouteBU_le_dyadicRouteBFullBound_upper
    hn hN hrho hz hbox
      (fun i hi => hlow ⟨i, hi⟩)
      (fun i hi => hhigh ⟨i, hi⟩) htail
  have hchoice : (dyadicRouteBAdaptiveChoice n rho z).2 =
      dyadicRouteBFullBound n rho z (dyadicRouteBAdaptiveChoice n rho z).1 := by
    simp only [dyadicRouteBAdaptiveChoice]
    split_ifs <;> rfl
  rw [← hchoice] at hbound
  exact hbound.trans_lt <|
    (dyadic_upper_lt_lower_of_hi_lt_lo hstrict).trans_le
      dyadicRouteBThreshold_contains.1

/-- Integer midpoint used by the checker. -/
def dyadicRouteBMidpoint (I : DyadicInterval) : ℤ :=
  floorDiv (I.lo + I.hi) 2

def dyadicRouteBLeftHalf (I : DyadicInterval) : DyadicInterval :=
  ⟨I.lo, dyadicRouteBMidpoint I⟩

def dyadicRouteBRightHalf (I : DyadicInterval) : DyadicInterval :=
  ⟨dyadicRouteBMidpoint I, I.hi⟩

theorem dyadicRouteB_contains_left_or_right
    {I : DyadicInterval} {x : ℝ} (hx : I.Contains x) :
    (dyadicRouteBLeftHalf I).Contains x ∨
      (dyadicRouteBRightHalf I).Contains x := by
  by_cases hm : x ≤ (dyadicRouteBMidpoint I : ℝ) / (dyadicScale : ℝ)
  · left
    exact ⟨hx.1, hm⟩
  · right
    exact ⟨le_of_not_ge hm, hx.2⟩

/-- The checker's upper endpoint for `(56/45) * sqrt(n)`. -/
def dyadicRouteBFiniteRootRadius (n : ℕ) : DyadicInterval :=
  DyadicInterval.mul (DyadicInterval.ofRat 56 45) (dyadicCellSqrtN n)

def dyadicRouteBIntervalFromOne (I : DyadicInterval) : DyadicInterval :=
  ⟨dyadicScale, I.hi⟩

def dyadicRouteBFiniteRootRho (n : ℕ) : DyadicInterval :=
  dyadicRouteBIntervalFromOne (dyadicRouteBFiniteRootRadius n)

def dyadicRouteBFiniteRootZ : DyadicInterval :=
  ⟨0, dyadicScale⟩

theorem dyadicRouteBFiniteRootRadius_contains (n : ℕ) :
    (dyadicRouteBFiniteRootRadius n).Contains
      (((56 : ℝ) / 45) * Real.sqrt (n : ℝ)) := by
  exact (DyadicInterval.contains_ofRat 56 (b := 45) (by norm_num)).mul
    (dyadicCellSqrtN_sound n)

theorem dyadicRouteBIntervalFromOne_contains
    {I : DyadicInterval} {x y : ℝ} (hI : I.Contains y)
    (hlower : 1 ≤ x) (hupper : x ≤ y) :
    (dyadicRouteBIntervalFromOne I).Contains x := by
  have hscaleNe : (dyadicScale : ℝ) ≠ 0 := by
    exact_mod_cast dyadicScale_pos.ne'
  constructor
  · change (dyadicScale : ℝ) / (dyadicScale : ℝ) ≤ x
    rw [div_self hscaleNe]
    exact hlower
  · exact hupper.trans hI.2

theorem dyadicRouteBFiniteRootRho_contains
    {n : ℕ} {rho : ℝ} (hlower : 1 ≤ rho)
    (hupper : rho ≤ ((56 : ℝ) / 45) * Real.sqrt (n : ℝ)) :
    (dyadicRouteBFiniteRootRho n).Contains rho := by
  exact dyadicRouteBIntervalFromOne_contains
    (dyadicRouteBFiniteRootRadius_contains n) hlower hupper

theorem dyadicRouteBFiniteRootZ_contains
    {z : ℝ} (hlower : 0 ≤ z) (hupper : z ≤ 1) :
    dyadicRouteBFiniteRootZ.Contains z := by
  have hscaleNe : (dyadicScale : ℝ) ≠ 0 := by
    exact_mod_cast dyadicScale_pos.ne'
  have hrootLower : dyadicRouteBFiniteRootZ.lower = 0 := by
    simp only [DyadicInterval.lower, dyadicRouteBFiniteRootZ,
      Int.cast_zero, zero_div]
  have hrootUpper : dyadicRouteBFiniteRootZ.upper = 1 := by
    unfold DyadicInterval.upper dyadicRouteBFiniteRootZ
    exact div_self hscaleNe
  unfold DyadicInterval.Contains
  rw [hrootLower, hrootUpper]
  exact ⟨hlower, hupper⟩

/-- Exact integer version of the checker's relative-width split decision. -/
def dyadicRouteBSplitRho
    (n : ℕ) (rho z : DyadicInterval) : Prop :=
  (rho.hi - rho.lo) * dyadicScale >
    (z.hi - z.lo) * ((dyadicRouteBFiniteRootRadius n).hi - dyadicScale)

instance (n : ℕ) (rho z : DyadicInterval) :
    Decidable (dyadicRouteBSplitRho n rho z) := by
  unfold dyadicRouteBSplitRho
  infer_instance

/-- Depth-bounded Boolean cover.  An accepted node stops immediately; otherwise both children
must succeed.  Fuel `30` reproduces the checker's maximum accepted depth. -/
def dyadicRouteBFiniteCover
    (n : ℕ) : ℕ → DyadicInterval → DyadicInterval → Bool
  | 0, rho, z => decide (DyadicRouteBFiniteBoxAccepted n rho z)
  | fuel + 1, rho, z =>
      if DyadicRouteBFiniteBoxAccepted n rho z then
        true
      else if dyadicRouteBSplitRho n rho z then
        dyadicRouteBFiniteCover n fuel (dyadicRouteBLeftHalf rho) z &&
          dyadicRouteBFiniteCover n fuel (dyadicRouteBRightHalf rho) z
      else
        dyadicRouteBFiniteCover n fuel rho (dyadicRouteBLeftHalf z) &&
          dyadicRouteBFiniteCover n fuel rho (dyadicRouteBRightHalf z)

theorem dyadicRouteBFiniteCover_sound
    {n : ℕ} (hn : 0 < n) {fuel : ℕ} {rho z : DyadicInterval}
    (hcover : dyadicRouteBFiniteCover n fuel rho z = true)
    {rhoR zR : ℝ} (hrho : rho.Contains rhoR) (hz : z.Contains zR) :
    Real.sqrt (n : ℝ) / rhoR *
        routeBU routeBKappa routeBTheta n rhoR (routeBDboundR rhoR zR) <
      (4495 : ℝ) / 10000 := by
  induction fuel generalizing rho z with
  | zero =>
      have haccepted : DyadicRouteBFiniteBoxAccepted n rho z := by
        exact of_decide_eq_true hcover
      exact routeB_normalizedRouteBU_lt_threshold_of_finiteBoxAccepted
        hn haccepted hrho hz
  | succ fuel ih =>
      by_cases haccepted : DyadicRouteBFiniteBoxAccepted n rho z
      · exact routeB_normalizedRouteBU_lt_threshold_of_finiteBoxAccepted
          hn haccepted hrho hz
      · by_cases hsplit : dyadicRouteBSplitRho n rho z
        · have hchildren :
            dyadicRouteBFiniteCover n fuel (dyadicRouteBLeftHalf rho) z = true ∧
              dyadicRouteBFiniteCover n fuel (dyadicRouteBRightHalf rho) z = true := by
            simpa [dyadicRouteBFiniteCover, haccepted, hsplit,
              Bool.and_eq_true] using hcover
          rcases dyadicRouteB_contains_left_or_right hrho with hleft | hright
          · exact ih hchildren.1 hleft hz
          · exact ih hchildren.2 hright hz
        · have hchildren :
            dyadicRouteBFiniteCover n fuel rho (dyadicRouteBLeftHalf z) = true ∧
              dyadicRouteBFiniteCover n fuel rho (dyadicRouteBRightHalf z) = true := by
            simpa [dyadicRouteBFiniteCover, haccepted, hsplit,
              Bool.and_eq_true] using hcover
          rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
          · exact ih hchildren.1 hrho hleft
          · exact ih hchildren.2 hrho hright

def dyadicRouteBFiniteCertificate (n : ℕ) : Bool :=
  dyadicRouteBFiniteCover n 30
    (dyadicRouteBFiniteRootRho n) dyadicRouteBFiniteRootZ

theorem routeB_normalizedRouteBU_lt_threshold_of_finiteCertificate
    {n : ℕ} (hn : 0 < n) (hcertificate : dyadicRouteBFiniteCertificate n = true)
    {rho z : ℝ} (hrhoLower : 1 ≤ rho)
    (hrhoUpper : rho ≤ ((56 : ℝ) / 45) * Real.sqrt (n : ℝ))
    (hzLower : 0 ≤ z) (hzUpper : z ≤ 1) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho z) <
      (4495 : ℝ) / 10000 := by
  exact dyadicRouteBFiniteCover_sound hn hcertificate
    (dyadicRouteBFiniteRootRho_contains hrhoLower hrhoUpper)
    (dyadicRouteBFiniteRootZ_contains hzLower hzUpper)

end BerryEsseen
