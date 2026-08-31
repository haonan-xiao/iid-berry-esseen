import BerryEsseen.Certificate.LargeN.Integral
import BerryEsseen.Certificate.Dyadic.GaussianTail
/-!
# Direct large-`n` Gaussian tail and full bound

This module transcribes the final `E1up` term of `tail_direct`, proves its
relation to the normalized Gaussian tail in `routeBU`, and combines it with
the two direct Darboux sums.
-/

open MeasureTheory intervalIntegral

namespace BerryEsseen

open DyadicInterval

noncomputable def routeBLargeTailArgument (L r : ℝ) : ℝ :=
  2 * Real.pi ^ 2 * prawitzSplit ^ 2 / (r ^ 2 * L ^ 2)

noncomputable def routeBLargeTailValue (L r : ℝ) : ℝ :=
  routeBE1 (routeBLargeTailArgument L r) / (2 * Real.pi * L)

def dyadicRouteBLargeTailX
    (L r : DyadicInterval) : DyadicInterval :=
  DyadicInterval.div
    (DyadicInterval.mul (DyadicInterval.point 2)
      (DyadicInterval.mul (DyadicInterval.sqr checkerPi)
        (DyadicInterval.sqr dyadicRouteBSplit)))
    (dyadicLargeDen L r)

def dyadicRouteBLargeTailDen (L : DyadicInterval) : DyadicInterval :=
  DyadicInterval.mul dyadicRouteBTwoPi L

def dyadicRouteBLargeTailValue
    (L r : DyadicInterval) : DyadicInterval :=
  DyadicInterval.div (dyadicE1Up (dyadicRouteBLargeTailX L r))
    (dyadicRouteBLargeTailDen L)

def dyadicRouteBLargeFullBound
    (L r : DyadicInterval) (N : ℕ) : DyadicInterval :=
  DyadicInterval.add (dyadicRouteBLargeFiniteBound L r N)
    (dyadicRouteBLargeTailValue L r)

structure DyadicLargeTailAdmissible
    (L r : DyadicInterval) : Prop where
  xPos : 0 < (dyadicRouteBLargeTailX L r).lo
  tailDenPos : 0 < (dyadicRouteBLargeTailDen L).lo

instance (L r : DyadicInterval) :
    Decidable (DyadicLargeTailAdmissible L r) :=
  decidable_of_iff
    (0 < (dyadicRouteBLargeTailX L r).lo ∧
      0 < (dyadicRouteBLargeTailDen L).lo) <| by
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2⟩
        · intro h
          exact ⟨h.xPos, h.tailDenPos⟩

/-- All exact-integer side conditions needed by the direct large-`n`
single-box theorem. -/
def DyadicRouteBLargeFullAdmissible
    (L r : DyadicInterval) (N : ℕ) : Prop :=
  DyadicLargeBoxAdmissible L r ∧
    DyadicLargeTailAdmissible L r ∧
    (∀ i : Fin N,
      DyadicLargeLowCellAdmissible L r (dyadicRouteBLowCell N i.1)) ∧
    (∀ i : Fin N,
      DyadicLargeHighCellAdmissible L r (dyadicRouteBHighCell N i.1))

instance (L r : DyadicInterval) (N : ℕ) :
    Decidable (DyadicRouteBLargeFullAdmissible L r N) := by
  unfold DyadicRouteBLargeFullAdmissible
  infer_instance

noncomputable section

theorem routeBLargeTailArgument_eq
    {n : ℕ} (hn : 0 < n) {rho z : ℝ} (hrho : 0 < rho) :
    routeBLargeTailArgument (routeBSmoothingScale n rho)
        (routeBDboundR rho z) =
      routeBTailArgument n rho z := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  unfold routeBLargeTailArgument routeBTailArgument routeBTailCoefficient
    routeBSmoothingScale routeBDboundR routeBDboundW
  field_simp [hrho.ne', hsqrt.ne']
  rw [Real.sq_sqrt hnR.le]

theorem routeBNormalizedE1Tail_eq_largeTailValue
    {n : ℕ} (hn : 0 < n) {rho z : ℝ} (hrho : 0 < rho) :
    Real.sqrt (n : ℝ) / rho *
        (routeBE1 (routeBTailArgument n rho z) / (2 * Real.pi)) =
      routeBLargeTailValue (routeBSmoothingScale n rho)
        (routeBDboundR rho z) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  rw [← routeBLargeTailArgument_eq hn hrho]
  unfold routeBLargeTailValue routeBSmoothingScale
  field_simp [hrho.ne', hsqrt.ne', Real.pi_ne_zero]

theorem dyadicRouteBLargeTailX_sound
    {L r : DyadicInterval} {LR rR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR)
    (hbox : DyadicLargeBoxAdmissible L r) :
    (dyadicRouteBLargeTailX L r).Contains
      (routeBLargeTailArgument LR rR) := by
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  have hpi2 := checkerPi_contains_pi.sqr checkerPi_contains_pi.ordered
  have hsplit2 := dyadicRouteBSplit_contains.sqr dyadicRouteBSplit_contains.ordered
  have hnum := htwo.mul (hpi2.mul hsplit2)
  have hden := dyadicLargeDen_sound hL hr
  have hquot := hnum.div hden hden.ordered hbox.denPos
  unfold dyadicRouteBLargeTailX routeBLargeTailArgument
  convert hquot using 1 <;> ring

theorem dyadicRouteBLargeTailDen_sound
    {L : DyadicInterval} {LR : ℝ} (hL : L.Contains LR) :
    (dyadicRouteBLargeTailDen L).Contains (2 * Real.pi * LR) := by
  simpa [dyadicRouteBLargeTailDen] using dyadicRouteBTwoPi_contains.mul hL

theorem routeBLargeTailValue_le_dyadic_upper
    {L r : DyadicInterval} {LR rR : ℝ}
    (hL : L.Contains LR) (hr : r.Contains rR)
    (hbox : DyadicLargeBoxAdmissible L r)
    (htail : DyadicLargeTailAdmissible L r) :
    routeBLargeTailValue LR rR ≤
      (dyadicRouteBLargeTailValue L r).upper := by
  have hLR := hbox.real_L_pos hL
  have hx := dyadicRouteBLargeTailX_sound hL hr hbox
  have he1 := routeBE1_le_dyadicE1Up_upper hx htail.xPos
  have he1Ordered : (dyadicE1Up (dyadicRouteBLargeTailX L r)).Ordered :=
    (dyadicE1Up_sound htail.xPos).ordered
  have he1Upper := DyadicInterval.contains_upper he1Ordered
  have hden := dyadicRouteBLargeTailDen_sound hL
  have hquot := he1Upper.div hden hden.ordered htail.tailDenPos
  have hcontains : (dyadicRouteBLargeTailValue L r).Contains
      ((dyadicE1Up (dyadicRouteBLargeTailX L r)).upper /
        (2 * Real.pi * LR)) := by
    simpa [dyadicRouteBLargeTailValue] using hquot
  have hdenPos : 0 < 2 * Real.pi * LR := by positivity
  have hscaled := (div_le_div_iff_of_pos_right hdenPos).2 he1
  exact hscaled.trans hcontains.2

theorem routeBNormalizedE1Tail_le_dyadicLargeTailValue_upper
    {n : ℕ} (hn : 0 < n) {rho z : ℝ}
    {L r : DyadicInterval}
    (hrho : 0 < rho)
    (hL : L.Contains (routeBSmoothingScale n rho))
    (hr : r.Contains (routeBDboundR rho z))
    (hbox : DyadicLargeBoxAdmissible L r)
    (htail : DyadicLargeTailAdmissible L r) :
    Real.sqrt (n : ℝ) / rho *
        (routeBE1 (routeBTailArgument n rho z) / (2 * Real.pi)) ≤
      (dyadicRouteBLargeTailValue L r).upper := by
  rw [routeBNormalizedE1Tail_eq_largeTailValue hn hrho]
  exact routeBLargeTailValue_le_dyadic_upper hL hr hbox htail

theorem routeB_normalizedRouteBU_le_dyadicRouteBLargeFullBound_upper
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {rho z : ℝ} {L r : DyadicInterval}
    (hrho1 : 1 ≤ rho) (hz0 : 0 ≤ z)
    (hL : L.Contains (routeBSmoothingScale n rho))
    (hr : r.Contains (routeBDboundR rho z))
    (hbox : DyadicLargeBoxAdmissible L r)
    (hlow : ∀ i < N,
      DyadicLargeLowCellAdmissible L r (dyadicRouteBLowCell N i))
    (hhigh : ∀ i < N,
      DyadicLargeHighCellAdmissible L r (dyadicRouteBHighCell N i))
    (htail : DyadicLargeTailAdmissible L r) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho z) ≤
      (dyadicRouteBLargeFullBound L r N).upper := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hrhoPos : 0 < rho := zero_lt_one.trans_le hrho1
  rw [routeB_normalizedRouteBU_eq_finiteIntegrals_add_tail hnPos hrhoPos hz0,
    routeB_normalizedGaussianTail_eq hnPos hrhoPos hz0]
  have hfinite :=
    routeBNormalizedFiniteIntegrals_le_dyadicRouteBLargeFiniteBound_upper
      hn hN hrho1 hz0 hL hr hbox hlow hhigh
  have htailBound := routeBNormalizedE1Tail_le_dyadicLargeTailValue_upper
    hnPos hrhoPos hL hr hbox htail
  have hsum := add_le_add hfinite htailBound
  simpa [dyadicRouteBLargeFullBound, DyadicInterval.add, DyadicInterval.upper,
    Int.cast_add, add_div] using hsum

/-- Convenience form used by executable certificates: all arithmetic side
conditions arrive as one decidable proposition. -/
theorem routeB_normalizedRouteBU_le_dyadicRouteBLargeFullBound_upper_of_admissible
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {rho z : ℝ} {L r : DyadicInterval}
    (hrho1 : 1 ≤ rho) (hz0 : 0 ≤ z)
    (hL : L.Contains (routeBSmoothingScale n rho))
    (hr : r.Contains (routeBDboundR rho z))
    (hfull : DyadicRouteBLargeFullAdmissible L r N) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho z) ≤
      (dyadicRouteBLargeFullBound L r N).upper := by
  rcases hfull with ⟨hbox, htail, hlow, hhigh⟩
  exact routeB_normalizedRouteBU_le_dyadicRouteBLargeFullBound_upper
    hn hN hrho1 hz0 hL hr hbox
      (fun i hi => hlow ⟨i, hi⟩)
      (fun i hi => hhigh ⟨i, hi⟩) htail

end

end BerryEsseen
