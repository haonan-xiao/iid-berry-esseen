import BerryEsseen.Smoothing.PrawitzGaussianTail
import BerryEsseen.Certificate.Dyadic.E1
import BerryEsseen.Certificate.Finite.Integral
/-!
# Exact dyadic certificate for the Route B Gaussian tail

This module transcribes the fourth term of the checker's `finite_bound` routine.  Its argument,
call to `E1up`, normalization by `sqrt n / rho`, and division by `2 * pi` are all evaluated by
the same precision-48 dyadic operations as the supplied checker.
-/

open MeasureTheory intervalIntegral

namespace BerryEsseen

open DyadicInterval

def dyadicRouteBTailX
    (n : ℕ) (rho z : DyadicInterval) : DyadicInterval :=
  DyadicInterval.div
    (DyadicInterval.mul
      (DyadicInterval.mul
        (DyadicInterval.point (Int.ofNat (2 * n)))
        (DyadicInterval.sqr checkerPi))
      (DyadicInterval.sqr dyadicRouteBSplit))
    (dyadicCellW2 rho z)

def dyadicRouteBTwoPi : DyadicInterval :=
  DyadicInterval.mul (DyadicInterval.point 2) checkerPi

def dyadicRouteBTailValue
    (n : ℕ) (rho z : DyadicInterval) : DyadicInterval :=
  DyadicInterval.mul
    (DyadicInterval.mul (dyadicCellSqrtN n) (dyadicCellP rho))
    (DyadicInterval.div (dyadicE1Up (dyadicRouteBTailX n rho z))
      dyadicRouteBTwoPi)

/-- Exact checker accumulator: the two finite Darboux loops plus the `E1up` tail. -/
def dyadicRouteBFullBound
    (n : ℕ) (rho z : DyadicInterval) (N : ℕ) : DyadicInterval :=
  DyadicInterval.add (dyadicRouteBFiniteBound n rho z N)
    (dyadicRouteBTailValue n rho z)

structure DyadicRouteBTailAdmissible
    (n : ℕ) (rho z : DyadicInterval) : Prop where
  w2Den : 0 < (dyadicCellW2 rho z).lo
  xPos : 0 < (dyadicRouteBTailX n rho z).lo

instance (n : ℕ) (rho z : DyadicInterval) :
    Decidable (DyadicRouteBTailAdmissible n rho z) :=
  decidable_of_iff
    (0 < (dyadicCellW2 rho z).lo ∧
      0 < (dyadicRouteBTailX n rho z).lo) <| by
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2⟩
        · intro h
          exact ⟨h.w2Den, h.xPos⟩

/-- All integer side conditions needed to apply the complete single-box theorem. -/
def DyadicRouteBFullAdmissible
    (n N : ℕ) (rho z : DyadicInterval) : Prop :=
  DyadicRouteBBoxAdmissible rho z ∧
    DyadicRouteBTailAdmissible n rho z ∧
    (∀ i : Fin N,
      DyadicLowCellAdmissible n rho z (dyadicRouteBLowCell N i.1)) ∧
    (∀ i : Fin N,
      DyadicHighCellAdmissible n rho z (dyadicRouteBHighCell N i.1))

instance (n N : ℕ) (rho z : DyadicInterval) :
    Decidable (DyadicRouteBFullAdmissible n N rho z) := by
  unfold DyadicRouteBFullAdmissible
  infer_instance

noncomputable section

theorem dyadicRouteBTwoPi_contains :
    dyadicRouteBTwoPi.Contains (2 * Real.pi) := by
  have htwo : (DyadicInterval.point 2).Contains (2 : ℝ) := by
    simpa using DyadicInterval.contains_point (2 : ℤ)
  simpa [dyadicRouteBTwoPi] using htwo.mul checkerPi_contains_pi

theorem dyadicRouteBTwoPi_lo_pos : 0 < dyadicRouteBTwoPi.lo := by
  norm_num [dyadicRouteBTwoPi, DyadicInterval.mul, DyadicInterval.point,
    checkerPi, cornerMinInt, floorDiv, dyadicScale, dyadicPrecision]

theorem dyadicRouteBTailX_sound
    {n : ℕ} {rho z : DyadicInterval} {rhoR zR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hadm : DyadicRouteBTailAdmissible n rho z) :
    (dyadicRouteBTailX n rho z).Contains (routeBTailArgument n rhoR zR) := by
  have hn : (DyadicInterval.point (Int.ofNat (2 * n))).Contains (2 * (n : ℝ)) := by
    convert DyadicInterval.contains_point (Int.ofNat (2 * n)) using 1
    norm_num
  have hpi2 := checkerPi_contains_pi.sqr checkerPi_contains_pi.ordered
  have hsplit2 := dyadicRouteBSplit_contains.sqr dyadicRouteBSplit_contains.ordered
  have hnum := (hn.mul hpi2).mul hsplit2
  have hw2 := dyadicCellW2_sound hrho hz
  have hquot := hnum.div hw2 hw2.ordered hadm.w2Den
  have hscale : (0 : ℝ) < (dyadicScale : ℝ) := by exact_mod_cast dyadicScale_pos
  have hw2Pos : 0 < routeBDboundW rhoR zR ^ 2 :=
    (div_pos (by exact_mod_cast hadm.w2Den) hscale).trans_le hw2.1
  have hwNe : routeBDboundW rhoR zR ≠ 0 := by
    intro hwZero
    rw [hwZero, zero_pow (by norm_num : 2 ≠ 0)] at hw2Pos
    exact lt_irrefl 0 hw2Pos
  change (dyadicRouteBTailX n rho z).Contains _
  rw [show routeBTailArgument n rhoR zR =
      2 * (n : ℝ) * Real.pi ^ 2 * prawitzSplit ^ 2 /
        routeBDboundW rhoR zR ^ 2 by
    unfold routeBTailArgument routeBTailCoefficient
    field_simp [hwNe]]
  simpa only [dyadicRouteBTailX] using hquot

theorem routeB_normalizedE1Tail_le_dyadicRouteBTailValue_upper
    {n : ℕ} (hn : 0 < n)
    {rho z : DyadicInterval} {rhoR zR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (htail : DyadicRouteBTailAdmissible n rho z) :
    Real.sqrt (n : ℝ) / rhoR *
        (routeBE1 (routeBTailArgument n rhoR zR) / (2 * Real.pi)) ≤
      (dyadicRouteBTailValue n rho z).upper := by
  have hrhoR := hbox.real_rho_pos hrho
  have hx := dyadicRouteBTailX_sound hrho hz htail
  have he1 := routeBE1_le_dyadicE1Up_upper hx htail.xPos
  have he1Ordered : (dyadicE1Up (dyadicRouteBTailX n rho z)).Ordered :=
    (dyadicE1Up_sound htail.xPos).ordered
  have he1Upper := DyadicInterval.contains_upper he1Ordered
  have htwoPi := dyadicRouteBTwoPi_contains
  have hquot := he1Upper.div htwoPi htwoPi.ordered dyadicRouteBTwoPi_lo_pos
  have hsn := dyadicCellSqrtN_sound n
  have hp := dyadicCellP_sound hrho hbox.rhoPos
  have hcontains : (dyadicRouteBTailValue n rho z).Contains
      (Real.sqrt (n : ℝ) / rhoR *
        ((dyadicE1Up (dyadicRouteBTailX n rho z)).upper / (2 * Real.pi))) := by
    simpa [dyadicRouteBTailValue, routeBDboundP, div_eq_mul_inv,
      mul_assoc] using (hsn.mul hp).mul hquot
  have hden : 0 < 2 * Real.pi := by positivity
  have hfactor : 0 ≤ Real.sqrt (n : ℝ) / rhoR := by positivity
  have hscaled := mul_le_mul_of_nonneg_left
    ((div_le_div_iff_of_pos_right hden).2 he1) hfactor
  exact hscaled.trans hcontains.2

theorem routeB_normalizedGaussianTail_le_dyadicRouteBTailValue_upper
    {n : ℕ} (hn : 0 < n)
    {rho z : DyadicInterval} {rhoR zR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (htail : DyadicRouteBTailAdmissible n rho z) :
    Real.sqrt (n : ℝ) / rhoR *
        ((1 / Real.pi) * ∫ t in Set.Ici prawitzSplit,
          routeBPowerGaussianEnvelope n rhoR (routeBDboundR rhoR zR) t / t) ≤
      (dyadicRouteBTailValue n rho z).upper := by
  rw [routeB_normalizedGaussianTail_eq hn
    (hbox.real_rho_pos hrho) (hbox.real_z_nonnegative hz)]
  exact routeB_normalizedE1Tail_le_dyadicRouteBTailValue_upper
    hn hrho hz hbox htail

theorem routeB_normalizedRouteBU_eq_finiteIntegrals_add_tail
    {n : ℕ} (hn : 0 < n) {rho z : ℝ} (hrho : 0 < rho) (hz : 0 ≤ z) :
    Real.sqrt (n : ℝ) / rho *
        routeBU routeBKappa routeBTheta n rho (routeBDboundR rho z) =
      ((∫ t in (0 : ℝ)..prawitzSplit,
          routeBNormalizedLowIntegrand n rho z t) +
        ∫ t in prawitzSplit..(1 : ℝ),
          routeBNormalizedHighIntegrand n rho z t) +
      Real.sqrt (n : ℝ) / rho *
        ((1 / Real.pi) * ∫ t in Set.Ici prawitzSplit,
          routeBPowerGaussianEnvelope n rho (routeBDboundR rho z) t / t) := by
  have hlower := intervalIntegrable_routeBNormalizedLowerDifferenceIntegrand n hrho hz
  have hcorr := intervalIntegrable_routeBNormalizedCorrectionIntegrand hn hrho hz
  have hlowEq :
      (∫ t in (0 : ℝ)..prawitzSplit,
          routeBNormalizedLowIntegrand n rho z t) =
        (2 * Real.sqrt (n : ℝ) / rho) *
            (∫ t in (0 : ℝ)..prawitzSplit,
              ‖prawitzKernel t‖ *
                routeBPowerDifferenceEnvelope routeBKappa routeBTheta n rho
                  (routeBDboundR rho z) t) +
          (2 * Real.sqrt (n : ℝ) / rho) *
            (∫ t in (0 : ℝ)..prawitzSplit,
              ‖prawitzKernelCorrection t‖ *
                routeBPowerGaussianEnvelope n rho (routeBDboundR rho z) t) := by
    unfold routeBNormalizedLowIntegrand
    rw [intervalIntegral.integral_add hlower hcorr]
    unfold routeBNormalizedLowerDifferenceIntegrand
      routeBNormalizedCorrectionIntegrand
    simp only [mul_assoc]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hhighEq :
      (∫ t in prawitzSplit..(1 : ℝ),
          routeBNormalizedHighIntegrand n rho z t) =
        (2 * Real.sqrt (n : ℝ) / rho) *
          (∫ t in prawitzSplit..(1 : ℝ),
            ‖prawitzKernel t‖ *
              routeBPowerModulusEnvelope routeBKappa routeBTheta n rho
                (routeBDboundR rho z) t) := by
    unfold routeBNormalizedHighIntegrand
    simp only [mul_assoc]
    rw [intervalIntegral.integral_const_mul]
  rw [hlowEq, hhighEq]
  unfold routeBU
  ring

/-- A single admissible checker box bounds the complete normalized `routeBU`, including its
improper Gaussian tail. -/
theorem routeB_normalizedRouteBU_le_dyadicRouteBFullBound_upper
    {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    {rho z : DyadicInterval} {rhoR zR : ℝ}
    (hrho : rho.Contains rhoR) (hz : z.Contains zR)
    (hbox : DyadicRouteBBoxAdmissible rho z)
    (hlow : ∀ i < N,
      DyadicLowCellAdmissible n rho z (dyadicRouteBLowCell N i))
    (hhigh : ∀ i < N,
      DyadicHighCellAdmissible n rho z (dyadicRouteBHighCell N i))
    (htail : DyadicRouteBTailAdmissible n rho z) :
    Real.sqrt (n : ℝ) / rhoR *
        routeBU routeBKappa routeBTheta n rhoR (routeBDboundR rhoR zR) ≤
      (dyadicRouteBFullBound n rho z N).upper := by
  have hrhoR := hbox.real_rho_pos hrho
  have hzR := hbox.real_z_nonnegative hz
  rw [routeB_normalizedRouteBU_eq_finiteIntegrals_add_tail hn hrhoR hzR]
  have hfinite := routeBNormalizedFiniteIntegrals_le_dyadicRouteBFiniteBound_upper
    hn hN hrho hz hbox hlow hhigh
  have htailBound := routeB_normalizedGaussianTail_le_dyadicRouteBTailValue_upper
    hn hrho hz hbox htail
  have hsum := add_le_add hfinite htailBound
  simpa [dyadicRouteBFullBound, DyadicInterval.add, DyadicInterval.upper,
    Int.cast_add, add_div] using hsum

end

end BerryEsseen
