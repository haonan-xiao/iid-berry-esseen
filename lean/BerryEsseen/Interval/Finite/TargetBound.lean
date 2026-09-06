import BerryEsseen.Interval.Finite.Cache

/-!
# Interval / Finite / Target Bound
-/

namespace BerryEsseen

open DyadicInterval MeasureTheory ProbabilityTheory

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def bound4395FiniteThreshold : DyadicInterval :=
  DyadicInterval.ofRat 879 2000

theorem bound4395FiniteThreshold_contains :
    bound4395FiniteThreshold.Contains ((879 : ℝ) / 2000) := by
  simpa [bound4395FiniteThreshold] using
    DyadicInterval.contains_ofRat 879 (b := 2000) (by norm_num)

def bound4395FiniteRatHull
    (alo blo ahi bhi : ℤ) : DyadicInterval :=
  ⟨(DyadicInterval.ofRat alo blo).lo,
    (DyadicInterval.ofRat ahi bhi).hi⟩

/-- Closed representative box around the discovered `n=4` bottleneck. -/
def bound4395FiniteRho : DyadicInterval :=
  bound4395FiniteRatHull 10370 10000 10372 10000

def bound4395FiniteZ : DyadicInterval :=
  bound4395FiniteRatHull 9641 10000 9644 10000

def bound4395FiniteTail : DyadicInterval :=
  dyadicRouteBCachedTailValue dyadicRouteBBuildResolutionCache.e1 4
    bound4395FiniteRho bound4395FiniteZ

def bound4395FiniteBound : DyadicInterval :=
  certifiedCachedFullBoundUsingTail
    dyadicRouteBBuildResolutionCache.cells1024 4
      bound4395FiniteRho bound4395FiniteZ bound4395FiniteTail

def bound4395FiniteAccepted : Bool :=
  decide (bound4395FiniteBound.hi < bound4395FiniteThreshold.lo) &&
    decide (CertifiedCachedFullAdmissible
      dyadicRouteBBuildResolutionCache.cells1024 4
        bound4395FiniteRho bound4395FiniteZ)

theorem bound4395FiniteAccepted_true_iff :
    bound4395FiniteAccepted = true ↔
      bound4395FiniteBound.hi < bound4395FiniteThreshold.lo ∧
        CertifiedCachedFullAdmissible
          dyadicRouteBBuildResolutionCache.cells1024 4
            bound4395FiniteRho bound4395FiniteZ := by
  simp [bound4395FiniteAccepted, Bool.and_eq_true]

/-- A successful exact Boolean has the intended normalized-distance meaning
for every admissible law point in the complete representative closed box. -/
theorem normalizedKolmogorovDistance_lt_879_2000_of_post044FiniteAccepted
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    (hrho : bound4395FiniteRho.Contains
      (thirdAbsoluteMoment (P.map (X 0))))
    (hz : bound4395FiniteZ.Contains
      (thirdAbsoluteMoment (P.map (X 0)) *
        (symmetrizationRatio (P.map (X 0)) - 1)))
    (haccepted : bound4395FiniteAccepted = true) :
    Real.sqrt (4 : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X 4) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  have hprop := bound4395FiniteAccepted_true_iff.mp haccepted
  have hvalid := dyadicRouteBBuildResolutionCache_valid
  have hcanonical := hprop.2.toCanonical hvalid.cells1024
  rcases hcanonical with ⟨hbox, htail, hlow, hhigh⟩
  have hbound := normalizedKolmogorovDistance_le_certifiedFullBound
    P X hindep hident hX hmean hsecond
      (n := 4) (N := 1024) (by norm_num) (by norm_num)
        hrho hz hbox hlow hhigh htail
  have hboundEq :
      bound4395FiniteBound =
        certifiedFullBound 4 bound4395FiniteRho
          bound4395FiniteZ 1024 := by
    simpa [bound4395FiniteBound, bound4395FiniteTail] using
      (certifiedCachedFullBoundUsingTail_eq
        hvalid.cells1024 hvalid.e1
          bound4395FiniteRho bound4395FiniteZ)
  rw [← hboundEq] at hbound
  exact hbound.trans_lt <|
    (dyadic_upper_lt_lower_of_hi_lt_lo hprop.1).trans_le
      bound4395FiniteThreshold_contains.1

structure Bound4395FiniteReport where
  cells : ℕ
  upperNumerator : ℤ
  thresholdNumerator : ℤ
  admissible : Bool
  accepted : Bool
deriving Repr

def bound4395FiniteReportValue : Bound4395FiniteReport :=
  let bound := bound4395FiniteBound
  let admissible := decide (CertifiedCachedFullAdmissible
    dyadicRouteBBuildResolutionCache.cells1024 4
      bound4395FiniteRho bound4395FiniteZ)
  let accepted :=
    decide (bound.hi < bound4395FiniteThreshold.lo) && admissible
  { cells := 1024
    upperNumerator := bound.hi
    thresholdNumerator := bound4395FiniteThreshold.lo
    admissible := admissible
    accepted := accepted }

end BerryEsseen
