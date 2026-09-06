import BerryEsseen.Interval.Finite.AdaptiveFullCover

/-!
# Interval / Finite / Adaptive Failure Diagnostic
-/

namespace BerryEsseen

set_option maxRecDepth 10000
set_option maxHeartbeats 0

structure Bound4395FiniteResolutionReport where
  cells : ℕ
  upperNumerator : ℤ
  thresholdNumerator : ℤ
  marginNumerator : ℤ
  strict : Bool
  boxAdmissible : Bool
  tailAdmissible : Bool
  lowCellsAdmissible : Bool
  highCellsAdmissible : Bool
  admissible : Bool
  accepted : Bool
deriving Repr

def bound4395FiniteResolutionReport
    {N : ℕ} (cellCache : DyadicRouteBCellCache N)
    (e1Cache : DyadicRouteBE1Cache)
    (n : ℕ) (rho z : DyadicInterval) :
    Bound4395FiniteResolutionReport :=
  let bound := certifiedCachedFullBound cellCache e1Cache n rho z
  let strict := decide (bound.hi < bound4395FiniteThreshold.lo)
  let boxAdmissible := decide (DyadicRouteBBoxAdmissible rho z)
  let tailAdmissible := decide (DyadicRouteBTailAdmissible n rho z)
  let lowCellsAdmissible := decide (∀ i : Fin N,
    CertifiedLowCellAdmissible n rho z (cellCache.low.get i))
  let highCellsAdmissible := decide (∀ i : Fin N,
    CertifiedHighCellAdmissible n rho z (cellCache.high.get i))
  let admissible := boxAdmissible && tailAdmissible &&
    lowCellsAdmissible && highCellsAdmissible
  { cells := N
    upperNumerator := bound.hi
    thresholdNumerator := bound4395FiniteThreshold.lo
    marginNumerator := bound4395FiniteThreshold.lo - bound.hi
    strict := strict
    boxAdmissible := boxAdmissible
    tailAdmissible := tailAdmissible
    lowCellsAdmissible := lowCellsAdmissible
    highCellsAdmissible := highCellsAdmissible
    admissible := admissible
    accepted := strict && admissible }

structure Bound4395FiniteTargetAwareFailure where
  n : ℕ
  path : String
  remainingFuel : ℕ
  rho : DyadicInterval
  z : DyadicInterval
  cells256 : Bound4395FiniteResolutionReport
  cells1024 : Bound4395FiniteResolutionReport
  cells2048 : Bound4395FiniteResolutionReport
deriving Repr

inductive Bound4395FiniteTargetAwareDiagnosticResult where
  | allAccepted (n : ℕ)
  | firstFailure (failure : Bound4395FiniteTargetAwareFailure)
  | oldLeafCodeUnavailable (n : ℕ)
  | oldLeafCodeMalformed (n : ℕ)
deriving Repr

def bound4395FiniteTargetAwareFailureAt
    (cache : DyadicRouteBResolutionCache) (n : ℕ)
    (path : String) (remainingFuel : ℕ)
    (rho z : DyadicInterval) : Bound4395FiniteTargetAwareFailure :=
  { n := n
    path := path
    remainingFuel := remainingFuel
    rho := rho
    z := z
    cells256 := bound4395FiniteResolutionReport
      cache.cells256 cache.e1 n rho z
    cells1024 := bound4395FiniteResolutionReport
      cache.cells1024 cache.e1 n rho z
    cells2048 := bound4395FiniteResolutionReport
      cache.cells2048 cache.e1 n rho z }

def findBound4395FiniteTargetAwareCoverFailure
    (cache : DyadicRouteBResolutionCache) (n : ℕ) :
    ℕ → String → DyadicInterval → DyadicInterval →
      Option Bound4395FiniteTargetAwareFailure
  | 0, path, rho, z =>
      if bound4395FiniteTargetAwareAccepted cache n rho z then none
      else some (bound4395FiniteTargetAwareFailureAt
        cache n path 0 rho z)
  | fuel + 1, path, rho, z =>
      if bound4395FiniteTargetAwareAccepted cache n rho z then none
      else if dyadicRouteBSplitRho n rho z then
        match findBound4395FiniteTargetAwareCoverFailure cache n fuel
            (path ++ "rho0") (dyadicRouteBLeftHalf rho) z with
        | some failure => some failure
        | none => findBound4395FiniteTargetAwareCoverFailure cache n fuel
            (path ++ "rho1") (dyadicRouteBRightHalf rho) z
      else
        match findBound4395FiniteTargetAwareCoverFailure cache n fuel
            (path ++ "z0") rho (dyadicRouteBLeftHalf z) with
        | some failure => some failure
        | none => findBound4395FiniteTargetAwareCoverFailure cache n fuel
            (path ++ "z1") rho (dyadicRouteBRightHalf z)

def findBound4395FiniteTargetAwareTreeFailure
    (cache : DyadicRouteBResolutionCache) (n extraFuel : ℕ) :
    DyadicRouteBLeafTree → String → DyadicInterval → DyadicInterval →
      Option Bound4395FiniteTargetAwareFailure
  | .leaf, path, rho, z =>
      findBound4395FiniteTargetAwareCoverFailure
        cache n extraFuel path rho z
  | .splitRho left right, path, rho, z =>
      match findBound4395FiniteTargetAwareTreeFailure cache n extraFuel
          left (path ++ "R0") (dyadicRouteBLeftHalf rho) z with
      | some failure => some failure
      | none => findBound4395FiniteTargetAwareTreeFailure cache n extraFuel
          right (path ++ "R1") (dyadicRouteBRightHalf rho) z
  | .splitZ left right, path, rho, z =>
      match findBound4395FiniteTargetAwareTreeFailure cache n extraFuel
          left (path ++ "Z0") rho (dyadicRouteBLeftHalf z) with
      | some failure => some failure
      | none => findBound4395FiniteTargetAwareTreeFailure cache n extraFuel
          right (path ++ "Z1") rho (dyadicRouteBRightHalf z)

def bound4395FiniteTargetAwareFirstFailure
    (n extraFuel : ℕ) : Option Bound4395FiniteTargetAwareFailure :=
  match certifiedOldLeafCode n with
  | none => none
  | some code =>
      match dyadicRouteBLeafTreeOfCode code with
      | none => none
      | some tree =>
          findBound4395FiniteTargetAwareTreeFailure
            dyadicRouteBBuildResolutionCache n extraFuel tree ""
              (dyadicRouteBFiniteRootRho n) dyadicRouteBFiniteRootZ

/-- Fail-closed public diagnostic entry point.  Unlike the `Option` helper,
this distinguishes a fully accepted cover from missing or malformed legacy
leaf-code input.  It remains discovery-only and is never imported by a proof
theorem. -/
def bound4395FiniteTargetAwareDiagnostic
    (n extraFuel : ℕ) : Bound4395FiniteTargetAwareDiagnosticResult :=
  match certifiedOldLeafCode n with
  | none => .oldLeafCodeUnavailable n
  | some code =>
      match dyadicRouteBLeafTreeOfCode code with
      | none => .oldLeafCodeMalformed n
      | some tree =>
          match findBound4395FiniteTargetAwareTreeFailure
              dyadicRouteBBuildResolutionCache n extraFuel tree ""
                (dyadicRouteBFiniteRootRho n) dyadicRouteBFiniteRootZ with
          | none => .allAccepted n
          | some failure => .firstFailure failure

end BerryEsseen
