import BerryEsseen.Interval.VariableExponent
import BerryEsseen.Smoothing.SmallParameterBoundary

/-!
# Smoothing / Variable Exponent Boundary
-/

namespace BerryEsseen

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def bound4395VariableAlphaSmallBoxAccepted
    (N : ℕ) (L r : DyadicInterval) : Bool :=
  decide ((certifiedLargeSmallVariableAlphaBound L r N).hi <
    bound4395Threshold.lo) &&
  decide (CertifiedLargeSmallVariableAlphaFullAdmissible L r N)

structure Bound4395VariableAlphaBoxResult where
  upperNumerator : ℤ
  thresholdNumerator : ℤ
  admissible : Bool
  accepted : Bool
deriving Repr

def bound4395VariableAlphaBoxResult
    (N : ℕ) (L r : DyadicInterval) :
    Bound4395VariableAlphaBoxResult :=
  let bound := certifiedLargeSmallVariableAlphaBound L r N
  let admissible :=
    decide (CertifiedLargeSmallVariableAlphaFullAdmissible L r N)
  { upperNumerator := bound.hi
    thresholdNumerator := bound4395Threshold.lo
    admissible := admissible
    accepted := decide (bound.hi < bound4395Threshold.lo) && admissible }

def bound4395VariableAlphaBoundaryQuadrants8192 :
    List Bound4395VariableAlphaBoxResult :=
  [ bound4395VariableAlphaBoxResult 8192
      bound4395BoundaryL0 bound4395BoundaryR0
  , bound4395VariableAlphaBoxResult 8192
      bound4395BoundaryL0 bound4395BoundaryR1
  , bound4395VariableAlphaBoxResult 8192
      bound4395BoundaryL1 bound4395BoundaryR0
  , bound4395VariableAlphaBoxResult 8192
      bound4395BoundaryL1 bound4395BoundaryR1 ]

def bound4395VariableAlphaBoundaryAllAccepted8192 : Bool :=
  bound4395VariableAlphaBoundaryQuadrants8192.all (·.accepted)

end BerryEsseen
