import BerryEsseen.Interval.Small.FixedExponentIntegral

/-!
# Interval / Variable Exponent
-/

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def largeVariableAlpha
    (L : DyadicInterval) : DyadicInterval :=
  certifiedLargeMax dyadicRouteBLargeAlpha <|
    DyadicInterval.sub (DyadicInterval.point 1) (DyadicInterval.sqr L)

def certifiedLargeSmallVariableAlphaExp
    (L r y : DyadicInterval) : DyadicInterval :=
  dyadicExpNeg <|
    DyadicInterval.mul (largeVariableAlpha L)
      (certifiedLargeSmallStrongQ L r y)

def certifiedLargeSmallVariableAlphaF1
    (L r y : DyadicInterval) : DyadicInterval :=
  let scale := DyadicInterval.div
    (DyadicInterval.mul (DyadicInterval.point 8)
      (DyadicInterval.sqr checkerPi))
    (powi r 3)
  let withY := DyadicInterval.mul scale (DyadicInterval.sqr y)
  let withP0 := DyadicInterval.mul withY
    (dyadicRouteBLargeSmallP0 L y)
  DyadicInterval.mul withP0
    (DyadicInterval.mul
      (dyadicPrawitzDstarFeasible r
        (dyadicRouteBLargeSmallV L y))
      (certifiedLargeSmallVariableAlphaExp L r y))

def certifiedLargeSmallVariableAlphaCellValue
    (L r y : DyadicInterval) : DyadicInterval :=
  DyadicInterval.add
    (DyadicInterval.add
      (certifiedLargeSmallVariableAlphaF1 L r y)
      (dyadicRouteBLargeSmallF3 L r y))
    (dyadicRouteBLargeSmallF2 L r y)

def certifiedLargeSmallVariableAlphaFiniteSum
    (L r : DyadicInterval) (N : ℕ) : DyadicInterval :=
  intervalNatSum (fun i =>
    DyadicInterval.mul (dyadicRouteBLargeSmallYWidth N i)
      (certifiedLargeSmallVariableAlphaCellValue L r
        (dyadicRouteBLargeSmallYCell N i))) N

def certifiedLargeSmallVariableAlphaBound
    (L r : DyadicInterval) (N : ℕ) : DyadicInterval :=
  DyadicInterval.add
    (certifiedLargeSmallVariableAlphaFiniteSum L r N)
    dyadicRouteBLargeSmallOmission

structure CertifiedLargeSmallVariableAlphaCellAdmissible
    (L r y : DyadicInterval) : Prop where
  base : CertifiedLargeSmallCellAdmissible L r y
  alphaArgNonnegative :
    0 ≤ (DyadicInterval.mul (largeVariableAlpha L)
      (certifiedLargeSmallStrongQ L r y)).lo
  valueOrdered :
    (certifiedLargeSmallVariableAlphaCellValue L r y).Ordered

instance (L r y : DyadicInterval) :
    Decidable (CertifiedLargeSmallVariableAlphaCellAdmissible L r y) :=
  decidable_of_iff
    (CertifiedLargeSmallCellAdmissible L r y ∧
      0 ≤ (DyadicInterval.mul (largeVariableAlpha L)
        (certifiedLargeSmallStrongQ L r y)).lo ∧
      (certifiedLargeSmallVariableAlphaCellValue L r y).lo ≤
        (certifiedLargeSmallVariableAlphaCellValue L r y).hi) <| by
    constructor
    · rintro ⟨hbase, harg, hordered⟩
      exact ⟨hbase, harg, hordered⟩
    · intro h
      exact ⟨h.base, h.alphaArgNonnegative, h.valueOrdered⟩

def CertifiedLargeSmallVariableAlphaFullAdmissible
    (L r : DyadicInterval) (N : ℕ) : Prop :=
  CertifiedLargeSmallBoxAdmissible L r ∧
    ∀ i : Fin N,
      CertifiedLargeSmallVariableAlphaCellAdmissible L r
        (dyadicRouteBLargeSmallYCell N i.1)

instance (L r : DyadicInterval) (N : ℕ) :
    Decidable (CertifiedLargeSmallVariableAlphaFullAdmissible L r N) := by
  unfold CertifiedLargeSmallVariableAlphaFullAdmissible
  infer_instance

end BerryEsseen
