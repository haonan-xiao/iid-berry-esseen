import BerryEsseen.Interval.Small.FixedExponentCover

/-!
# Smoothing / Small Parameter Boundary
-/

namespace BerryEsseen

open DyadicInterval MeasureTheory ProbabilityTheory

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def bound4395Threshold : DyadicInterval :=
  DyadicInterval.ofRat 879 2000

theorem bound4395Threshold_contains :
    bound4395Threshold.Contains ((879 : ℝ) / 2000) := by
  simpa [bound4395Threshold] using
    DyadicInterval.contains_ofRat 879 (b := 2000) (by norm_num)

def bound4395RatHull (alo blo ahi bhi : ℤ) : DyadicInterval :=
  ⟨(DyadicInterval.ofRat alo blo).lo, (DyadicInterval.ofRat ahi bhi).hi⟩

/-- The closed box used by the existing exact sensitivity audit:
`0 ≤ L ≤ 1/(16*4096)` and `2-1/4096 ≤ r ≤ 2`. -/
def bound4395BoundaryL : DyadicInterval :=
  bound4395RatHull 0 1 1 65536

def bound4395BoundaryR : DyadicInterval :=
  bound4395RatHull 8191 4096 2 1

def bound4395BoundaryL0 : DyadicInterval :=
  dyadicRouteBLeftHalf bound4395BoundaryL

def bound4395BoundaryL1 : DyadicInterval :=
  dyadicRouteBRightHalf bound4395BoundaryL

def bound4395BoundaryR0 : DyadicInterval :=
  dyadicRouteBLeftHalf bound4395BoundaryR

def bound4395BoundaryR1 : DyadicInterval :=
  dyadicRouteBRightHalf bound4395BoundaryR

/-- Exact Boolean tested by a single strengthened endpoint box at target
`879/2000`.  Its two conjuncts are precisely the outward-rounded upper-bound
comparison and the already-proved checker admissibility conditions. -/
def bound4395SmallBoxAccepted
    (N : ℕ) (L r : DyadicInterval) : Bool :=
  decide ((certifiedLargeSmallBound L r N).hi <
    bound4395Threshold.lo) &&
  decide (CertifiedLargeSmallFullAdmissible L r N)

theorem bound4395SmallBoxAccepted_true_iff
    (N : ℕ) (L r : DyadicInterval) :
    bound4395SmallBoxAccepted N L r = true ↔
      (certifiedLargeSmallBound L r N).hi <
          bound4395Threshold.lo ∧
        CertifiedLargeSmallFullAdmissible L r N := by
  simp [bound4395SmallBoxAccepted, Bool.and_eq_true]

/-- Soundness bridge for the discovery checker.  This theorem does not assert
that any box is accepted; it proves that a successful exact Boolean check has
the intended analytic meaning under exactly the existing law assumptions. -/
theorem lawNormalizedPrawitzFunctional_lt_879_2000_of_post044SmallBoxAccepted
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hX : MemLp (id : ℝ → ℝ) 3 mu)
    (hmean : ∫ x : ℝ, x ∂mu = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂mu = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment mu)))
    (hr : r.Contains (symmetrizationRatio mu))
    (haccepted : bound4395SmallBoxAccepted N L r = true) :
    lawNormalizedPrawitzFunctional n mu < (879 : ℝ) / 2000 := by
  have hprop :=
    (bound4395SmallBoxAccepted_true_iff N L r).mp haccepted
  have hreal := lawNormalizedPrawitzFunctional_le_smallBound_upper
    mu hX hmean hsecond hn hN hL hr hprop.2.1
      (fun i hi => hprop.2.2 ⟨i, hi⟩)
  exact hreal.trans_lt <|
    (dyadic_upper_lt_lower_of_hi_lt_lo hprop.1).trans_le
      bound4395Threshold_contains.1

/-- Law-level consequence of the exact post-`0.44` box checker.  This closes
the existing Prawitz smoothing comparison and therefore bounds the normalized
Kolmogorov distance, not merely the auxiliary numerical functional. -/
theorem normalizedKolmogorovDistance_lt_879_2000_of_post044SmallBoxAccepted
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n N : ℕ} (hn : 100 ≤ n) (hN : 0 < N)
    {L r : DyadicInterval}
    (hL : L.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0)))))
    (hr : r.Contains (symmetrizationRatio (P.map (X 0))))
    (haccepted : bound4395SmallBoxAccepted N L r = true) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rho *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  let mu := P.map (X 0)
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  have hKD := normalizedKolmogorovDistance_le_lawNormalizedPrawitzFunctional
    P X hindep hident hX hmean hsecond (n := n) (by omega)
  have hfunctional :=
    lawNormalizedPrawitzFunctional_lt_879_2000_of_post044SmallBoxAccepted
      mu hX hmean hsecond hn hN
        (by simpa only [mu] using hL)
        (by simpa only [mu] using hr) haccepted
  exact hKD.trans_lt <| by simpa only [mu] using hfunctional

/-- The two coordinate bisections cover the complete closed boundary box.
Shared midpoints are intentionally present in both adjacent children. -/
theorem bound4395Boundary_quadrants_cover
    {L r : ℝ}
    (hL : bound4395BoundaryL.Contains L)
    (hr : bound4395BoundaryR.Contains r) :
    (bound4395BoundaryL0.Contains L ∧
        bound4395BoundaryR0.Contains r) ∨
      (bound4395BoundaryL0.Contains L ∧
        bound4395BoundaryR1.Contains r) ∨
      (bound4395BoundaryL1.Contains L ∧
        bound4395BoundaryR0.Contains r) ∨
      (bound4395BoundaryL1.Contains L ∧
        bound4395BoundaryR1.Contains r) := by
  rcases dyadicRouteB_contains_left_or_right hL with hL0 | hL1
  · rcases dyadicRouteB_contains_left_or_right hr with hr0 | hr1
    · exact Or.inl ⟨hL0, hr0⟩
    · exact Or.inr (Or.inl ⟨hL0, hr1⟩)
  · rcases dyadicRouteB_contains_left_or_right hr with hr0 | hr1
    · exact Or.inr (Or.inr (Or.inl ⟨hL1, hr0⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hL1, hr1⟩))

/-- Exact conjunction whose future native proof would certify all four closed
quadrants of the current worst endpoint box. -/
def bound4395BoundaryAllAccepted8192 : Bool :=
  bound4395SmallBoxAccepted 8192
      bound4395BoundaryL0 bound4395BoundaryR0 &&
    bound4395SmallBoxAccepted 8192
      bound4395BoundaryL0 bound4395BoundaryR1 &&
    bound4395SmallBoxAccepted 8192
      bound4395BoundaryL1 bound4395BoundaryR0 &&
    bound4395SmallBoxAccepted 8192
      bound4395BoundaryL1 bound4395BoundaryR1

/-- A successful four-quadrant exact check bounds every admissible law point
in the complete closed boundary box. -/
theorem normalizedKolmogorovDistance_lt_879_2000_of_post044BoundaryAccepted
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 100 ≤ n)
    (hL : bound4395BoundaryL.Contains
      (routeBSmoothingScale n (thirdAbsoluteMoment (P.map (X 0)))))
    (hr : bound4395BoundaryR.Contains
      (symmetrizationRatio (P.map (X 0))))
    (haccepted : bound4395BoundaryAllAccepted8192 = true) :
    let rho := thirdAbsoluteMoment (P.map (X 0))
    Real.sqrt (n : ℝ) / rho *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  have hacc :
      ((bound4395SmallBoxAccepted 8192
            bound4395BoundaryL0 bound4395BoundaryR0 = true ∧
          bound4395SmallBoxAccepted 8192
            bound4395BoundaryL0 bound4395BoundaryR1 = true) ∧
        bound4395SmallBoxAccepted 8192
          bound4395BoundaryL1 bound4395BoundaryR0 = true) ∧
      bound4395SmallBoxAccepted 8192
        bound4395BoundaryL1 bound4395BoundaryR1 = true := by
    simpa [bound4395BoundaryAllAccepted8192, Bool.and_eq_true] using haccepted
  rcases hacc with ⟨⟨⟨hacc00, hacc01⟩, hacc10⟩, hacc11⟩
  rcases bound4395Boundary_quadrants_cover hL hr with
    h00 | h01 | h10 | h11
  · exact normalizedKolmogorovDistance_lt_879_2000_of_post044SmallBoxAccepted
      P X hindep hident hX hmean hsecond hn (by norm_num)
        h00.1 h00.2 hacc00
  · exact normalizedKolmogorovDistance_lt_879_2000_of_post044SmallBoxAccepted
      P X hindep hident hX hmean hsecond hn (by norm_num)
        h01.1 h01.2 hacc01
  · exact normalizedKolmogorovDistance_lt_879_2000_of_post044SmallBoxAccepted
      P X hindep hident hX hmean hsecond hn (by norm_num)
        h10.1 h10.2 hacc10
  · exact normalizedKolmogorovDistance_lt_879_2000_of_post044SmallBoxAccepted
      P X hindep hident hX hmean hsecond hn (by norm_num)
        h11.1 h11.2 hacc11

structure Bound4395SmallBoxResult where
  upperNumerator : ℤ
  thresholdNumerator : ℤ
  admissible : Bool
  accepted : Bool
deriving Repr

def bound4395SmallBoxResult
    (N : ℕ) (L r : DyadicInterval) : Bound4395SmallBoxResult :=
  let bound := certifiedLargeSmallBound L r N
  let admissible := decide (CertifiedLargeSmallFullAdmissible L r N)
  let accepted :=
    decide (bound.hi < bound4395Threshold.lo) && admissible
  { upperNumerator := bound.hi
    thresholdNumerator := bound4395Threshold.lo
    admissible := admissible
    accepted := accepted }

def bound4395BoundaryQuadrants8192 :
    List Bound4395SmallBoxResult :=
  [ bound4395SmallBoxResult 8192
      bound4395BoundaryL0 bound4395BoundaryR0
  , bound4395SmallBoxResult 8192
      bound4395BoundaryL0 bound4395BoundaryR1
  , bound4395SmallBoxResult 8192
      bound4395BoundaryL1 bound4395BoundaryR0
  , bound4395SmallBoxResult 8192
      bound4395BoundaryL1 bound4395BoundaryR1 ]

structure Bound4395BoundaryReport where
  quadrants : List Bound4395SmallBoxResult
  allAccepted : Bool
deriving Repr

def bound4395BoundaryReport8192 : Bound4395BoundaryReport :=
  let quadrants := bound4395BoundaryQuadrants8192
  { quadrants := quadrants
    allAccepted := quadrants.all (·.accepted) }

end BerryEsseen
