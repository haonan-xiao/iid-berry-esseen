import BerryEsseen.Interval.Finite.Cache
import BerryEsseen.Interval.Prawitz.FiniteLeafTree

/-!
# Interval / Finite / Leaf
-/

namespace BerryEsseen

open MeasureTheory ProbabilityTheory DyadicInterval

set_option maxRecDepth 10000

def certifiedVerifyLeafTree
    (cache : DyadicRouteBResolutionCache) (n : ℕ) :
    DyadicRouteBLeafTree → DyadicInterval → DyadicInterval → Bool
  | .leaf, rho, z => certifiedCachedFiniteBoxAccepted cache n rho z
  | .splitRho left right, rho, z =>
      certifiedVerifyLeafTree cache n left (dyadicRouteBLeftHalf rho) z &&
        certifiedVerifyLeafTree cache n right (dyadicRouteBRightHalf rho) z
  | .splitZ left right, rho, z =>
      certifiedVerifyLeafTree cache n left rho (dyadicRouteBLeftHalf z) &&
        certifiedVerifyLeafTree cache n right rho (dyadicRouteBRightHalf z)

theorem certifiedVerifyLeafTree_sound
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) {tree : DyadicRouteBLeafTree}
    {rho z : DyadicInterval}
    (hverify : certifiedVerifyLeafTree cache n tree rho z = true)
    (hrho : rho.Contains (thirdAbsoluteMoment (P.map (X 0))))
    (hz : z.Contains
      (thirdAbsoluteMoment (P.map (X 0)) *
        (symmetrizationRatio (P.map (X 0)) - 1))) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  induction tree generalizing rho z with
  | leaf =>
      exact normalizedKolmogorovDistance_lt_044_of_cachedFiniteBoxAccepted
        hcache P X hindep hident hX hmean hsecond hn hverify hrho hz
  | splitRho left right ihLeft ihRight =>
      have hchildren :
          certifiedVerifyLeafTree cache n left
                (dyadicRouteBLeftHalf rho) z = true ∧
            certifiedVerifyLeafTree cache n right
                (dyadicRouteBRightHalf rho) z = true := by
        simpa [certifiedVerifyLeafTree, Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hrho with hleft | hright
      · exact ihLeft hchildren.1 hleft hz
      · exact ihRight hchildren.2 hright hz
  | splitZ left right ihLeft ihRight =>
      have hchildren :
          certifiedVerifyLeafTree cache n left rho
                (dyadicRouteBLeftHalf z) = true ∧
            certifiedVerifyLeafTree cache n right rho
                (dyadicRouteBRightHalf z) = true := by
        simpa [certifiedVerifyLeafTree, Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
      · exact ihLeft hchildren.1 hrho hleft
      · exact ihRight hchildren.2 hrho hright

def certifiedLeafTreeCertificate
    (n : ℕ) (tree : DyadicRouteBLeafTree) : Bool :=
  let cache := dyadicRouteBBuildResolutionCache
  certifiedVerifyLeafTree cache n tree
    (dyadicRouteBFiniteRootRho n) dyadicRouteBFiniteRootZ

theorem normalizedKolmogorovDistance_lt_044_of_certifiedLeafTreeCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) {tree : DyadicRouteBLeafTree}
    (hcertificate : certifiedLeafTreeCertificate n tree = true)
    (hrhoLower : 1 ≤ thirdAbsoluteMoment (P.map (X 0)))
    (hrhoUpper : thirdAbsoluteMoment (P.map (X 0)) ≤
      ((56 : ℝ) / 45) * Real.sqrt (n : ℝ))
    (hzLower : 0 ≤ thirdAbsoluteMoment (P.map (X 0)) *
      (symmetrizationRatio (P.map (X 0)) - 1))
    (hzUpper : thirdAbsoluteMoment (P.map (X 0)) *
      (symmetrizationRatio (P.map (X 0)) - 1) ≤ 1) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  exact certifiedVerifyLeafTree_sound
    dyadicRouteBBuildResolutionCache_valid P X hindep hident hX hmean hsecond
      hn hcertificate
      (dyadicRouteBFiniteRootRho_contains hrhoLower hrhoUpper)
      (dyadicRouteBFiniteRootZ_contains hzLower hzUpper)

def certifiedLeafCodeCertificate (n : ℕ) (code : String) : Bool :=
  match dyadicRouteBLeafTreeOfCode code with
  | some tree => certifiedLeafTreeCertificate n tree
  | none => false

theorem normalizedKolmogorovDistance_lt_044_of_certifiedLeafCodeCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) {code : String}
    (hcertificate : certifiedLeafCodeCertificate n code = true)
    (hrhoLower : 1 ≤ thirdAbsoluteMoment (P.map (X 0)))
    (hrhoUpper : thirdAbsoluteMoment (P.map (X 0)) ≤
      ((56 : ℝ) / 45) * Real.sqrt (n : ℝ))
    (hzLower : 0 ≤ thirdAbsoluteMoment (P.map (X 0)) *
      (symmetrizationRatio (P.map (X 0)) - 1))
    (hzUpper : thirdAbsoluteMoment (P.map (X 0)) *
      (symmetrizationRatio (P.map (X 0)) - 1) ≤ 1) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  unfold certifiedLeafCodeCertificate at hcertificate
  split at hcertificate
  next tree htree =>
    exact normalizedKolmogorovDistance_lt_044_of_certifiedLeafTreeCertificate
      P X hindep hident hX hmean hsecond hn hcertificate
        hrhoLower hrhoUpper hzLower hzUpper
  next => simp at hcertificate

/-- Verify an existing split topology and, at every old leaf, run a fresh certified cover of
bounded additional depth.  This is useful for treating the baseline bound codes solely as subdivision
proposals while allowing the sharper the first-absolute-moment bounds checker to add whatever local refinement it needs. -/
def certifiedVerifyLeafTreeWithRefinement
    (cache : DyadicRouteBResolutionCache) (n extraFuel : ℕ) :
    DyadicRouteBLeafTree → DyadicInterval → DyadicInterval → Bool
  | .leaf, rho, z =>
      certifiedCachedFiniteCover cache n extraFuel rho z
  | .splitRho left right, rho, z =>
      certifiedVerifyLeafTreeWithRefinement cache n extraFuel left
            (dyadicRouteBLeftHalf rho) z &&
        certifiedVerifyLeafTreeWithRefinement cache n extraFuel right
            (dyadicRouteBRightHalf rho) z
  | .splitZ left right, rho, z =>
      certifiedVerifyLeafTreeWithRefinement cache n extraFuel left rho
            (dyadicRouteBLeftHalf z) &&
        certifiedVerifyLeafTreeWithRefinement cache n extraFuel right rho
            (dyadicRouteBRightHalf z)

theorem certifiedVerifyLeafTreeWithRefinement_sound
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) {extraFuel : ℕ}
    {tree : DyadicRouteBLeafTree} {rho z : DyadicInterval}
    (hverify : certifiedVerifyLeafTreeWithRefinement
      cache n extraFuel tree rho z = true)
    (hrho : rho.Contains (thirdAbsoluteMoment (P.map (X 0))))
    (hz : z.Contains
      (thirdAbsoluteMoment (P.map (X 0)) *
        (symmetrizationRatio (P.map (X 0)) - 1))) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  induction tree generalizing rho z with
  | leaf =>
      exact certifiedCachedFiniteCover_sound
        hcache P X hindep hident hX hmean hsecond hn hverify hrho hz
  | splitRho left right ihLeft ihRight =>
      have hchildren :
          certifiedVerifyLeafTreeWithRefinement cache n extraFuel left
                (dyadicRouteBLeftHalf rho) z = true ∧
            certifiedVerifyLeafTreeWithRefinement cache n extraFuel right
                (dyadicRouteBRightHalf rho) z = true := by
        simpa [certifiedVerifyLeafTreeWithRefinement, Bool.and_eq_true]
          using hverify
      rcases dyadicRouteB_contains_left_or_right hrho with hleft | hright
      · exact ihLeft hchildren.1 hleft hz
      · exact ihRight hchildren.2 hright hz
  | splitZ left right ihLeft ihRight =>
      have hchildren :
          certifiedVerifyLeafTreeWithRefinement cache n extraFuel left rho
                (dyadicRouteBLeftHalf z) = true ∧
            certifiedVerifyLeafTreeWithRefinement cache n extraFuel right rho
                (dyadicRouteBRightHalf z) = true := by
        simpa [certifiedVerifyLeafTreeWithRefinement, Bool.and_eq_true]
          using hverify
      rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
      · exact ihLeft hchildren.1 hrho hleft
      · exact ihRight hchildren.2 hrho hright

def certifiedRefinedLeafTreeCertificate
    (n extraFuel : ℕ) (tree : DyadicRouteBLeafTree) : Bool :=
  let cache := dyadicRouteBBuildResolutionCache
  certifiedVerifyLeafTreeWithRefinement cache n extraFuel tree
    (dyadicRouteBFiniteRootRho n) dyadicRouteBFiniteRootZ

theorem normalizedKolmogorovDistance_lt_044_of_certifiedRefinedLeafTreeCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) {extraFuel : ℕ}
    {tree : DyadicRouteBLeafTree}
    (hcertificate :
      certifiedRefinedLeafTreeCertificate n extraFuel tree = true)
    (hrhoLower : 1 ≤ thirdAbsoluteMoment (P.map (X 0)))
    (hrhoUpper : thirdAbsoluteMoment (P.map (X 0)) ≤
      ((56 : ℝ) / 45) * Real.sqrt (n : ℝ))
    (hzLower : 0 ≤ thirdAbsoluteMoment (P.map (X 0)) *
      (symmetrizationRatio (P.map (X 0)) - 1))
    (hzUpper : thirdAbsoluteMoment (P.map (X 0)) *
      (symmetrizationRatio (P.map (X 0)) - 1) ≤ 1) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  exact certifiedVerifyLeafTreeWithRefinement_sound
    dyadicRouteBBuildResolutionCache_valid P X hindep hident hX hmean hsecond
      hn hcertificate
      (dyadicRouteBFiniteRootRho_contains hrhoLower hrhoUpper)
      (dyadicRouteBFiniteRootZ_contains hzLower hzUpper)

def certifiedRefinedLeafCodeCertificate
    (n extraFuel : ℕ) (code : String) : Bool :=
  match dyadicRouteBLeafTreeOfCode code with
  | some tree =>
      certifiedRefinedLeafTreeCertificate n extraFuel tree
  | none => false

theorem normalizedKolmogorovDistance_lt_044_of_certifiedRefinedLeafCodeCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) {extraFuel : ℕ} {code : String}
    (hcertificate :
      certifiedRefinedLeafCodeCertificate n extraFuel code = true)
    (hrhoLower : 1 ≤ thirdAbsoluteMoment (P.map (X 0)))
    (hrhoUpper : thirdAbsoluteMoment (P.map (X 0)) ≤
      ((56 : ℝ) / 45) * Real.sqrt (n : ℝ))
    (hzLower : 0 ≤ thirdAbsoluteMoment (P.map (X 0)) *
      (symmetrizationRatio (P.map (X 0)) - 1))
    (hzUpper : thirdAbsoluteMoment (P.map (X 0)) *
      (symmetrizationRatio (P.map (X 0)) - 1) ≤ 1) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (44 : ℝ) / 100 := by
  unfold certifiedRefinedLeafCodeCertificate at hcertificate
  split at hcertificate
  next tree htree =>
    exact
      normalizedKolmogorovDistance_lt_044_of_certifiedRefinedLeafTreeCertificate
        P X hindep hident hX hmean hsecond hn hcertificate
          hrhoLower hrhoUpper hzLower hzUpper
  next => simp at hcertificate

end BerryEsseen
