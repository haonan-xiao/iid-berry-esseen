import BerryEsseen.Interval.Finite.Adaptive
import BerryEsseen.Certificates.Data.FinitePartitions

/-!
# Interval / Finite / Adaptive Full Cover
-/

namespace BerryEsseen

open MeasureTheory ProbabilityTheory DyadicInterval

set_option maxRecDepth 10000

def bound4395FiniteTargetAwareCover
    (cache : DyadicRouteBResolutionCache) (n : ℕ) :
    ℕ → DyadicInterval → DyadicInterval → Bool
  | 0, rho, z => bound4395FiniteTargetAwareAccepted cache n rho z
  | fuel + 1, rho, z =>
      if bound4395FiniteTargetAwareAccepted cache n rho z then true
      else if dyadicRouteBSplitRho n rho z then
        bound4395FiniteTargetAwareCover cache n fuel
              (dyadicRouteBLeftHalf rho) z &&
          bound4395FiniteTargetAwareCover cache n fuel
              (dyadicRouteBRightHalf rho) z
      else
        bound4395FiniteTargetAwareCover cache n fuel rho
              (dyadicRouteBLeftHalf z) &&
          bound4395FiniteTargetAwareCover cache n fuel rho
              (dyadicRouteBRightHalf z)

noncomputable section

theorem bound4395FiniteTargetAwareCover_sound
    {cache : DyadicRouteBResolutionCache} (hcache : cache.Valid)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) {fuel : ℕ} {rho z : DyadicInterval}
    (hcover : bound4395FiniteTargetAwareCover
      cache n fuel rho z = true)
    (hrho : rho.Contains (thirdAbsoluteMoment (P.map (X 0))))
    (hz : z.Contains
      (thirdAbsoluteMoment (P.map (X 0)) *
        (symmetrizationRatio (P.map (X 0)) - 1))) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  induction fuel generalizing rho z with
  | zero =>
      exact
        normalizedKolmogorovDistance_lt_879_2000_of_post044FiniteTargetAware
          hcache P X hindep hident hX hmean hsecond hn hcover hrho hz
  | succ fuel ih =>
      cases haccepted :
          bound4395FiniteTargetAwareAccepted cache n rho z with
      | true =>
          exact
            normalizedKolmogorovDistance_lt_879_2000_of_post044FiniteTargetAware
              hcache P X hindep hident hX hmean hsecond hn
                haccepted hrho hz
      | false =>
          by_cases hsplit : dyadicRouteBSplitRho n rho z
          · have hchildren :
                bound4395FiniteTargetAwareCover cache n fuel
                    (dyadicRouteBLeftHalf rho) z = true ∧
                  bound4395FiniteTargetAwareCover cache n fuel
                    (dyadicRouteBRightHalf rho) z = true := by
              simpa [bound4395FiniteTargetAwareCover, haccepted, hsplit,
                Bool.and_eq_true] using hcover
            rcases dyadicRouteB_contains_left_or_right hrho with hleft | hright
            · exact ih hchildren.1 hleft hz
            · exact ih hchildren.2 hright hz
          · have hchildren :
                bound4395FiniteTargetAwareCover cache n fuel rho
                    (dyadicRouteBLeftHalf z) = true ∧
                  bound4395FiniteTargetAwareCover cache n fuel rho
                    (dyadicRouteBRightHalf z) = true := by
              simpa [bound4395FiniteTargetAwareCover, haccepted, hsplit,
                Bool.and_eq_true] using hcover
            rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
            · exact ih hchildren.1 hrho hleft
            · exact ih hchildren.2 hrho hright

end

def bound4395FiniteTargetAwareVerifyLeafTree
    (cache : DyadicRouteBResolutionCache) (n extraFuel : ℕ) :
    DyadicRouteBLeafTree → DyadicInterval → DyadicInterval → Bool
  | .leaf, rho, z =>
      bound4395FiniteTargetAwareCover cache n extraFuel rho z
  | .splitRho left right, rho, z =>
      bound4395FiniteTargetAwareVerifyLeafTree cache n extraFuel left
            (dyadicRouteBLeftHalf rho) z &&
        bound4395FiniteTargetAwareVerifyLeafTree cache n extraFuel right
            (dyadicRouteBRightHalf rho) z
  | .splitZ left right, rho, z =>
      bound4395FiniteTargetAwareVerifyLeafTree cache n extraFuel left rho
            (dyadicRouteBLeftHalf z) &&
        bound4395FiniteTargetAwareVerifyLeafTree cache n extraFuel right rho
            (dyadicRouteBRightHalf z)

noncomputable section

theorem bound4395FiniteTargetAwareVerifyLeafTree_sound
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
    (hverify : bound4395FiniteTargetAwareVerifyLeafTree
      cache n extraFuel tree rho z = true)
    (hrho : rho.Contains (thirdAbsoluteMoment (P.map (X 0))))
    (hz : z.Contains
      (thirdAbsoluteMoment (P.map (X 0)) *
        (symmetrizationRatio (P.map (X 0)) - 1))) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  induction tree generalizing rho z with
  | leaf =>
      exact bound4395FiniteTargetAwareCover_sound
        hcache P X hindep hident hX hmean hsecond hn hverify hrho hz
  | splitRho left right ihLeft ihRight =>
      have hchildren :
          bound4395FiniteTargetAwareVerifyLeafTree cache n extraFuel left
                (dyadicRouteBLeftHalf rho) z = true ∧
            bound4395FiniteTargetAwareVerifyLeafTree cache n extraFuel right
                (dyadicRouteBRightHalf rho) z = true := by
        simpa [bound4395FiniteTargetAwareVerifyLeafTree,
          Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hrho with hleft | hright
      · exact ihLeft hchildren.1 hleft hz
      · exact ihRight hchildren.2 hright hz
  | splitZ left right ihLeft ihRight =>
      have hchildren :
          bound4395FiniteTargetAwareVerifyLeafTree cache n extraFuel left rho
                (dyadicRouteBLeftHalf z) = true ∧
            bound4395FiniteTargetAwareVerifyLeafTree cache n extraFuel right rho
                (dyadicRouteBRightHalf z) = true := by
        simpa [bound4395FiniteTargetAwareVerifyLeafTree,
          Bool.and_eq_true] using hverify
      rcases dyadicRouteB_contains_left_or_right hz with hleft | hright
      · exact ihLeft hchildren.1 hrho hleft
      · exact ihRight hchildren.2 hrho hright

end

def bound4395FiniteTargetAwareLeafTreeCertificate
    (n extraFuel : ℕ) (tree : DyadicRouteBLeafTree) : Bool :=
  bound4395FiniteTargetAwareVerifyLeafTree
    dyadicRouteBBuildResolutionCache n extraFuel tree
      (dyadicRouteBFiniteRootRho n) dyadicRouteBFiniteRootZ

def bound4395FiniteTargetAwareLeafCodeCertificate
    (n extraFuel : ℕ) (code : String) : Bool :=
  match dyadicRouteBLeafTreeOfCode code with
  | some tree =>
      bound4395FiniteTargetAwareLeafTreeCertificate n extraFuel tree
  | none => false

def bound4395OldFiniteTargetAwareLeafCodeCertificate
    (n extraFuel : ℕ) : Bool :=
  match certifiedOldLeafCode n with
  | some code =>
      bound4395FiniteTargetAwareLeafCodeCertificate n extraFuel code
  | none => false

noncomputable section

theorem normalizedKolmogorovDistance_lt_879_2000_of_post044OldFiniteTargetAware
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ)
    (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hX : MemLp (id : ℝ → ℝ) 3 (P.map (X 0)))
    (hmean : ∫ x : ℝ, x ∂(P.map (X 0)) = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂(P.map (X 0)) = 1)
    {n : ℕ} (hn : 1 ≤ n) {extraFuel : ℕ}
    (hcertificate :
      bound4395OldFiniteTargetAwareLeafCodeCertificate
        n extraFuel = true)
    (hrhoLower : 1 ≤ thirdAbsoluteMoment (P.map (X 0)))
    (hrhoUpper : thirdAbsoluteMoment (P.map (X 0)) ≤
      ((56 : ℝ) / 45) * Real.sqrt (n : ℝ))
    (hzLower : 0 ≤ thirdAbsoluteMoment (P.map (X 0)) *
      (symmetrizationRatio (P.map (X 0)) - 1))
    (hzUpper : thirdAbsoluteMoment (P.map (X 0)) *
      (symmetrizationRatio (P.map (X 0)) - 1) ≤ 1) :
    Real.sqrt (n : ℝ) / thirdAbsoluteMoment (P.map (X 0)) *
        kolmogorovDistance (standardizedSumLaw P X n) standardNormalLaw <
      (879 : ℝ) / 2000 := by
  unfold bound4395OldFiniteTargetAwareLeafCodeCertificate at hcertificate
  cases hcode : certifiedOldLeafCode n with
  | none => simp [hcode] at hcertificate
  | some code =>
      rw [hcode] at hcertificate
      cases htree : dyadicRouteBLeafTreeOfCode code with
      | none =>
          simp [bound4395FiniteTargetAwareLeafCodeCertificate, htree]
            at hcertificate
      | some tree =>
        have htreeCertificate :
            bound4395FiniteTargetAwareLeafTreeCertificate
              n extraFuel tree = true := by
          simpa [bound4395FiniteTargetAwareLeafCodeCertificate, htree]
            using hcertificate
        exact bound4395FiniteTargetAwareVerifyLeafTree_sound
          dyadicRouteBBuildResolutionCache_valid
            P X hindep hident hX hmean hsecond hn htreeCertificate
            (dyadicRouteBFiniteRootRho_contains hrhoLower hrhoUpper)
            (dyadicRouteBFiniteRootZ_contains hzLower hzUpper)

end

end BerryEsseen
