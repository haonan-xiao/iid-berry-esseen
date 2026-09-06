import BerryEsseen.Interval.Finite.AdaptiveFullCover

/-!
# Interval / Finite / Adaptive Fuel Monotonicity
-/

namespace BerryEsseen

open DyadicInterval

set_option maxRecDepth 10000

theorem bound4395FiniteTargetAwareCover_succ_of_true
    (cache : DyadicRouteBResolutionCache) (n : ℕ)
    {fuel : ℕ} {rho z : DyadicInterval}
    (hcover : bound4395FiniteTargetAwareCover
      cache n fuel rho z = true) :
    bound4395FiniteTargetAwareCover
      cache n (fuel + 1) rho z = true := by
  induction fuel generalizing rho z with
  | zero =>
      have haccepted :
          bound4395FiniteTargetAwareAccepted cache n rho z = true := by
        simpa [bound4395FiniteTargetAwareCover] using hcover
      simp [bound4395FiniteTargetAwareCover, haccepted]
  | succ fuel ih =>
      cases haccepted :
          bound4395FiniteTargetAwareAccepted cache n rho z with
      | true =>
          simp [bound4395FiniteTargetAwareCover, haccepted]
      | false =>
          by_cases hsplit : dyadicRouteBSplitRho n rho z
          · have hchildren :
                bound4395FiniteTargetAwareCover cache n fuel
                    (dyadicRouteBLeftHalf rho) z = true ∧
                  bound4395FiniteTargetAwareCover cache n fuel
                    (dyadicRouteBRightHalf rho) z = true := by
              simpa [bound4395FiniteTargetAwareCover, haccepted, hsplit,
                Bool.and_eq_true] using hcover
            simpa [bound4395FiniteTargetAwareCover, haccepted, hsplit,
              Bool.and_eq_true] using
                And.intro (ih hchildren.1) (ih hchildren.2)
          · have hchildren :
                bound4395FiniteTargetAwareCover cache n fuel rho
                    (dyadicRouteBLeftHalf z) = true ∧
                  bound4395FiniteTargetAwareCover cache n fuel rho
                    (dyadicRouteBRightHalf z) = true := by
              simpa [bound4395FiniteTargetAwareCover, haccepted, hsplit,
                Bool.and_eq_true] using hcover
            simpa [bound4395FiniteTargetAwareCover, haccepted, hsplit,
              Bool.and_eq_true] using
                And.intro (ih hchildren.1) (ih hchildren.2)

theorem bound4395FiniteTargetAwareVerifyLeafTree_succ_of_true
    (cache : DyadicRouteBResolutionCache) (n extraFuel : ℕ)
    {tree : DyadicRouteBLeafTree} {rho z : DyadicInterval}
    (hverify : bound4395FiniteTargetAwareVerifyLeafTree
      cache n extraFuel tree rho z = true) :
    bound4395FiniteTargetAwareVerifyLeafTree
      cache n (extraFuel + 1) tree rho z = true := by
  induction tree generalizing rho z with
  | leaf =>
      exact bound4395FiniteTargetAwareCover_succ_of_true
        cache n hverify
  | splitRho left right ihLeft ihRight =>
      have hchildren :
          bound4395FiniteTargetAwareVerifyLeafTree cache n extraFuel left
                (dyadicRouteBLeftHalf rho) z = true ∧
            bound4395FiniteTargetAwareVerifyLeafTree cache n extraFuel right
                (dyadicRouteBRightHalf rho) z = true := by
        simpa [bound4395FiniteTargetAwareVerifyLeafTree,
          Bool.and_eq_true] using hverify
      simpa [bound4395FiniteTargetAwareVerifyLeafTree,
        Bool.and_eq_true] using
          And.intro (ihLeft hchildren.1) (ihRight hchildren.2)
  | splitZ left right ihLeft ihRight =>
      have hchildren :
          bound4395FiniteTargetAwareVerifyLeafTree cache n extraFuel left rho
                (dyadicRouteBLeftHalf z) = true ∧
            bound4395FiniteTargetAwareVerifyLeafTree cache n extraFuel right rho
                (dyadicRouteBRightHalf z) = true := by
        simpa [bound4395FiniteTargetAwareVerifyLeafTree,
          Bool.and_eq_true] using hverify
      simpa [bound4395FiniteTargetAwareVerifyLeafTree,
        Bool.and_eq_true] using
          And.intro (ihLeft hchildren.1) (ihRight hchildren.2)

theorem bound4395OldFiniteTargetAwareLeafCodeCertificate_succ_of_true
    (n extraFuel : ℕ)
    (hcertificate :
      bound4395OldFiniteTargetAwareLeafCodeCertificate
        n extraFuel = true) :
    bound4395OldFiniteTargetAwareLeafCodeCertificate
      n (extraFuel + 1) = true := by
  unfold bound4395OldFiniteTargetAwareLeafCodeCertificate at hcertificate ⊢
  cases hcode : certifiedOldLeafCode n with
  | none => simp [hcode] at hcertificate
  | some code =>
      simp only [hcode] at hcertificate ⊢
      unfold bound4395FiniteTargetAwareLeafCodeCertificate at hcertificate ⊢
      cases htree : dyadicRouteBLeafTreeOfCode code with
      | none =>
          simp [htree] at hcertificate
      | some tree =>
          simp only [htree] at hcertificate ⊢
          unfold bound4395FiniteTargetAwareLeafTreeCertificate
            at hcertificate ⊢
          exact bound4395FiniteTargetAwareVerifyLeafTree_succ_of_true
            dyadicRouteBBuildResolutionCache n extraFuel hcertificate

end BerryEsseen
