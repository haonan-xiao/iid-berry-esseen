import BerryEsseen.Interval.Finite.FastEvaluator

/-!
# Interval / Finite / Fast Cover
-/

namespace BerryEsseen

def fastFiniteCover
    (cache : DyadicRouteBResolutionCache) (n : ℕ) :
    ℕ → DyadicInterval → DyadicInterval → Bool
  | 0, rho, z => fastFiniteTargetAwareAccepted cache n rho z
  | fuel + 1, rho, z =>
      if fastFiniteTargetAwareAccepted cache n rho z then true
      else if dyadicRouteBSplitRho n rho z then
        fastFiniteCover cache n fuel (dyadicRouteBLeftHalf rho) z &&
          fastFiniteCover cache n fuel (dyadicRouteBRightHalf rho) z
      else
        fastFiniteCover cache n fuel rho (dyadicRouteBLeftHalf z) &&
          fastFiniteCover cache n fuel rho (dyadicRouteBRightHalf z)

theorem fastFiniteCover_eq
    (cache : DyadicRouteBResolutionCache) (n fuel : ℕ)
    (rho z : DyadicInterval) :
    fastFiniteCover cache n fuel rho z =
      bound4395FiniteTargetAwareCover cache n fuel rho z := by
  induction fuel generalizing rho z with
  | zero => exact fastFiniteTargetAwareAccepted_eq cache n rho z
  | succ fuel ih =>
      simp only [fastFiniteCover, bound4395FiniteTargetAwareCover,
        fastFiniteTargetAwareAccepted_eq, ih]

def fastFiniteVerifyLeafTree
    (cache : DyadicRouteBResolutionCache) (n extraFuel : ℕ) :
    DyadicRouteBLeafTree → DyadicInterval → DyadicInterval → Bool
  | .leaf, rho, z => fastFiniteCover cache n extraFuel rho z
  | .splitRho left right, rho, z =>
      fastFiniteVerifyLeafTree cache n extraFuel left
          (dyadicRouteBLeftHalf rho) z &&
        fastFiniteVerifyLeafTree cache n extraFuel right
          (dyadicRouteBRightHalf rho) z
  | .splitZ left right, rho, z =>
      fastFiniteVerifyLeafTree cache n extraFuel left rho
          (dyadicRouteBLeftHalf z) &&
        fastFiniteVerifyLeafTree cache n extraFuel right rho
          (dyadicRouteBRightHalf z)

theorem fastFiniteVerifyLeafTree_eq
    (cache : DyadicRouteBResolutionCache) (n extraFuel : ℕ)
    (tree : DyadicRouteBLeafTree) (rho z : DyadicInterval) :
    fastFiniteVerifyLeafTree cache n extraFuel tree rho z =
      bound4395FiniteTargetAwareVerifyLeafTree cache n extraFuel tree rho z := by
  induction tree generalizing rho z with
  | leaf => exact fastFiniteCover_eq cache n extraFuel rho z
  | splitRho left right ihLeft ihRight =>
      simp only [fastFiniteVerifyLeafTree,
        bound4395FiniteTargetAwareVerifyLeafTree, ihLeft, ihRight]
  | splitZ left right ihLeft ihRight =>
      simp only [fastFiniteVerifyLeafTree,
        bound4395FiniteTargetAwareVerifyLeafTree, ihLeft, ihRight]

#print axioms fastFiniteCover_eq
#print axioms fastFiniteVerifyLeafTree_eq

end BerryEsseen
