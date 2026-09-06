import BerryEsseen.Interval.Finite.AdaptiveFullCover

/-!
# Interval / Finite / Subtree
-/

namespace BerryEsseen

set_option maxRecDepth 10000

theorem bound4395FiniteVerifySplitRho_true
    {cache : DyadicRouteBResolutionCache} {n fuel : Nat}
    {left right : DyadicRouteBLeafTree} {rho z : DyadicInterval}
    (hleft : bound4395FiniteTargetAwareVerifyLeafTree cache n fuel left
      (dyadicRouteBLeftHalf rho) z = true)
    (hright : bound4395FiniteTargetAwareVerifyLeafTree cache n fuel right
      (dyadicRouteBRightHalf rho) z = true) :
    bound4395FiniteTargetAwareVerifyLeafTree cache n fuel
      (.splitRho left right) rho z = true := by
  simpa [bound4395FiniteTargetAwareVerifyLeafTree, Bool.and_eq_true]
    using And.intro hleft hright

theorem bound4395FiniteVerifySplitZ_true
    {cache : DyadicRouteBResolutionCache} {n fuel : Nat}
    {left right : DyadicRouteBLeafTree} {rho z : DyadicInterval}
    (hleft : bound4395FiniteTargetAwareVerifyLeafTree cache n fuel left
      rho (dyadicRouteBLeftHalf z) = true)
    (hright : bound4395FiniteTargetAwareVerifyLeafTree cache n fuel right
      rho (dyadicRouteBRightHalf z) = true) :
    bound4395FiniteTargetAwareVerifyLeafTree cache n fuel
      (.splitZ left right) rho z = true := by
  simpa [bound4395FiniteTargetAwareVerifyLeafTree, Bool.and_eq_true]
    using And.intro hleft hright

theorem bound4395OldFiniteCertificate_of_parsed_tree
    {n fuel : Nat} {tree : DyadicRouteBLeafTree}
    (hparse : (certifiedOldLeafCode n).bind dyadicRouteBLeafTreeOfCode =
      some tree)
    (hverify : bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache n fuel tree
        (dyadicRouteBFiniteRootRho n) dyadicRouteBFiniteRootZ = true) :
    bound4395OldFiniteTargetAwareLeafCodeCertificate n fuel = true := by
  cases hcode : certifiedOldLeafCode n with
  | none => simp [hcode] at hparse
  | some code =>
      simp only [hcode, Option.bind_some] at hparse
      simpa [bound4395OldFiniteTargetAwareLeafCodeCertificate, hcode,
        bound4395FiniteTargetAwareLeafCodeCertificate, hparse,
        bound4395FiniteTargetAwareLeafTreeCertificate] using hverify

#print axioms bound4395FiniteVerifySplitRho_true
#print axioms bound4395FiniteVerifySplitZ_true
#print axioms bound4395OldFiniteCertificate_of_parsed_tree

end BerryEsseen
