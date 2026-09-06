import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN62Shard0014Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLLRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLLZRZRLLRLLRLLRZRLLRLLRLLRZRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLLRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLZLLZRZRLLRLLRLLRZRLLRLLRLLRZZRZLLLRZLRLLLZRZRLLRLLLRZRLLRLLLZRLLRLL").getD .leaf

theorem finiteN62Shard0014_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 62 5
        finiteN62Shard0014Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 62))))) (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
