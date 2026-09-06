import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN74Shard0016Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRLLRLLLRZRLLRLLZLLZRLLRLL").getD .leaf

theorem finiteN74Shard0016_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 74 5
        finiteN74Shard0016Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 74))))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
