import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN73Shard0028Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZZRZRLLRLLLRZRLLRLLLZRZRLLRLLLRZRLLRLLLZRLLRLL").getD .leaf

theorem finiteN73Shard0028_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 73 5
        finiteN73Shard0028Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 73)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
