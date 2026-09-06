import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN66Shard0021Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZZRZRLLRLLLRZRLLRLLLZRZRLLRLLLRZRLLRLLRLLZRLLRLL").getD .leaf

theorem finiteN66Shard0021_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 66 5
        finiteN66Shard0021Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 66)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
