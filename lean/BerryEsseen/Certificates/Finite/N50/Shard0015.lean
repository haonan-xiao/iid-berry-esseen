import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN50Shard0015Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRLLRLLRLLRZRLLRLLRLLZRZRLLRLLRLLRZRLLRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLZRZRLLRLLRLLRZRLLRLLRLLRZZRZLLLRZLLLZRZRLLRLLLRZRLLRLLLZRLLRLL").getD .leaf

theorem finiteN50Shard0015_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 50 5
        finiteN50Shard0015Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 50)))))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
