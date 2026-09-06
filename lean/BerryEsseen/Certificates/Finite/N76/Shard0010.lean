import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN76Shard0010Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLRLLRZRLLRLLRLLRZLLLRZRZRLLRLLRLLRZRLLRLLRLLRZLRLLLRZRLLRLLZRLLRLLRZRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLLRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLLRZRLLRLLZRLLRLLZRZRLLRLLRLLRZRLLRLLRLL").getD .leaf

theorem finiteN76Shard0010_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 76 5
        finiteN76Shard0010Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 76)))) (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
