import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN45Shard0007Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLRLLRZRLLRLLRLLRZLRLLLRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLLZRZRLLRLLRLLRZRLLRLLRLLRZRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLZLLRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLZLRLLZRZRLLRLLRLLRZRLLRLLRLLZRZRLLRZLLLZRLLRLLRZRZLRLLLRZRLLRLLLZRLLRLL").getD .leaf

theorem finiteN45Shard0007_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 45 5
        finiteN45Shard0007Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 45)))) (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
