import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN87Shard0007Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRLLZRZRLLRLLLRZRLLRLLLRZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZLLLZRZRLLRLLRLLRZRLLRLLRLLZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLL").getD .leaf

theorem finiteN87Shard0007_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 87 5
        finiteN87Shard0007Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 87)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
