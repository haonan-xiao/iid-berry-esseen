import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN85Shard0007Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLRLLRZRLLRLLRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLRLLZRZRLLRLLLRZRLLRLLLRZRZRZRLLRLLRLLRZRLLRLLRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLRZLLLZRZRLLRLLRLLRZRLLRLLRLLRZZRLLRLLZRLLRLLZRLLRLL").getD .leaf

theorem finiteN85Shard0007_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 85 5
        finiteN85Shard0007Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 85)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
