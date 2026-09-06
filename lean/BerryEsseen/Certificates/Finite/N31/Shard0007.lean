import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN31Shard0007Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLRLLRZRLLRLLRLLZRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLZRLLRLLZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZRZRZRLLRLLRLLRZRLLRLLRLLZRZLLLRZRLLRLLLRZRZRLLRLLRLLRZRLLRLLRLLZRZRLLRLLLRZRLLRLLLZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZZRLLRZLLLZRZLRLLLRZRLLRLLLZRLLRLL").getD .leaf

theorem finiteN31Shard0007_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 31 5
        finiteN31Shard0007Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 31)))) (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
