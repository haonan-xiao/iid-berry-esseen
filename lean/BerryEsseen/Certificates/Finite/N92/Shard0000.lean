import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN92Shard0000Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZLLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZLLLZRZRLLRLLRLLRZRLLRLLRLLRZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZLZLLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZZLLZLRLLLZRZRLLRLLRLLRZRLLRLLRLLRZZRLLRLLZRLLRLLZRLLRLL").getD .leaf

theorem finiteN92Shard0000_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 92 5
        finiteN92Shard0000Tree (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 92)) (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
