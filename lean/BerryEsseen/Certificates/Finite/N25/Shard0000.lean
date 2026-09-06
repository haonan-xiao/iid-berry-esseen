import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN25Shard0000Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRLLRZLLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRZLLLRZRLLRLLLRZZRLLRLLZRLLRLLZRLLRLL").getD .leaf

theorem finiteN25Shard0000_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 25 5
        finiteN25Shard0000Tree (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 25)) (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
