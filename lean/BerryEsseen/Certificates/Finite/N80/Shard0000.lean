import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN80Shard0000Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLRLLRZRLLRLLRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLRLLRZRLLRLLZRLLRLLRZRZRZRLLRLLRLLRZRLLRLLRLLRZLLLRZRZRLLRLLRLLRZRLLRLLRLLRZLRLLLRZRLLRLLZRLLRLLZRZRLLRLLRLLRZRLLRLLRLL").getD .leaf

theorem finiteN80Shard0000_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 80 5
        finiteN80Shard0000Tree (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 80)) (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
