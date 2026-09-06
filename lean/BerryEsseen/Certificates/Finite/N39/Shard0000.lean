import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN39Shard0000Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZLLLRZLLLZRLLRLLRZRZLRLLLRZRLLRLLLZRLLRLLZRZRLLRLLLRZRLLRLLLRZRZRZRLLRLLLRZRLLRLLLZRLLRLLRZRZRLLRLLLRZRLLRLLLZRLLRLLZRZRLLRLLLRZRLLRLLZLLZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLL").getD .leaf

theorem finiteN39Shard0000_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 39 5
        finiteN39Shard0000Tree (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 39)) (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
