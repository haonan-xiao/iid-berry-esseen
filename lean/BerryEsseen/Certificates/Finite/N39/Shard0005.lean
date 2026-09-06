import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN39Shard0005Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRZLLLRZRLLRLLLZRLLRLLRZRZRLLRLLLRZRLLRLLZLLZRLLRLL").getD .leaf

theorem finiteN39Shard0005_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 39 5
        finiteN39Shard0005Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 39))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
