import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN93Shard0004Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRZRLLRLLLRZRLLRLLLZRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLZRLLRLL").getD .leaf

theorem finiteN93Shard0004_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 93 5
        finiteN93Shard0004Tree (dyadicRouteBRightHalf (dyadicRouteBFiniteRootRho 93)) (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
