import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN47Shard0002Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRZRLLRLLLRZRLLRLLLRLLRZRZRLLRLLLRZRLLRLLZLLRLL").getD .leaf

theorem finiteN47Shard0002_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 47 5
        finiteN47Shard0002Tree (dyadicRouteBRightHalf (dyadicRouteBFiniteRootRho 47)) (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
