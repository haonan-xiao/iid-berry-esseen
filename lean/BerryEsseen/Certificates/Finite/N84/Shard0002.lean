import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN84Shard0002Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLLRZRLLRLLLRLLRZRZRLLRLLLRZRLLRLLLRLLZRZRLLRLLLRZRLLRLLLRZRZRZRLLRLLLRZRLLRLLLRLLRZRZRLLRLLRLLRZRLLRLLRLLRLLZRZRLLRLLLRZRLLRLLLZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLL").getD .leaf

theorem finiteN84Shard0002_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 84 5
        finiteN84Shard0002Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 84))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
