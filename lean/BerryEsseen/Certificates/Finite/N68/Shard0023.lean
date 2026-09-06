import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN68Shard0023Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLRLLRZRLLRLLRLLRZLLLRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLLZRZRLLRLLRLLRZRLLRLLRLLRZRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLLRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLZLLZRZRLLRLLRLLRZRLLRLLRLLZRZRZRLLRLLLRZRLLRLLLZRLLRLLRZRZRLLRLLLRZRLLRLLRLLZRLLRLL").getD .leaf

theorem finiteN68Shard0023_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 68 5
        finiteN68Shard0023Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 68)))))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
