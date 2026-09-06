import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN68Shard0022Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLLRZRLLRLLRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLRLLZRZRLLRLLRLLRZRLLRLLRLLRZRZRZRLLRLLRLLRZRLLRLLRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLRZLLLZRZRLLRLLRLLRZRLLRLLRLLZRZRZRLLRLLLRZRLLRLLLZRLLRLLRZRZRLLRLLLRZRLLRLLLZRLLRLL").getD .leaf

theorem finiteN68Shard0022_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 68 5
        finiteN68Shard0022Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 68)))))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
