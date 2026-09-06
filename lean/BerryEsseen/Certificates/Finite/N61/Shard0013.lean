import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN61Shard0013Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZLLLRZLRLLLZRLLRLLRZRZRLLRLLLRZRLLRLLLZRLLRLLZRZRLLRLLLRZRLLRLLLRZRZRZRLLRLLLRZRLLRLLLZRLLRLLRZRZRLLRLLLRZRLLRLLLZRLLRLLZRZRLLRLLZLRLLRZRLLRLLZRLLRLLZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLL").getD .leaf

theorem finiteN61Shard0013_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 61 5
        finiteN61Shard0013Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 61))))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
