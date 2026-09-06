import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN72Shard0011Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLLRZRLLRLLLRLLRZRZRLLRLLLRZRLLRLLZLLRLLRZRLLRLLZRLLRLLRZRZRZRLLRLLZLRLLRZRLLRLLZRLLRLLRLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRLLRZRLLRLLZRLLRLLRZRLLRLLZRLLRLL").getD .leaf

theorem finiteN72Shard0011_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 72 5
        finiteN72Shard0011Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 72))))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
