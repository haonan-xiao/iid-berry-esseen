import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN99Shard0012Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLLRZRLLRLLZLLRLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRLLRZRLLRLLZLRLLRZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRLLRZRLLRLLZRLLRLLZRZRLLRLLRLLRZRLLRLLRLL").getD .leaf

theorem finiteN99Shard0012_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 99 5
        finiteN99Shard0012Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 99))))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
