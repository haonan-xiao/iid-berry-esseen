import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN03Shard0020Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRLLRLLRLLRZRLLRLLRLLRZRLLRLLZRLLRLLRZRZRLLRZLLZLLRZLLZLLRZRZLRLLZLRLLRZRLLRLLZRLLRLLRZZLRLLZRLLRLLZRLLRLLRZRZLLZLLRZZLLZRLLRLLZRLLRLLZRZLLZLLRZZLLZLRLLZLRLLZRZRZLLRLLRZRLLRLLRLLRZRLLRLLZLRLLRZRZRLLRLLRLLRZRLLRZLLZLLRZLZLLZLRLLRZRLLRZLLZLLZRLLRZLLZLL").getD .leaf

theorem finiteN03Shard0020_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 3 6
        finiteN03Shard0020Tree (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 3)))))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
