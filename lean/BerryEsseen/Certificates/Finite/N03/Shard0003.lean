import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN03Shard0003Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZLRLLZLLRZRLLRLLZLRLLZRLLRZLLZLLRZRZRLLRLLZRLLRLLRZRLLRZLLLZRLLRLLZRZRLLRLLZLRLLRZRLLRLLZRLLRLLZRZRLLRLLZRLLRLLRZRZLRLLZLLRZRLLRLLZRLLRLLZRZLLLRZLRLLZLRLL").getD .leaf

theorem finiteN03Shard0003_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 3 6
        finiteN03Shard0003Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 3)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
