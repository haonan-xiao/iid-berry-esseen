import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN23Shard0000Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZLLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZZLLZLRLLZLLZRZRLLRLLRLLRZRLLRLLRLL").getD .leaf

theorem finiteN23Shard0000_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 23 5
        finiteN23Shard0000Tree (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 23)) (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
