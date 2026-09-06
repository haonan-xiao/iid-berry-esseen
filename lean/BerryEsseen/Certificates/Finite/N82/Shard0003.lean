import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN82Shard0003Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRLLRLLRLLRZRLLRZLLLRLL").getD .leaf

theorem finiteN82Shard0003_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 82 5
        finiteN82Shard0003Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 82))) (dyadicRouteBRightHalf (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
