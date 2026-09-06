import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN95Shard0018Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZLLLRZLZLLLZRLLRLL").getD .leaf

theorem finiteN95Shard0018_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 95 5
        finiteN95Shard0018Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 95)))))) (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
