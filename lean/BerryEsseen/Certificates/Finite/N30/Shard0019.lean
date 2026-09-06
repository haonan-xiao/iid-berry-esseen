import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN30Shard0019Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZZRZRLLRLLZLLRZRLLRLLZRLLRLLZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRZLLLRZLZLLL").getD .leaf

theorem finiteN30Shard0019_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 30 5
        finiteN30Shard0019Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 30)))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
