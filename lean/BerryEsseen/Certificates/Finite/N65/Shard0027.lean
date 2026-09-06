import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN65Shard0027Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRZRLLRLLRLLRZRLLRLLRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLRZLRLLL").getD .leaf

theorem finiteN65Shard0027_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 65 5
        finiteN65Shard0027Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 65))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
