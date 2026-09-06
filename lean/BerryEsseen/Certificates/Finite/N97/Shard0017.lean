import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN97Shard0017Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRLLRZLLLRLLRZRZLRLLLRZRLLRLLLRLL").getD .leaf

theorem finiteN97Shard0017_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 97 5
        finiteN97Shard0017Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 97)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
