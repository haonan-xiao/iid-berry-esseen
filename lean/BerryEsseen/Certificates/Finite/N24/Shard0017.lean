import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN24Shard0017Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRZRLLRLLRLLRZRLLRLLRLLZRZLLLRZLRLLLRZRZRLLRLLRLLRZRLLRLLRLLZRZRLLRLLRLLRZRLLRLLRLL").getD .leaf

theorem finiteN24Shard0017_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 24 5
        finiteN24Shard0017Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 24))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
