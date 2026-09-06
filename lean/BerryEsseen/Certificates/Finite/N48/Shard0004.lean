import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN48Shard0004Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZLLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZZLLZLRLLLZRZRLLRLLRLLRZRLLRLLRLLRZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZZRLLRLLZRLLRLLLRZRZRZLLLRZRLLRLLLZRLLRLLRZRZRLLRLLLRZRLLRLLLZRLLRLLRZZRLLRLLZRLLRLLZLLZRZRLLRLLRLLRZRLLRLLRLL").getD .leaf

theorem finiteN48Shard0004_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 48 5
        finiteN48Shard0004Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 48)))) (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
