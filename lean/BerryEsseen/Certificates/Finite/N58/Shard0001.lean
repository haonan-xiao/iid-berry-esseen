import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN58Shard0001Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZLLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZLZLLLZRZRLLRLLRLLRZRLLRLLRLLRZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZZLLZRLLRLLLRZRZRZLLLRZLRLLLZRLLRLLRZRZRLLRLLLRZRLLRLLLZRLLRLLRZZRLLRLLZRLLRLLLZRZRLLRLLRLLRZRLLRLLRLL").getD .leaf

theorem finiteN58Shard0001_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 58 5
        finiteN58Shard0001Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 58))) (dyadicRouteBRightHalf (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
