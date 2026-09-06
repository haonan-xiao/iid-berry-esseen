import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN56Shard0001Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRLLRLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRLLRLLRZZRLLRLLZRLLRLLZRLLRLLRZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRZLLLRZLRLLLRZRZRLLRZLRLLLZRLLRLLRZRZRLLRLLLRZRLLRLLLZRLLRLLZRZRLLRLLLRZRLLRLLLRZZRLLRLLZRLLRLLZRLLRLL").getD .leaf

theorem finiteN56Shard0001_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 56 5
        finiteN56Shard0001Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 56))) (dyadicRouteBRightHalf (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
