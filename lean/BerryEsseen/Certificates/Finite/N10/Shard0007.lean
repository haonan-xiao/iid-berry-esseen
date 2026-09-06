import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN10Shard0007Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRZRZLLLRZLLLZRLLRLLRZRZLRLLLRZRLLRLLZLLZRLLRLLRZZRLLRLLZRLLRLLZRLLRLLRZRZRZRLLRLLZLRLLRZRLLRLLZRLLRLLZRLLRZLLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRZLRLLZLLRZRLLRLLZLLRZZRLLRLLZRLLRLLZRLLRLL").getD .leaf

theorem finiteN10Shard0007_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 10 6
        finiteN10Shard0007Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 10)))))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
