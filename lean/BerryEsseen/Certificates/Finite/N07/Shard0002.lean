import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN07Shard0002Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRZRZLLLRZLRLLLRLLRZRZRLLRLLZLLRZRLLRLLZRLLRLLRZLZLLZLLZRZRLLRLLRLLRZRLLRLLRLLRZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZZLRLLZRLLRLLZLRLLRZRZRLLRLLZRLLRLLRZRZLLLRZLRLLLZRLLRLLRZZRLLRLLZRLLRLLZRLLRLLZRZRLLRLLRLLRZRZLLLRZRLLRLLZLLRZLLZLL").getD .leaf

theorem finiteN07Shard0002_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 7 6
        finiteN07Shard0002Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 7)))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
