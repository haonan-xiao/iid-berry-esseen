import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN04Shard0022Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRZRLLRLLZLRLLRZRLLRLLZRLLRLLRZZLLZLRLLZLLRZRZRZLRLLLRZRLLRLLRLLZRLLRZLLLRZRZRLLRLLRLLRZRLLRZLRLLZLLRZLLLZRZLRLLRLLRZRLLRLLRLLRZZRLLRLLZRLLRZLLLZRLLRLL").getD .leaf

theorem finiteN04Shard0022_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 4 6
        finiteN04Shard0022Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 4))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
