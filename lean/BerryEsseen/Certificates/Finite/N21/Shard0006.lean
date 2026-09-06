import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN21Shard0006Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZLRLLLRZRLLRLLLZRLLRLLRZRZRLLRLLLRZRLLRLLRLLZRLLRLLRZZRLLRLLZRLLRLLZRLLRLLRZRZRZRLLRLLRLLRZRLLRLLRLLZRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLZRZLLLRZLRLLLRZZRLLRLLZRLLRLLZRLLRLLRZRZLLLRZZLRLLZRLLRLLZLLZRLLRLL").getD .leaf

theorem finiteN21Shard0006_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 21 5
        finiteN21Shard0006Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 21)))) (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
