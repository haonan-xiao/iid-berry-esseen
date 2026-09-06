import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN04Shard0003Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "ZRZRZRLLRLLZRLLRLLRZRZLLLRZLRLLRLLZRLLRLLRZZRLLRLLZRLLRLLZRLLRLLRZRZRZRLLRLLRLLRZRLLRLLRLLZRZLLLRZLRLLRLLRZRZRLLRLLRLLRZRLLRLLRLLZRZRLLRLLRLLRZRLLRLLRLLRZZRLLRLLZRZLLRLLRZRLLRLLRLLZRZLLZLLRZLRLLZLRLL").getD .leaf

theorem finiteN04Shard0003_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 4 6
        finiteN04Shard0003Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 4))))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ)))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
