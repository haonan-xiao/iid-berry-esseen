import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN28Shard0000Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRZZLLZLLLRZRZRLLRLLZRLLRLLRZRLLRZLLLZRLLRLLRZZRLLRLLZRLLRLLZLLRZRLLRLLZRLLRLL").getD .leaf

theorem finiteN28Shard0000_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 28 5
        finiteN28Shard0000Tree (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 28)) (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
