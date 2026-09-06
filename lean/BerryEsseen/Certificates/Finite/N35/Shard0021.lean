import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN35Shard0021Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZZRLLRLLZRLLRLLZRLLRLLRZZRLLRLLZRLLRLLZRLLRLLZRLLRLL").getD .leaf

theorem finiteN35Shard0021_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 35 5
        finiteN35Shard0021Tree (dyadicRouteBRightHalf (dyadicRouteBFiniteRootRho 35)) (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
