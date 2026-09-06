import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN58Shard0027Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZZRLLRLLZRLLRLLZRLLRLLRZZRLLRLLZRLLRLLZRLLRLLZRLLRLL").getD .leaf

theorem finiteN58Shard0027_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 58 5
        finiteN58Shard0027Tree (dyadicRouteBRightHalf (dyadicRouteBFiniteRootRho 58)) (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
