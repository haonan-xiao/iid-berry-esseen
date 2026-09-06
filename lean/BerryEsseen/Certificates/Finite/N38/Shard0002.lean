import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN38Shard0002Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZZRLLRLLZRLLRLLZLLRZZRLLRLLZRLLRLLZLRLLZRLLRLL").getD .leaf

theorem finiteN38Shard0002_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 38 5
        finiteN38Shard0002Tree (dyadicRouteBRightHalf (dyadicRouteBFiniteRootRho 38)) (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
