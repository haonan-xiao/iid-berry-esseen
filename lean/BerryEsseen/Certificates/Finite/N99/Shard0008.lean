import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN99Shard0008Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZZRLLRLLZRLLRLLZRLLRLL").getD .leaf

theorem finiteN99Shard0008_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 99 5
        finiteN99Shard0008Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 99)))) (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
