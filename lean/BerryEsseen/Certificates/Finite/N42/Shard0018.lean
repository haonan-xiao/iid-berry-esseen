import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN42Shard0018Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZZRLLRLLZRLLRLLZRLLRLLRZZRLLRLLZRLLRLLZRLLRLLZRZLLLRZLZLLL").getD .leaf

theorem finiteN42Shard0018_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 42 5
        finiteN42Shard0018Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 42)))))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
