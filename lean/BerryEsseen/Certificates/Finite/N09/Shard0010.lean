import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN09Shard0010Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZZRLLRLLZRLLRLLZRLLRLLRZZRLLRZLLLZRZLLLRZRLLRLLRLLZRZLLLRZLLZLLZRZZRLLRLLZRLLRLLZRLLRLLRZZRLLRLLZRLLRLLZRLLRLL").getD .leaf

theorem finiteN09Shard0010_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 9 6
        finiteN09Shard0010Tree (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 9)))))) (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
