import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN70Shard0001Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRLLRZLLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRZLLLRZRLLRLLLRZZRLLRLLZRLLRLLZRLLRLL").getD .leaf

theorem finiteN70Shard0001_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 70 5
        finiteN70Shard0001Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 70))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
