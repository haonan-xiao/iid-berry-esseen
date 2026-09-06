import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN91Shard0012Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLLRZRLLRLLLRLLRZRZRLLRLLLRZRLLRLLLRLLZRZRLLRLLLRZRLLRLLLRZRZRZRLLRLLZLLRZRLLRLLZRLLRLLRLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLRLLZRZRLLRLLRLLRZRLLRLLRLLRZZRLLRLLZRLLRLLZRLLRLL").getD .leaf

theorem finiteN91Shard0012_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 91 5
        finiteN91Shard0012Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 91))))) (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
