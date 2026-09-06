import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN29Shard0001Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLLRZRLLRLLLZRLLRLLRZRZRLLRLLLRZRLLRLLLZRLLRLLRZZRLLRLLZRLLRLLZLRLLRZRZRZRLLRLLZLLRZRLLRLLZLRLLZRLLRLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRLLRLLRZZRLLRLLZRLLRLLZRLLRLLZRZRLLRLLRLLRZRLLRLLRLL").getD .leaf

theorem finiteN29Shard0001_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 29 5
        finiteN29Shard0001Tree (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 29)) (dyadicRouteBRightHalf (dyadicRouteBLeftHalf dyadicRouteBFiniteRootZ)) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
