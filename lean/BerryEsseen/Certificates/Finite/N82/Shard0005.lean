import BerryEsseen.Interval.Finite.Subtree
import BerryEsseen.Interval.Finite.FastCover

namespace BerryEsseen
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def finiteN82Shard0005Tree : DyadicRouteBLeafTree :=
  (dyadicRouteBLeafTreeOfCode "RZRZRZRZRLLRLLZLRLLRZRLLRLLZRLLRLLZRLLRLLRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRLLRLLRZZRLLRLLZRLLRLLZLRLLRZRZRZRLLRLLZRLLRLLRZRLLRLLZRLLRLLZRLLRLLRZRZRLLRLLZRLLRLLRZRLLRZLLLZRLLRLLZRLLRLLRZZRLLRLLZRLLRLLZRLLRLLRZRLLRLLZRLLRLL").getD .leaf

theorem finiteN82Shard0005_checked :
    bound4395FiniteTargetAwareVerifyLeafTree
      dyadicRouteBBuildResolutionCache 82 5
        finiteN82Shard0005Tree (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBFiniteRootRho 82))) (dyadicRouteBLeftHalf (dyadicRouteBLeftHalf (dyadicRouteBRightHalf dyadicRouteBFiniteRootZ))) = true := by
  rw [← fastFiniteVerifyLeafTree_eq]
  native_decide

end BerryEsseen
